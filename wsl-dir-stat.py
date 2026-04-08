#!/usr/bin/env python3
"""
wsl-dir-stat: A WinDirStat-like disk usage analyzer for WSL/Linux.

Features:
  - Recursive directory tree with sizes, percentages, and visual bars
  - File extension breakdown (which types consume the most space)
  - Top N largest files
  - Color-coded output
  - Configurable scan depth and sorting
  - Parallel scanning with work-queue based thread pool
  - SQLite cache with mtime-based invalidation for instant re-scans
"""

import argparse
import fnmatch
import heapq
import json
import os
import queue
import shutil
import sqlite3
import subprocess
import sys
import threading
import time
from collections import defaultdict
from pathlib import Path

# ── ANSI Colors ──────────────────────────────────────────────────────────────

class Color:
    RESET   = "\033[0m"
    BOLD    = "\033[1m"
    DIM     = "\033[2m"
    RED     = "\033[31m"
    GREEN   = "\033[32m"
    YELLOW  = "\033[33m"
    BLUE    = "\033[34m"
    MAGENTA = "\033[35m"
    CYAN    = "\033[36m"
    WHITE   = "\033[37m"

    # Bar gradient (green → yellow → red)
    BAR_COLORS = [
        "\033[38;5;22m",   # dark green
        "\033[38;5;28m",
        "\033[38;5;34m",
        "\033[38;5;70m",
        "\033[38;5;106m",
        "\033[38;5;142m",  # yellow-ish
        "\033[38;5;178m",
        "\033[38;5;214m",
        "\033[38;5;208m",
        "\033[38;5;202m",
        "\033[38;5;196m",  # red
    ]

NO_COLOR = os.environ.get("NO_COLOR") is not None

def c(color: str, text: str) -> str:
    if NO_COLOR:
        return str(text)
    return f"{color}{text}{Color.RESET}"

# ── Size Formatting ──────────────────────────────────────────────────────────

SIZE_UNITS = [
    (1 << 40, "TiB"),
    (1 << 30, "GiB"),
    (1 << 20, "MiB"),
    (1 << 10, "KiB"),
    (1,        "B"),
]

def fmt_size(size_bytes: int) -> str:
    if size_bytes < 0:
        return "???"
    for threshold, unit in SIZE_UNITS:
        if size_bytes >= threshold:
            value = size_bytes / threshold
            if value >= 100:
                return f"{value:>7.1f} {unit}"
            elif value >= 10:
                return f"{value:>7.1f} {unit}"
            else:
                return f"{value:>7.2f} {unit}"
    return f"{size_bytes:>7} B  "

def color_size(size_bytes: int) -> str:
    s = fmt_size(size_bytes)
    if size_bytes >= (1 << 30):
        return c(Color.RED + Color.BOLD, s)
    elif size_bytes >= (100 << 20):
        return c(Color.RED, s)
    elif size_bytes >= (10 << 20):
        return c(Color.YELLOW, s)
    elif size_bytes >= (1 << 20):
        return c(Color.GREEN, s)
    else:
        return c(Color.DIM, s)

# ── Visual Bar ───────────────────────────────────────────────────────────────

BAR_CHARS = "█▓▒░"

def make_bar(fraction: float, width: int = 30) -> str:
    filled = int(fraction * width)
    bar = ""
    for i in range(filled):
        color_idx = int((i / width) * (len(Color.BAR_COLORS) - 1))
        bar += c(Color.BAR_COLORS[color_idx], "█")
    bar += c(Color.DIM, "░") * (width - filled)
    return bar

def pct_str(fraction: float) -> str:
    pct = fraction * 100
    if pct >= 10:
        return f"{pct:5.1f}%"
    elif pct >= 1:
        return f"{pct:5.1f}%"
    elif pct >= 0.1:
        return f"{pct:5.2f}%"[:-1] + "%"  # e.g. 0.12%
    else:
        return f" <0.1%"

# ── Fast Extension Extraction ────────────────────────────────────────────────

def _get_ext(filename: str) -> str:
    """Fast file extension extraction — 4.7× faster than Path().suffix."""
    _, ext = os.path.splitext(filename)
    return ext.lower() if ext else "(no ext)"

# ── Directory Scanner ────────────────────────────────────────────────────────

class DirNode:
    __slots__ = ("name", "path", "size", "file_count", "dir_count",
                 "children", "is_file", "error")

    def __init__(self, name: str, path: str, is_file: bool = False):
        self.name = name
        self.path = path
        self.size = 0
        self.file_count = 0
        self.dir_count = 0
        self.children: list["DirNode"] = []
        self.is_file = is_file
        self.error: str | None = None


class TopFilesHeap:
    """Bounded min-heap tracking the N largest files seen during scan.

    Avoids the post-scan full-tree traversal to find top files.
    Thread-safe when each thread has its own instance.
    """
    __slots__ = ("_heap", "_max_size")

    def __init__(self, max_size: int = 15):
        self._heap: list[tuple[int, str]] = []
        self._max_size = max_size

    def push(self, size: int, path: str):
        if len(self._heap) < self._max_size:
            heapq.heappush(self._heap, (size, path))
        elif size > self._heap[0][0]:
            heapq.heapreplace(self._heap, (size, path))

    def merge(self, other: "TopFilesHeap"):
        for item in other._heap:
            self.push(item[0], item[1])

    def get_sorted(self) -> list[tuple[int, str]]:
        return sorted(self._heap, key=lambda x: x[0], reverse=True)


# ── Cache Layer ──────────────────────────────────────────────────────────────

CACHE_DIR = os.path.join(os.environ.get("XDG_CACHE_HOME",
                         os.path.expanduser("~/.cache")), "wsl-dir-stat")
CACHE_DB = os.path.join(CACHE_DIR, "cache.db")

_CACHE_SCHEMA = """
CREATE TABLE IF NOT EXISTS dir_cache (
    path       TEXT PRIMARY KEY,
    mtime      REAL NOT NULL,
    scanned_at REAL NOT NULL,
    size       INTEGER NOT NULL,
    file_count INTEGER NOT NULL,
    dir_count  INTEGER NOT NULL,
    files_json TEXT NOT NULL,
    ext_json   TEXT NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_dir_cache_mtime ON dir_cache(path, mtime);
"""


class ScanCache:
    """SQLite-backed directory scan cache with mtime invalidation.

    Each directory's scan result is cached keyed by (path, mtime). On re-scan,
    if a directory's mtime matches the cache, we skip stat() calls on all its
    files and reuse cached sizes. Subdirectories are still recursively validated.

    Thread safety: reads use per-thread connections (WAL supports concurrent
    readers). Writes are buffered in-memory and flushed in a single batch to
    avoid SQLite write contention.
    """

    def __init__(self, enabled: bool = True):
        self.enabled = enabled
        self._local = threading.local()
        self._connections: list[sqlite3.Connection] = []
        self._conn_lock = threading.Lock()
        self._write_buf: list[tuple] = []
        self._write_lock = threading.Lock()
        self.hits = 0
        self.misses = 0
        self._stats_lock = threading.Lock()

    def _get_conn(self) -> sqlite3.Connection | None:
        if not self.enabled:
            return None
        conn = getattr(self._local, "conn", None)
        if conn is None:
            os.makedirs(CACHE_DIR, exist_ok=True)
            conn = sqlite3.connect(CACHE_DB)
            conn.execute("PRAGMA journal_mode=WAL")
            conn.execute("PRAGMA synchronous=NORMAL")
            conn.execute("PRAGMA busy_timeout=2000")
            conn.executescript(_CACHE_SCHEMA)
            self._local.conn = conn
            with self._conn_lock:
                self._connections.append(conn)
        return conn

    def open(self):
        self._get_conn()

    def close(self):
        self.flush()
        with self._conn_lock:
            for conn in self._connections:
                try:
                    conn.close()
                except Exception:
                    pass
            self._connections.clear()

    def lookup(self, path: str, mtime: float
               ) -> tuple[list[tuple[str, int]], dict[str, dict]] | None:
        """Check cache for a directory. Returns (files, ext_stats) or None."""
        conn = self._get_conn()
        if not conn:
            return None
        row = conn.execute(
            "SELECT mtime, files_json, ext_json FROM dir_cache WHERE path = ?",
            (path,)
        ).fetchone()
        if row and row[0] == mtime:
            with self._stats_lock:
                self.hits += 1
            files = json.loads(row[1])
            ext = json.loads(row[2])
            return files, ext
        with self._stats_lock:
            self.misses += 1
        return None

    def store(self, path: str, mtime: float, size: int, file_count: int,
              dir_count: int, files: list[tuple[str, int]],
              ext_stats: dict):
        """Buffer a cache write (flushed later to avoid write contention)."""
        if not self.enabled:
            return
        row = (path, mtime, time.time(), size, file_count, dir_count,
               json.dumps(files), json.dumps(ext_stats))
        with self._write_lock:
            self._write_buf.append(row)

    def flush(self):
        """Write all buffered cache entries to the DB in one transaction."""
        with self._write_lock:
            buf = self._write_buf
            self._write_buf = []
        if not buf:
            return
        # Use a dedicated connection for the batch write
        conn = self._get_conn()
        if not conn:
            return
        try:
            conn.executemany(
                "INSERT OR REPLACE INTO dir_cache "
                "(path, mtime, scanned_at, size, file_count, dir_count, "
                " files_json, ext_json) VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
                buf
            )
            conn.commit()
        except sqlite3.Error:
            pass  # cache is best-effort

    @staticmethod
    def clear():
        """Delete the cache database."""
        if os.path.exists(CACHE_DB):
            os.remove(CACHE_DB)
            print(f"  Cache cleared: {CACHE_DB}")
        else:
            print("  No cache to clear.")


# ── Progress Tracker (thread-local counters) ─────────────────────────────────

class ProgressTracker:
    """Thread-safe progress tracking with thread-local counters.

    Each thread bumps its own counter without acquiring any lock. The
    display thread periodically sums all thread-local counters.
    """

    def __init__(self):
        self._local = threading.local()
        self._counters: list[list[int]] = []  # shared refs to per-thread [count]
        self._lock = threading.Lock()
        self.start_time = time.monotonic()
        self._last_print = 0

    def _get_counter(self) -> list[int]:
        """Get or create a thread-local counter (a mutable list of [int])."""
        counter = getattr(self._local, "counter", None)
        if counter is None:
            counter = [0]
            self._local.counter = counter
            with self._lock:
                self._counters.append(counter)
        return counter

    def update(self):
        counter = self._get_counter()
        counter[0] += 1
        # Only check for print periodically (every 100 dirs per thread)
        if counter[0] % 100 == 0:
            self._maybe_print()

    def _maybe_print(self):
        now = time.monotonic()
        if now - self._last_print < 0.3:
            return
        self._last_print = now
        total = sum(c[0] for c in self._counters)
        elapsed = now - self.start_time
        rate = int(total / elapsed) if elapsed > 0 else 0
        print(f"\r  Scanning... {total:,} dirs "
              f"({elapsed:.1f}s, {rate:,}/s)    ",
              end="", flush=True)

    @property
    def dirs_scanned(self) -> int:
        return sum(c[0] for c in self._counters)

    def finish(self):
        total = self.dirs_scanned
        elapsed = time.monotonic() - self.start_time
        if total >= 100:
            rate = int(total / elapsed) if elapsed > 0 else 0
            print(f"\r  Scanned {total:,} dirs "
                  f"in {elapsed:.1f}s ({rate:,}/s)          ")


# ── Single-Threaded Scanner ─────────────────────────────────────────────────

def scan_directory(path: str, ext_stats: dict, progress: ProgressTracker = None,
                   follow_symlinks: bool = False,
                   top_heap: TopFilesHeap = None,
                   cache: ScanCache = None,
                   exclude: list[str] | None = None) -> DirNode:
    """Recursively scan a directory tree and build a DirNode hierarchy."""
    root_name = os.path.basename(path) or path
    node = DirNode(root_name, path)

    try:
        dir_stat = os.stat(path)
        dir_mtime = dir_stat.st_mtime
    except OSError:
        dir_mtime = None

    try:
        entries = list(os.scandir(path))
    except PermissionError:
        node.error = "Permission denied"
        return node
    except OSError as e:
        node.error = str(e)
        return node

    # Try cache for this directory's direct files
    cached = cache.lookup(path, dir_mtime) if cache and dir_mtime else None
    local_file_size = 0
    local_file_count = 0
    local_ext: dict[str, dict] = {}

    if cached:
        # Use cached file data — skip stat() calls on individual files
        cached_files, cached_ext = cached
        for fname, fsize in cached_files:
            child = DirNode(fname, os.path.join(path, fname), is_file=True)
            child.size = fsize
            child.file_count = 1
            node.children.append(child)
            local_file_size += fsize
            if top_heap:
                top_heap.push(fsize, child.path)
        local_file_count = len(cached_files)
        local_ext = cached_ext
        for ext, info in cached_ext.items():
            ext_stats[ext]["size"] += info["size"]
            ext_stats[ext]["count"] += info["count"]
    else:
        # Full scan of files in this directory
        files_for_cache: list[tuple[str, int]] = []
        dir_ext: dict[str, dict] = defaultdict(lambda: {"size": 0, "count": 0})

        for entry in entries:
            try:
                if entry.is_symlink() and not follow_symlinks:
                    continue
                if entry.is_file(follow_symlinks=follow_symlinks):
                    try:
                        st = entry.stat(follow_symlinks=follow_symlinks)
                        fsize = st.st_size
                    except (OSError, PermissionError):
                        fsize = 0
                    child = DirNode(entry.name, entry.path, is_file=True)
                    child.size = fsize
                    child.file_count = 1
                    node.children.append(child)
                    local_file_size += fsize
                    local_file_count += 1
                    files_for_cache.append((entry.name, fsize))
                    if top_heap:
                        top_heap.push(fsize, entry.path)
                    ext = _get_ext(entry.name)
                    dir_ext[ext]["size"] += fsize
                    dir_ext[ext]["count"] += 1
            except (PermissionError, OSError):
                continue

        # Merge dir-level ext stats into the running total
        for ext, info in dir_ext.items():
            ext_stats[ext]["size"] += info["size"]
            ext_stats[ext]["count"] += info["count"]

        local_ext = {k: dict(v) for k, v in dir_ext.items()}

        # Store in cache
        if cache and dir_mtime:
            cache.store(path, dir_mtime, local_file_size, local_file_count,
                        0, files_for_cache, local_ext)

    node.size = local_file_size
    node.file_count = local_file_count

    # Recurse into subdirectories (always — mtime of parent doesn't guarantee
    # children are unchanged)
    for entry in entries:
        try:
            if entry.is_symlink() and not follow_symlinks:
                continue
            if entry.is_dir(follow_symlinks=follow_symlinks):
                if exclude and any(fnmatch.fnmatch(entry.name, pat)
                                   for pat in exclude):
                    continue
                child = scan_directory(entry.path, ext_stats, progress,
                                       follow_symlinks, top_heap, cache,
                                       exclude)
                node.children.append(child)
                node.size += child.size
                node.file_count += child.file_count
                node.dir_count += child.dir_count + 1
        except (PermissionError, OSError):
            continue

    node.children.sort(key=lambda n: n.size, reverse=True)

    if progress:
        progress.update()

    return node


# ── Work-Queue Parallel Scanner ──────────────────────────────────────────────

def _scan_one_dir(path: str, follow_symlinks: bool, cache: ScanCache = None,
                  exclude: list[str] | None = None
                  ) -> tuple[str, list[tuple[str, int, bool]], int, int,
                             dict, str | None]:
    """Scan a single directory (non-recursive). Returns data for assembly.

    Returns:
        (path, entries, file_size, file_count, ext_stats, error)
        entries: list of (name, size_or_0, is_dir)
    """
    try:
        dir_stat = os.stat(path)
        dir_mtime = dir_stat.st_mtime
    except OSError:
        dir_mtime = None

    try:
        raw_entries = list(os.scandir(path))
    except PermissionError:
        return (path, [], 0, 0, {}, "Permission denied")
    except OSError as e:
        return (path, [], 0, 0, {}, str(e))

    result_entries: list[tuple[str, int, bool]] = []
    total_file_size = 0
    total_file_count = 0
    dir_ext: dict[str, dict] = {}

    # Check cache for this directory's files
    cached = cache.lookup(path, dir_mtime) if cache and dir_mtime else None

    if cached:
        cached_files, dir_ext = cached
        for fname, fsize in cached_files:
            result_entries.append((fname, fsize, False))
            total_file_size += fsize
            total_file_count += 1
    else:
        files_for_cache: list[tuple[str, int]] = []
        ext_accum: dict[str, dict] = defaultdict(lambda: {"size": 0, "count": 0})

        for entry in raw_entries:
            try:
                if entry.is_symlink() and not follow_symlinks:
                    continue
                if entry.is_file(follow_symlinks=follow_symlinks):
                    try:
                        st = entry.stat(follow_symlinks=follow_symlinks)
                        fsize = st.st_size
                    except (OSError, PermissionError):
                        fsize = 0
                    result_entries.append((entry.name, fsize, False))
                    total_file_size += fsize
                    total_file_count += 1
                    files_for_cache.append((entry.name, fsize))
                    ext = _get_ext(entry.name)
                    ext_accum[ext]["size"] += fsize
                    ext_accum[ext]["count"] += 1
            except (PermissionError, OSError):
                continue

        dir_ext = {k: dict(v) for k, v in ext_accum.items()}

        if cache and dir_mtime:
            cache.store(path, dir_mtime, total_file_size, total_file_count,
                        0, files_for_cache, dir_ext)

    # Discover subdirectories (always from live scandir, not cache)
    for entry in raw_entries:
        try:
            if entry.is_symlink() and not follow_symlinks:
                continue
            if entry.is_dir(follow_symlinks=follow_symlinks):
                if exclude and any(fnmatch.fnmatch(entry.name, pat)
                                   for pat in exclude):
                    continue
                result_entries.append((entry.name, 0, True))
        except (PermissionError, OSError):
            continue

    return (path, result_entries, total_file_size, total_file_count,
            dir_ext, None)


def scan_directory_parallel(path: str, ext_stats: dict,
                            progress: ProgressTracker = None,
                            follow_symlinks: bool = False,
                            jobs: int = 4,
                            top_heap: TopFilesHeap = None,
                            cache: ScanCache = None,
                            exclude: list[str] | None = None) -> DirNode:
    """Scan using a work-queue thread pool for deep parallelism.

    Unlike the old approach (parallelize only at depth 1), this submits
    every directory to the thread pool as it is discovered. Work is
    naturally distributed across threads regardless of tree shape.
    """
    work_q: queue.Queue[str] = queue.Queue()
    # results: path -> (entries, file_size, file_count, ext_stats, error)
    results: dict[str, tuple] = {}
    results_lock = threading.Lock()
    active = threading.Semaphore(0)
    pending = [0]
    pending_lock = threading.Lock()
    done_event = threading.Event()

    # Per-thread top-files heaps (merged at end)
    thread_heaps: list[TopFilesHeap] = []
    thread_heaps_lock = threading.Lock()
    _tls = threading.local()

    def _get_thread_heap() -> TopFilesHeap | None:
        if top_heap is None:
            return None
        h = getattr(_tls, "heap", None)
        if h is None:
            h = TopFilesHeap(top_heap._max_size)
            _tls.heap = h
            with thread_heaps_lock:
                thread_heaps.append(h)
        return h

    def worker():
        while True:
            try:
                dir_path = work_q.get(timeout=0.1)
            except queue.Empty:
                if done_event.is_set():
                    return
                continue

            result = _scan_one_dir(dir_path, follow_symlinks, cache, exclude)
            _, entries, _, _, _, _ = result

            # Push file sizes into thread-local heap
            th = _get_thread_heap()
            if th:
                for name, size, is_dir in entries:
                    if not is_dir and size > 0:
                        th.push(size, os.path.join(dir_path, name))

            # Discover child directories and enqueue them
            child_dirs = [os.path.join(dir_path, name)
                          for name, _, is_dir in entries if is_dir]

            with pending_lock:
                pending[0] += len(child_dirs)

            for child_path in child_dirs:
                work_q.put(child_path)

            with results_lock:
                results[dir_path] = result

            if progress:
                progress.update()

            with pending_lock:
                pending[0] -= 1
                if pending[0] <= 0 and work_q.empty():
                    done_event.set()

    # Start workers
    threads = []
    for _ in range(jobs):
        t = threading.Thread(target=worker, daemon=True)
        t.start()
        threads.append(t)

    # Seed the queue with the root directory
    with pending_lock:
        pending[0] = 1
    work_q.put(path)

    # Wait for completion
    done_event.wait()
    # Give workers time to drain
    for t in threads:
        t.join(timeout=2.0)

    # Flush cache periodically-accumulated writes
    if cache:
        cache.flush()

    # Merge thread-local heaps
    if top_heap:
        for th in thread_heaps:
            top_heap.merge(th)

    # Merge ext stats from all results
    for _, (_, _, _, _, dir_ext, _) in results.items():
        for ext_key, info in dir_ext.items():
            ext_stats[ext_key]["size"] += info["size"]
            ext_stats[ext_key]["count"] += info["count"]

    # ── Assemble the tree from flat results ──
    def _build_node(dir_path: str) -> DirNode:
        name = os.path.basename(dir_path) or dir_path
        node = DirNode(name, dir_path)

        if dir_path not in results:
            node.error = "Not scanned"
            return node

        _, entries, file_size, file_count, _, error = results[dir_path]
        if error:
            node.error = error
            return node

        node.size = file_size
        node.file_count = file_count

        for ename, esize, is_dir in entries:
            if is_dir:
                child_path = os.path.join(dir_path, ename)
                child = _build_node(child_path)
                node.children.append(child)
                node.size += child.size
                node.file_count += child.file_count
                node.dir_count += child.dir_count + 1
            else:
                child = DirNode(ename, os.path.join(dir_path, ename),
                                is_file=True)
                child.size = esize
                child.file_count = 1
                node.children.append(child)

        node.children.sort(key=lambda n: n.size, reverse=True)
        return node

    return _build_node(path)

# ── Tree Printer ─────────────────────────────────────────────────────────────

TREE_BRANCH = "├── "
TREE_LAST   = "└── "
TREE_PIPE   = "│   "
TREE_SPACE  = "    "

def print_tree(node: DirNode, total_size: int, max_depth: int = 3,
               min_pct: float = 0.01, top_n: int = 15,
               prefix: str = "", is_last: bool = True, depth: int = 0):
    """Print a tree view of the directory structure."""
    if total_size == 0:
        frac = 0.0
    else:
        frac = node.size / total_size

    # Skip tiny entries after first level
    if depth > 0 and frac < min_pct:
        return False  # signal that we skipped

    # Build the line
    size_part = color_size(node.size)
    pct_part = c(Color.CYAN, pct_str(frac))
    bar_part = make_bar(frac, 20)

    if depth == 0:
        connector = ""
        name = c(Color.BOLD + Color.BLUE, f"📁 {node.path}")
    else:
        connector = prefix + (TREE_LAST if is_last else TREE_BRANCH)
        if node.is_file:
            name = c(Color.WHITE, node.name)
        elif node.error:
            name = c(Color.RED, f"📁 {node.name} [{node.error}]")
        else:
            name = c(Color.BLUE, f"📁 {node.name}/")

    print(f"  {size_part}  {pct_part}  {bar_part}  {connector}{name}")

    # Recurse into children
    if not node.is_file and depth < max_depth:
        child_prefix = prefix + (TREE_SPACE if is_last else TREE_PIPE)
        visible_children = []
        hidden_size = 0
        hidden_count = 0

        for child in node.children:
            child_frac = child.size / total_size if total_size > 0 else 0
            if child_frac >= min_pct and len(visible_children) < top_n:
                visible_children.append(child)
            else:
                hidden_size += child.size
                hidden_count += 1

        for i, child in enumerate(visible_children):
            is_child_last = (i == len(visible_children) - 1) and hidden_count == 0
            print_tree(child, total_size, max_depth, min_pct, top_n,
                       child_prefix, is_child_last, depth + 1)

        if hidden_count > 0:
            hfrac = hidden_size / total_size if total_size > 0 else 0
            hsize = color_size(hidden_size)
            hpct = c(Color.DIM, pct_str(hfrac))
            hbar = make_bar(hfrac, 20)
            hconn = child_prefix + TREE_LAST
            htxt = c(Color.DIM, f"... {hidden_count} more items")
            print(f"  {hsize}  {hpct}  {hbar}  {hconn}{htxt}")

    return True

# ── Extension Stats Printer ──────────────────────────────────────────────────

def print_ext_stats(ext_stats: dict, total_size: int, top_n: int = 20):
    """Print a breakdown of space usage by file extension."""
    sorted_exts = sorted(ext_stats.items(), key=lambda x: x[1]["size"],
                         reverse=True)[:top_n]

    if not sorted_exts:
        return

    print(c(Color.BOLD, "\n  ╔══════════════════════════════════════════════"
            "══════════════════════════════════════════╗"))
    print(c(Color.BOLD, "  ║  FILE TYPE BREAKDOWN"
            "                                                              ║"))
    print(c(Color.BOLD, "  ╚══════════════════════════════════════════════"
            "══════════════════════════════════════════╝"))

    header = (f"  {'Extension':<12} {'Size':>12}  {'% of Total':>8}"
              f"  {'Count':>8}  {'Avg Size':>12}  Bar")
    print(c(Color.BOLD, header))
    print(f"  {'─' * 12} {'─' * 12}  {'─' * 8}  {'─' * 8}  {'─' * 12}  {'─' * 20}")

    for ext, info in sorted_exts:
        frac = info["size"] / total_size if total_size > 0 else 0
        avg = info["size"] // info["count"] if info["count"] > 0 else 0
        ext_display = c(Color.YELLOW, f"{ext:<12}")
        size_display = color_size(info["size"])
        pct_display = c(Color.CYAN, pct_str(frac))
        count_display = c(Color.WHITE, f"{info['count']:>8,}")
        avg_display = fmt_size(avg)
        bar = make_bar(frac, 20)
        print(f"  {ext_display} {size_display}  {pct_display}"
              f"  {count_display}  {avg_display}  {bar}")

    remaining = len(ext_stats) - top_n
    if remaining > 0:
        print(c(Color.DIM, f"\n  ... and {remaining} more file types"))

# ── Top Files Printer ────────────────────────────────────────────────────────

def find_top_files(node: DirNode, top_n: int = 15) -> list[DirNode]:
    """Find the N largest files via tree traversal (fallback path)."""
    heap: list[tuple[int, str, str]] = []  # (size, path, name)

    def _collect(n: DirNode):
        if n.is_file:
            if len(heap) < top_n:
                heapq.heappush(heap, (n.size, n.path, n.name))
            elif n.size > heap[0][0]:
                heapq.heapreplace(heap, (n.size, n.path, n.name))
            return
        for child in n.children:
            _collect(child)

    _collect(node)
    return sorted(heap, key=lambda x: x[0], reverse=True)

def print_top_files(scan_root: str, total_size: int,
                    top_files: list[tuple[int, str]], top_n: int = 15):
    """Print the largest files found. Accepts (size, path) tuples."""
    if not top_files:
        return

    print(c(Color.BOLD, "\n  ╔══════════════════════════════════════════════"
            "══════════════════════════════════════════╗"))
    print(c(Color.BOLD, "  ║  LARGEST FILES"
            "                                                                   ║"))
    print(c(Color.BOLD, "  ╚══════════════════════════════════════════════"
            "══════════════════════════════════════════╝"))

    header = f"  {'#':>3}  {'Size':>12}  {'% of Total':>8}  Path"
    print(c(Color.BOLD, header))
    print(f"  {'─' * 3}  {'─' * 12}  {'─' * 8}  {'─' * 50}")

    for i, (fsize, fpath) in enumerate(top_files[:top_n], 1):
        frac = fsize / total_size if total_size > 0 else 0
        num = c(Color.DIM, f"{i:>3}")
        size = color_size(fsize)
        pct = c(Color.CYAN, pct_str(frac))

        # Show path relative to scan root
        try:
            rel = os.path.relpath(fpath, scan_root)
        except ValueError:
            rel = fpath
        path_display = c(Color.WHITE, rel)

        print(f"  {num}  {size}  {pct}  {path_display}")

# ── Summary ──────────────────────────────────────────────────────────────────

def print_summary(node: DirNode, scan_path: str):
    """Print scan summary info."""
    print(c(Color.BOLD, "\n  ╔══════════════════════════════════════════════"
            "══════════════════════════════════════════╗"))
    print(c(Color.BOLD, "  ║  WSL-DIR-STAT  ·  Disk Usage Analyzer"
            "                                            ║"))
    print(c(Color.BOLD, "  ╚══════════════════════════════════════════════"
            "══════════════════════════════════════════╝"))

    print(f"\n  {c(Color.BOLD, 'Scanned:')}  {c(Color.BLUE, scan_path)}")
    print(f"  {c(Color.BOLD, 'Total:')}    {color_size(node.size)}")
    print(f"  {c(Color.BOLD, 'Files:')}    {c(Color.WHITE, f'{node.file_count:,}')}")
    print(f"  {c(Color.BOLD, 'Dirs:')}     {c(Color.WHITE, f'{node.dir_count:,}')}")

# ── Disk Usage (mount info) ─────────────────────────────────────────────────

def print_disk_usage(path: str):
    """Show disk usage of the filesystem containing the scanned path."""
    try:
        stat = os.statvfs(path)
        total = stat.f_blocks * stat.f_frsize
        free = stat.f_bfree * stat.f_frsize
        avail = stat.f_bavail * stat.f_frsize
        used = total - free

        if total == 0:
            return

        frac = used / total

        print(f"\n  {c(Color.BOLD, 'Disk:')}     "
              f"{color_size(used)} used / {fmt_size(total)} total "
              f"({fmt_size(avail)} avail)")
        print(f"           {make_bar(frac, 40)}  "
              f"{c(Color.CYAN, pct_str(frac))}")
    except OSError:
        pass

# ── Docker Disk Usage ────────────────────────────────────────────────────────

def _parse_docker_size(s: str) -> int:
    """Parse Docker's human-readable size string (e.g. '22.4GB') to bytes."""
    s = s.strip()
    if s == "0B" or not s:
        return 0
    multipliers = {
        'B': 1, 'KB': 1000, 'MB': 1000**2, 'GB': 1000**3, 'TB': 1000**4,
        'kB': 1000, 'KiB': 1024, 'MiB': 1024**2, 'GiB': 1024**3, 'TiB': 1024**4,
    }
    for suffix, mult in sorted(multipliers.items(), key=lambda x: -len(x[0])):
        if s.endswith(suffix):
            try:
                return int(float(s[:-len(suffix)]) * mult)
            except ValueError:
                return 0
    try:
        return int(float(s))
    except ValueError:
        return 0


def get_docker_usage() -> dict | None:
    """Run 'docker system df' and parse the output.

    Returns a dict with keys: rows, total, reclaimable.
    Each row is a dict with: type, total, active, size, reclaimable, etc.
    Returns None if Docker is unavailable.
    """
    if not shutil.which("docker"):
        return None
    try:
        result = subprocess.run(
            ["docker", "system", "df", "--format",
             "{{.Type}}\t{{.TotalCount}}\t{{.Active}}\t{{.Size}}\t{{.Reclaimable}}"],
            capture_output=True, text=True, timeout=120,
        )
        if result.returncode != 0:
            return None
    except (subprocess.TimeoutExpired, OSError):
        return None

    rows = []
    for line in result.stdout.strip().splitlines():
        parts = line.split("\t")
        if len(parts) < 5:
            continue
        reclaimable_str = parts[4].strip()
        reclaim_paren = ""
        if " (" in reclaimable_str:
            reclaim_val, reclaim_paren = reclaimable_str.rsplit(" (", 1)
            reclaim_paren = reclaim_paren.rstrip(")")
        else:
            reclaim_val = reclaimable_str
        rows.append({
            "type": parts[0].strip(),
            "total": int(parts[1].strip()) if parts[1].strip().isdigit() else 0,
            "active": int(parts[2].strip()) if parts[2].strip().isdigit() else 0,
            "size": _parse_docker_size(parts[3]),
            "size_raw": parts[3].strip(),
            "reclaimable": _parse_docker_size(reclaim_val),
            "reclaimable_raw": reclaimable_str,
            "reclaimable_pct": reclaim_paren,
        })

    if not rows:
        return None

    docker_total = sum(r["size"] for r in rows)
    docker_reclaimable = sum(r["reclaimable"] for r in rows)
    return {"rows": rows, "total": docker_total, "reclaimable": docker_reclaimable}


def print_docker_usage(docker_info: dict):
    """Print Docker disk usage to terminal."""
    print(f"\n  {c(Color.BOLD, 'Docker:')}   "
          f"{color_size(docker_info['total'])} total"
          f" ({fmt_size(docker_info['reclaimable']).strip()} reclaimable)")

    header = (f"  {'Type':<16} {'Total':>6} {'Active':>7} "
              f"{'Size':>12}  {'Reclaimable':>20}")
    print(f"  {c(Color.DIM, '─' * 68)}")
    print(f"  {c(Color.DIM, header.strip())}")
    for row in docker_info["rows"]:
        print(f"  {row['type']:<16} {row['total']:>6} {row['active']:>7} "
              f"{color_size(row['size'])}  "
              f"{fmt_size(row['reclaimable']).strip():>12}"
              f" {c(Color.DIM, '(' + row['reclaimable_pct'] + ')') if row['reclaimable_pct'] else ''}")


# ── Directory Tree View ──────────────────────────────────────────────────────

def print_directory_tree(node: DirNode, total_size: int, max_depth: int,
                         min_pct: float, top_n_children: int):
    """Print the directory tree section."""
    print(c(Color.BOLD, "\n  ╔══════════════════════════════════════════════"
            "══════════════════════════════════════════╗"))
    print(c(Color.BOLD, "  ║  DIRECTORY TREE"
            "                                                                  ║"))
    print(c(Color.BOLD, "  ╚══════════════════════════════════════════════"
            "══════════════════════════════════════════╝"))
    print()

    print_tree(node, total_size, max_depth=max_depth, min_pct=min_pct,
               top_n=top_n_children)

# ── Text Report ──────────────────────────────────────────────────────────────

def generate_text_report(root: DirNode, scan_path: str, ext_stats: dict,
                         top_files: list[tuple[int, str]],
                         max_depth: int, min_pct: float,
                         top_n_children: int, top_n_exts: int,
                         docker_info: dict | None = None) -> str:
    """Generate a plain-text report (no ANSI colors)."""
    lines: list[str] = []
    W = lines.append

    W("=" * 78)
    W("  WSL-DIR-STAT  ·  Disk Usage Report")
    W("=" * 78)
    W("")
    W(f"  Scanned:  {scan_path}")
    W(f"  Total:    {fmt_size(root.size).strip()}")
    W(f"  Files:    {root.file_count:,}")
    W(f"  Dirs:     {root.dir_count:,}")

    # Disk usage
    try:
        st = os.statvfs(scan_path)
        total = st.f_blocks * st.f_frsize
        free = st.f_bfree * st.f_frsize
        avail = st.f_bavail * st.f_frsize
        used = total - free
        if total > 0:
            pct = used / total * 100
            bar_w = 40
            filled = int(used / total * bar_w)
            bar = "#" * filled + "." * (bar_w - filled)
            W(f"\n  Disk:     {fmt_size(used).strip()} used"
              f" / {fmt_size(total).strip()} total"
              f" ({fmt_size(avail).strip()} avail)")
            W(f"            [{bar}] {pct:.1f}%")
    except OSError:
        pass

    # Docker usage
    if docker_info:
        W(f"\n  Docker:   {fmt_size(docker_info['total']).strip()} total"
          f" ({fmt_size(docker_info['reclaimable']).strip()} reclaimable)")
        W(f"  {'Type':<16} {'Total':>6} {'Active':>7} {'Size':>12}  {'Reclaimable':>20}")
        W(f"  {'─' * 68}")
        for row in docker_info["rows"]:
            reclaim_str = fmt_size(row['reclaimable']).strip()
            if row['reclaimable_pct']:
                reclaim_str += f" ({row['reclaimable_pct']})"
            W(f"  {row['type']:<16} {row['total']:>6} {row['active']:>7} "
              f"{fmt_size(row['size']).strip():>12}  {reclaim_str:>20}")

    # Directory tree
    W("")
    W("-" * 78)
    W("  DIRECTORY TREE")
    W("-" * 78)
    W("")

    def _text_tree(node: DirNode, total_size: int, prefix: str = "",
                   is_last: bool = True, depth: int = 0):
        frac = node.size / total_size if total_size > 0 else 0
        if depth > 0 and frac < min_pct:
            return

        size_s = fmt_size(node.size).strip()
        pct_s = f"{frac * 100:5.1f}%" if frac >= 0.01 else " <1.0%"

        if depth == 0:
            W(f"  {size_s:>12}  {pct_s}  {node.path}")
        else:
            conn = prefix + ("└── " if is_last else "├── ")
            label = node.name if node.is_file else f"{node.name}/"
            if node.error:
                label += f" [{node.error}]"
            W(f"  {size_s:>12}  {pct_s}  {conn}{label}")

        if not node.is_file and depth < max_depth:
            child_prefix = prefix + ("    " if is_last else "│   ")
            visible = []
            hidden_size = 0
            hidden_count = 0
            for ch in node.children:
                ch_frac = ch.size / total_size if total_size > 0 else 0
                if ch_frac >= min_pct and len(visible) < top_n_children:
                    visible.append(ch)
                else:
                    hidden_size += ch.size
                    hidden_count += 1
            for i, ch in enumerate(visible):
                ch_last = (i == len(visible) - 1) and hidden_count == 0
                _text_tree(ch, total_size, child_prefix, ch_last, depth + 1)
            if hidden_count > 0:
                h_frac = hidden_size / total_size if total_size > 0 else 0
                h_pct = f"{h_frac * 100:5.1f}%" if h_frac >= 0.01 else " <1.0%"
                h_conn = child_prefix + "└── "
                W(f"  {fmt_size(hidden_size).strip():>12}  {h_pct}"
                  f"  {h_conn}... {hidden_count} more items")

    _text_tree(root, root.size)

    # Extension breakdown
    sorted_exts = sorted(ext_stats.items(), key=lambda x: x[1]["size"],
                         reverse=True)[:top_n_exts]
    if sorted_exts:
        W("")
        W("-" * 78)
        W("  FILE TYPE BREAKDOWN")
        W("-" * 78)
        W(f"  {'Extension':<12} {'Size':>12}  {'%':>6}  {'Count':>8}  {'Avg Size':>12}")
        W(f"  {'─' * 12} {'─' * 12}  {'─' * 6}  {'─' * 8}  {'─' * 12}")
        for ext, info in sorted_exts:
            frac = info["size"] / root.size * 100 if root.size > 0 else 0
            avg = info["size"] // info["count"] if info["count"] > 0 else 0
            W(f"  {ext:<12} {fmt_size(info['size']).strip():>12}"
              f"  {frac:5.1f}%  {info['count']:>8,}  {fmt_size(avg).strip():>12}")
        remaining = len(ext_stats) - top_n_exts
        if remaining > 0:
            W(f"\n  ... and {remaining} more file types")

    # Top files
    if top_files:
        W("")
        W("-" * 78)
        W("  LARGEST FILES")
        W("-" * 78)
        W(f"  {'#':>3}  {'Size':>12}  {'%':>6}  Path")
        W(f"  {'─' * 3}  {'─' * 12}  {'─' * 6}  {'─' * 50}")
        for i, (fsize, fpath) in enumerate(top_files, 1):
            frac = fsize / root.size * 100 if root.size > 0 else 0
            try:
                rel = os.path.relpath(fpath, scan_path)
            except ValueError:
                rel = fpath
            W(f"  {i:>3}  {fmt_size(fsize).strip():>12}  {frac:5.1f}%  {rel}")

    W("")
    return "\n".join(lines)


# ── HTML Report ──────────────────────────────────────────────────────────────

def _html_escape(text: str) -> str:
    return text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")

def generate_html_report(root: DirNode, scan_path: str, ext_stats: dict,
                         top_files: list[tuple[int, str]],
                         max_depth: int, min_pct: float,
                         top_n_children: int, top_n_exts: int,
                         docker_info: dict | None = None) -> str:
    """Generate a standalone interactive HTML report."""

    # ── Build tree JSON for the interactive view ──
    def _node_json(node: DirNode, total_size: int, depth: int = 0) -> dict:
        frac = node.size / total_size if total_size > 0 else 0
        d = {
            "name": node.name,
            "size": node.size,
            "size_fmt": fmt_size(node.size).strip(),
            "pct": round(frac * 100, 2),
            "is_file": node.is_file,
        }
        if node.error:
            d["error"] = node.error
        if not node.is_file and depth < max_depth + 2:
            children = []
            for ch in node.children:
                ch_frac = ch.size / total_size if total_size > 0 else 0
                if ch_frac >= min_pct * 0.1 and len(children) < top_n_children * 2:
                    children.append(_node_json(ch, total_size, depth + 1))
            d["children"] = children
        return d

    tree_json = json.dumps(_node_json(root, root.size), separators=(",", ":"))

    # ── Build ext stats for the table ──
    sorted_exts = sorted(ext_stats.items(), key=lambda x: x[1]["size"],
                         reverse=True)[:top_n_exts]
    ext_rows = ""
    for ext, info in sorted_exts:
        frac = info["size"] / root.size * 100 if root.size > 0 else 0
        avg = info["size"] // info["count"] if info["count"] > 0 else 0
        ext_rows += (
            f'<tr><td>{_html_escape(ext)}</td>'
            f'<td class="num">{fmt_size(info["size"]).strip()}</td>'
            f'<td class="num">{frac:.1f}%</td>'
            f'<td class="num">{info["count"]:,}</td>'
            f'<td class="num">{fmt_size(avg).strip()}</td>'
            f'<td><div class="bar"><div class="bar-fill" style="width:{min(frac, 100):.1f}%"></div></div></td>'
            f'</tr>\n'
        )

    # ── Build top files table ──
    files_rows = ""
    for i, (fsize, fpath) in enumerate(top_files, 1):
        frac = fsize / root.size * 100 if root.size > 0 else 0
        try:
            rel = os.path.relpath(fpath, scan_path)
        except ValueError:
            rel = fpath
        files_rows += (
            f'<tr><td class="num">{i}</td>'
            f'<td class="num">{fmt_size(fsize).strip()}</td>'
            f'<td class="num">{frac:.1f}%</td>'
            f'<td class="path">{_html_escape(rel)}</td></tr>\n'
        )

    # ── Disk info ──
    disk_html = ""
    try:
        st = os.statvfs(scan_path)
        total = st.f_blocks * st.f_frsize
        free = st.f_bfree * st.f_frsize
        avail = st.f_bavail * st.f_frsize
        used = total - free
        if total > 0:
            pct = used / total * 100
            disk_html = f"""
            <div class="stat-card">
              <div class="stat-label">Disk Usage</div>
              <div class="stat-value">{fmt_size(used).strip()} / {fmt_size(total).strip()}</div>
              <div class="disk-bar"><div class="disk-fill" style="width:{pct:.1f}%"></div></div>
              <div class="stat-sub">{pct:.1f}% used · {fmt_size(avail).strip()} available</div>
            </div>"""
    except OSError:
        pass

    # ── Docker info ──
    docker_html = ""
    docker_table_html = ""
    if docker_info:
        docker_html = f"""
            <div class="stat-card">
              <div class="stat-label">Docker Usage</div>
              <div class="stat-value">{fmt_size(docker_info['total']).strip()}</div>
              <div class="stat-sub">{fmt_size(docker_info['reclaimable']).strip()} reclaimable</div>
            </div>"""
        docker_rows = ""
        for row in docker_info["rows"]:
            reclaim_str = _html_escape(fmt_size(row['reclaimable']).strip())
            if row['reclaimable_pct']:
                reclaim_str += f" ({_html_escape(row['reclaimable_pct'])})"
            docker_rows += (
                f'<tr><td>{_html_escape(row["type"])}</td>'
                f'<td class="num">{row["total"]}</td>'
                f'<td class="num">{row["active"]}</td>'
                f'<td class="num">{fmt_size(row["size"]).strip()}</td>'
                f'<td class="num">{reclaim_str}</td></tr>\n'
            )
        docker_table_html = f"""
<h2>🐳 Docker Disk Usage</h2>
<table id="docker-table">
<thead><tr>
  <th>Type</th>
  <th data-sort="num">Total</th>
  <th data-sort="num">Active</th>
  <th data-sort="num">Size</th>
  <th data-sort="num">Reclaimable</th>
</tr></thead>
<tbody>
{docker_rows}
</tbody>
</table>
"""

    # ── Treemap data (top-level children only for simplicity) ──
    treemap_items = ""
    colors = ["#4e79a7","#f28e2b","#e15759","#76b7b2","#59a14f",
              "#edc948","#b07aa1","#ff9da7","#9c755f","#bab0ac",
              "#86bcb6","#8cd17d","#b6992d","#499894","#d37295"]
    for i, ch in enumerate(root.children[:20]):
        if ch.size <= 0:
            continue
        frac = ch.size / root.size * 100 if root.size > 0 else 0
        if frac < 0.5:
            continue
        color = colors[i % len(colors)]
        label = _html_escape(ch.name)
        treemap_items += (
            f'<div class="tm-item" style="flex-grow:{max(1, int(frac * 10))}; '
            f'background:{color}" title="{label}: {fmt_size(ch.size).strip()} ({frac:.1f}%)">'
            f'<span class="tm-label">{label}</span>'
            f'<span class="tm-size">{fmt_size(ch.size).strip()}</span></div>\n'
        )

    scan_time = time.strftime("%Y-%m-%d %H:%M:%S")

    html = f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>WSL-DIR-STAT · {_html_escape(scan_path)}</title>
<style>
  :root {{
    --bg: #1a1b26; --surface: #24283b; --surface2: #2f3347;
    --text: #c0caf5; --text-dim: #565f89; --accent: #7aa2f7;
    --green: #9ece6a; --yellow: #e0af68; --red: #f7768e;
    --orange: #ff9e64; --cyan: #7dcfff; --purple: #bb9af7;
    --border: #3b4261;
  }}
  * {{ box-sizing: border-box; margin: 0; padding: 0; }}
  body {{
    font-family: 'Segoe UI', system-ui, -apple-system, sans-serif;
    background: var(--bg); color: var(--text); padding: 24px;
    line-height: 1.5; max-width: 1400px; margin: 0 auto;
  }}
  h1 {{ color: var(--accent); font-size: 1.6rem; margin-bottom: 4px; }}
  h2 {{
    color: var(--accent); font-size: 1.1rem; margin: 32px 0 12px 0;
    padding-bottom: 6px; border-bottom: 2px solid var(--border);
  }}
  .subtitle {{ color: var(--text-dim); font-size: 0.85rem; margin-bottom: 20px; }}
  .stats-grid {{
    display: grid; grid-template-columns: repeat(auto-fit, minmax(200px, 1fr));
    gap: 12px; margin-bottom: 24px;
  }}
  .stat-card {{
    background: var(--surface); padding: 16px; border-radius: 8px;
    border: 1px solid var(--border);
  }}
  .stat-label {{ color: var(--text-dim); font-size: 0.8rem; text-transform: uppercase; letter-spacing: 0.05em; }}
  .stat-value {{ font-size: 1.4rem; font-weight: 700; color: var(--text); margin: 4px 0; }}
  .stat-sub {{ color: var(--text-dim); font-size: 0.8rem; }}
  .disk-bar {{
    height: 8px; background: var(--surface2); border-radius: 4px;
    margin: 8px 0 4px 0; overflow: hidden;
  }}
  .disk-fill {{
    height: 100%; border-radius: 4px;
    background: linear-gradient(90deg, var(--green), var(--yellow), var(--red));
  }}
  /* Treemap */
  .treemap {{
    display: flex; flex-wrap: wrap; gap: 2px; min-height: 80px;
    border-radius: 6px; overflow: hidden; margin-bottom: 24px;
  }}
  .tm-item {{
    display: flex; flex-direction: column; justify-content: center;
    align-items: center; min-width: 40px; min-height: 60px;
    padding: 6px 8px; color: #fff; font-size: 0.75rem;
    overflow: hidden; cursor: default; transition: opacity 0.2s;
  }}
  .tm-item:hover {{ opacity: 0.8; }}
  .tm-label {{ font-weight: 600; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; max-width: 100%; }}
  .tm-size {{ font-size: 0.65rem; opacity: 0.8; }}
  /* Tree */
  .tree {{ font-family: 'Cascadia Code', 'Fira Code', 'Consolas', monospace; font-size: 0.82rem; }}
  .tree details {{ margin-left: 20px; }}
  .tree details[open] > summary {{ margin-bottom: 2px; }}
  .tree summary {{
    cursor: pointer; padding: 2px 6px; border-radius: 4px;
    list-style: none; display: flex; align-items: center; gap: 8px;
  }}
  .tree summary::-webkit-details-marker {{ display: none; }}
  .tree summary:hover {{ background: var(--surface2); }}
  .tree .icon {{ width: 16px; text-align: center; flex-shrink: 0; }}
  .tree .name {{ color: var(--accent); }}
  .tree .name.file {{ color: var(--text); }}
  .tree .sz {{ color: var(--text-dim); font-size: 0.75rem; min-width: 90px; text-align: right; }}
  .tree .pct {{ color: var(--cyan); font-size: 0.75rem; min-width: 50px; text-align: right; }}
  .tree .bar {{ display: inline-block; height: 6px; border-radius: 3px; background: var(--accent); opacity: 0.5; margin-left: 6px; }}
  .tree .file-row {{
    margin-left: 20px; padding: 2px 6px; display: flex;
    align-items: center; gap: 8px; border-radius: 4px;
  }}
  .tree .file-row:hover {{ background: var(--surface2); }}
  .tree .more {{
    margin-left: 20px; padding: 4px 6px; color: var(--text-dim);
    font-style: italic; font-size: 0.78rem;
  }}
  /* Tables */
  table {{ width: 100%; border-collapse: collapse; font-size: 0.85rem; }}
  th {{
    text-align: left; padding: 8px 12px; border-bottom: 2px solid var(--border);
    color: var(--text-dim); text-transform: uppercase; font-size: 0.75rem;
    letter-spacing: 0.05em; cursor: pointer; user-select: none;
    position: relative;
  }}
  th:hover {{ color: var(--accent); }}
  th .sort-arrow {{ margin-left: 4px; font-size: 0.7rem; }}
  td {{ padding: 6px 12px; border-bottom: 1px solid var(--border); }}
  tr:hover td {{ background: var(--surface); }}
  .num {{ text-align: right; font-family: 'Cascadia Code', 'Fira Code', monospace; }}
  .path {{ word-break: break-all; color: var(--text-dim); }}
  .bar {{ height: 6px; background: var(--surface2); border-radius: 3px; min-width: 120px; }}
  .bar-fill {{ height: 100%; border-radius: 3px; background: linear-gradient(90deg, var(--green), var(--accent)); }}
  footer {{ margin-top: 40px; padding-top: 16px; border-top: 1px solid var(--border); color: var(--text-dim); font-size: 0.75rem; text-align: center; }}
</style>
</head>
<body>

<h1>📊 WSL-DIR-STAT</h1>
<div class="subtitle">Scanned <strong>{_html_escape(scan_path)}</strong> on {scan_time}</div>

<div class="stats-grid">
  <div class="stat-card">
    <div class="stat-label">Total Size</div>
    <div class="stat-value">{fmt_size(root.size).strip()}</div>
  </div>
  <div class="stat-card">
    <div class="stat-label">Files</div>
    <div class="stat-value">{root.file_count:,}</div>
  </div>
  <div class="stat-card">
    <div class="stat-label">Directories</div>
    <div class="stat-value">{root.dir_count:,}</div>
  </div>
  {disk_html}
  {docker_html}
</div>

<h2>📦 Space Distribution</h2>
<div class="treemap">
{treemap_items}
</div>

<h2>🌳 Directory Tree</h2>
<div class="tree" id="tree"></div>

<h2>📋 File Types</h2>
<table id="ext-table">
<thead><tr>
  <th data-sort="str">Extension</th>
  <th data-sort="num">Size</th>
  <th data-sort="num">%</th>
  <th data-sort="num">Count</th>
  <th data-sort="num">Avg Size</th>
  <th>Distribution</th>
</tr></thead>
<tbody>
{ext_rows}
</tbody>
</table>

<h2>📄 Largest Files</h2>
<table id="files-table">
<thead><tr>
  <th data-sort="num">#</th>
  <th data-sort="num">Size</th>
  <th data-sort="num">%</th>
  <th data-sort="str">Path</th>
</tr></thead>
<tbody>
{files_rows}
</tbody>
</table>

{docker_table_html}

<footer>Generated by wsl-dir-stat · {scan_time}</footer>

<script>
// ── Interactive Tree ──
const treeData = {tree_json};
const treeEl = document.getElementById('tree');

function buildTree(node, totalSize, depth, maxDepth) {{
  if (node.is_file) {{
    const row = document.createElement('div');
    row.className = 'file-row';
    const pct = totalSize > 0 ? (node.size / totalSize * 100) : 0;
    const barW = Math.max(1, Math.min(200, pct * 2));
    row.innerHTML = `<span class="icon">📄</span><span class="name file">${{esc(node.name)}}</span>`
      + `<span class="sz">${{node.size_fmt}}</span><span class="pct">${{pct.toFixed(1)}}%</span>`
      + `<span class="bar" style="width:${{barW}}px"></span>`;
    return row;
  }}

  const details = document.createElement('details');
  if (depth < 1) details.open = true;

  const summary = document.createElement('summary');
  const pct = totalSize > 0 ? (node.size / totalSize * 100) : 0;
  const barW = Math.max(1, Math.min(200, pct * 2));
  summary.innerHTML = `<span class="icon">📁</span><span class="name">${{esc(node.name)}}/</span>`
    + `<span class="sz">${{node.size_fmt}}</span><span class="pct">${{pct.toFixed(1)}}%</span>`
    + `<span class="bar" style="width:${{barW}}px"></span>`;
  details.appendChild(summary);

  if (node.children && depth < maxDepth) {{
    node.children.forEach(ch => {{
      details.appendChild(buildTree(ch, totalSize, depth + 1, maxDepth));
    }});
  }}
  if (node.error) {{
    const err = document.createElement('div');
    err.className = 'more';
    err.textContent = '⚠ ' + node.error;
    details.appendChild(err);
  }}
  return details;
}}

function esc(s) {{ const d = document.createElement('div'); d.textContent = s; return d.innerHTML; }}

treeEl.appendChild(buildTree(treeData, treeData.size, 0, {max_depth + 2}));

// ── Sortable Tables ──
document.querySelectorAll('th[data-sort]').forEach(th => {{
  th.addEventListener('click', () => {{
    const table = th.closest('table');
    const tbody = table.querySelector('tbody');
    const rows = Array.from(tbody.querySelectorAll('tr'));
    const idx = Array.from(th.parentNode.children).indexOf(th);
    const type = th.dataset.sort;
    const asc = th.classList.toggle('sort-asc');

    rows.sort((a, b) => {{
      let va = a.children[idx]?.textContent.trim() || '';
      let vb = b.children[idx]?.textContent.trim() || '';
      if (type === 'num') {{
        va = parseFloat(va.replace(/[^\\d.\\-]/g, '')) || 0;
        vb = parseFloat(vb.replace(/[^\\d.\\-]/g, '')) || 0;
        return asc ? va - vb : vb - va;
      }}
      return asc ? va.localeCompare(vb) : vb.localeCompare(va);
    }});
    rows.forEach(r => tbody.appendChild(r));

    th.parentNode.querySelectorAll('.sort-arrow').forEach(a => a.remove());
    const arrow = document.createElement('span');
    arrow.className = 'sort-arrow';
    arrow.textContent = asc ? '▲' : '▼';
    th.appendChild(arrow);
  }});
}});
</script>
</body>
</html>"""

    return html


# ── Main ─────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="wsl-dir-stat: WinDirStat-like disk usage analyzer for WSL",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s                      # Scan current directory
  %(prog)s /home                # Scan /home
  %(prog)s -d 5 /var            # Scan /var with depth 5
  %(prog)s -j 8 /home           # Scan with 8 threads
  %(prog)s -n 25 --no-tree /    # Top 25 files, skip tree, scan root
  %(prog)s -e node_modules -e .git .  # Exclude dirs by name
  %(prog)s -e '.*' /home        # Exclude all hidden directories
  %(prog)s --exts 30 ~/projects # Show top 30 file types
  %(prog)s --clear-cache        # Delete cached scan data
  %(prog)s --report-html r.html  # Generate interactive HTML report
  %(prog)s --report-text r.txt   # Generate plain-text report
  %(prog)s --docker /            # Include Docker disk usage in report

Environment:
  NO_COLOR=1                    # Disable colored output
        """,
    )
    parser.add_argument("path", nargs="?", default=".",
                        help="Directory to scan (default: current dir)")
    parser.add_argument("-d", "--depth", type=int, default=3,
                        help="Max tree depth to display (default: 3)")
    parser.add_argument("-n", "--top", type=int, default=15,
                        help="Number of largest files to show (default: 15)")
    parser.add_argument("--exts", type=int, default=20,
                        help="Number of file extensions to show (default: 20)")
    parser.add_argument("--min-pct", type=float, default=1.0,
                        help="Min %% of total to show in tree (default: 1.0)")
    parser.add_argument("--children", type=int, default=15,
                        help="Max children per directory in tree (default: 15)")
    parser.add_argument("--no-tree", action="store_true",
                        help="Skip the directory tree view")
    parser.add_argument("--no-files", action="store_true",
                        help="Skip the largest files list")
    parser.add_argument("--no-exts", action="store_true",
                        help="Skip the file type breakdown")
    parser.add_argument("--no-disk", action="store_true",
                        help="Skip filesystem disk usage info")
    parser.add_argument("--docker", action="store_true",
                        help="Include Docker disk usage (runs 'docker system df')")
    parser.add_argument("-L", "--follow-symlinks", action="store_true",
                        help="Follow symbolic links (default: skip)")
    parser.add_argument("-e", "--exclude", action="append", default=[],
                        metavar="PATTERN",
                        help="Exclude directories matching glob pattern "
                             "(repeatable, e.g. -e node_modules -e .git)")
    parser.add_argument("-j", "--jobs", type=int,
                        default=os.cpu_count() or 4,
                        help="Parallel threads for scanning "
                             f"(default: {os.cpu_count() or 4}, your CPU count)")
    parser.add_argument("--no-cache", action="store_true",
                        help="Disable scan cache (always do a fresh scan)")
    parser.add_argument("--clear-cache", action="store_true",
                        help="Delete cached scan data and exit")
    parser.add_argument("--report-html", metavar="FILE",
                        help="Write an interactive HTML report to FILE")
    parser.add_argument("--report-text", metavar="FILE",
                        help="Write a plain-text report to FILE")

    args = parser.parse_args()

    if args.clear_cache:
        ScanCache.clear()
        return

    scan_path = os.path.abspath(args.path)
    if not os.path.isdir(scan_path):
        print(f"Error: '{scan_path}' is not a directory.", file=sys.stderr)
        sys.exit(1)

    # Set up cache
    cache = ScanCache(enabled=not args.no_cache)
    cache.open()

    # Set up scanning
    ext_stats: dict = defaultdict(lambda: {"size": 0, "count": 0})
    progress = ProgressTracker()
    top_heap = TopFilesHeap(max_size=args.top)

    jobs = max(1, args.jobs)
    mode = f"{jobs} threads" if jobs > 1 else "single-threaded"
    cache_label = "" if args.no_cache else " +cache"
    print(f"\n  Scanning {c(Color.BLUE, scan_path)} "
          f"({mode}{cache_label}) ...", flush=True)

    exclude = args.exclude or None

    if jobs > 1:
        root = scan_directory_parallel(scan_path, ext_stats, progress,
                                       args.follow_symlinks, jobs,
                                       top_heap, cache, exclude)
    else:
        root = scan_directory(scan_path, ext_stats, progress,
                              args.follow_symlinks, top_heap, cache,
                              exclude)
    progress.finish()

    cache.close()

    # Show cache stats
    if cache.enabled and (cache.hits + cache.misses) > 0:
        total_lookups = cache.hits + cache.misses
        hit_pct = cache.hits / total_lookups * 100
        print(f"  Cache: {cache.hits:,} hits / {cache.misses:,} misses "
              f"({hit_pct:.0f}% hit rate)")

    # Print results
    print_summary(root, scan_path)

    if not args.no_disk:
        print_disk_usage(scan_path)

    docker_info = None
    if args.docker:
        print(f"  Querying Docker disk usage ...", end="", flush=True)
        docker_info = get_docker_usage()
        print("\r" + " " * 40 + "\r", end="", flush=True)
        if docker_info:
            print_docker_usage(docker_info)
        else:
            print(f"\n  {c(Color.DIM, 'Docker: not available '
                  '(not installed, daemon not running, or timed out)')}")

    if not args.no_tree:
        print_directory_tree(root, root.size, args.depth,
                             args.min_pct / 100.0, args.children)

    if not args.no_exts:
        print_ext_stats(ext_stats, root.size, args.exts)

    if not args.no_files:
        # Use heap if populated, fall back to tree traversal
        top_files = top_heap.get_sorted()
        if not top_files:
            top_files = [(s, p) for s, p, _ in find_top_files(root, args.top)]
        print_top_files(scan_path, root.size, top_files, args.top)
    else:
        top_files = top_heap.get_sorted()

    # ── Generate reports ──
    if args.report_text:
        if not top_files:
            top_files = top_heap.get_sorted()
            if not top_files:
                top_files = [(s, p) for s, p, _ in
                             find_top_files(root, args.top)]
        report = generate_text_report(root, scan_path, ext_stats, top_files,
                                      args.depth, args.min_pct / 100.0,
                                      args.children, args.exts,
                                      docker_info=docker_info)
        with open(args.report_text, "w", encoding="utf-8") as f:
            f.write(report)
        print(f"\n  Text report saved to: {c(Color.GREEN, args.report_text)}")

    if args.report_html:
        if not top_files:
            top_files = top_heap.get_sorted()
            if not top_files:
                top_files = [(s, p) for s, p, _ in
                             find_top_files(root, args.top)]
        report = generate_html_report(root, scan_path, ext_stats, top_files,
                                      args.depth, args.min_pct / 100.0,
                                      args.children, args.exts,
                                      docker_info=docker_info)
        with open(args.report_html, "w", encoding="utf-8") as f:
            f.write(report)
        print(f"\n  HTML report saved to: {c(Color.GREEN, args.report_html)}")

    print()  # final newline


if __name__ == "__main__":
    main()
