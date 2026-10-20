#!/usr/bin/env python3
"""Build the exact theorem's local imports one module at a time.

This script uses only normal `lake build +Module` invocations. It does not
trust file existence, edit traces, bypass hashes, or pass --old. Every module
is offered to Lake on every run, so resuming still validates dependencies.

Author: Joshua Wharton <joshua@qfex.com>, QFEX, 2026.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
IMPORT = re.compile(r"^\s*(?:public\s+)?import\s+(?:all\s+)?(.+?)\s*$")
MODULE_NAME = re.compile(r"^[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*$")


def strip_comments(source: str) -> str:
    """Remove nested Lean comments while preserving newlines and string text.

    Imports are read only from the initial header; the string handling keeps
    an incidental comment delimiter inside a string from changing the scan.
    """
    out: list[str] = []
    index = 0
    depth = 0
    quoted = False
    while index < len(source):
        pair = source[index:index + 2]
        char = source[index]
        if depth:
            if pair == "/-":
                depth += 1
                index += 2
            elif pair == "-/":
                depth -= 1
                index += 2
            else:
                out.append("\n" if char == "\n" else " ")
                index += 1
        elif quoted:
            out.append(char)
            index += 1
            if char == "\\" and index < len(source):
                out.append(source[index])
                index += 1
            elif char == '"':
                quoted = False
        elif pair == "/-":
            out.append(" ")
            depth = 1
            index += 2
        elif pair == "--":
            end = source.find("\n", index)
            if end == -1:
                break
            out.append("\n")
            index = end + 1
        else:
            out.append(char)
            quoted = char == '"'
            index += 1
    if depth:
        raise ValueError("Unterminated Lean block comment")
    return "".join(out)


def read_imports(path: Path) -> list[str]:
    imports: list[str] = []
    for line in strip_comments(path.read_text()).splitlines():
        line = line.strip()
        if not line or line in {"module", "prelude"}:
            continue
        match = IMPORT.fullmatch(line)
        if match:
            for name in match.group(1).split():
                if not MODULE_NAME.fullmatch(name):
                    raise ValueError(f"Unsupported import syntax in {path}: {line}")
                imports.append(name)
            continue
        # Lean imports belong to the file header, before declarations/options.
        break
    return imports


def source_graph() -> tuple[dict[str, Path], dict[str, list[str]]]:
    paths = sorted((ROOT / "Submission").rglob("*.lean"))
    paths.append(ROOT / "Submission.lean")
    sources = {
        ".".join(path.relative_to(ROOT).with_suffix("").parts): path
        for path in paths
    }
    dependencies: dict[str, list[str]] = {}
    for name, path in sources.items():
        imported = read_imports(path)
        missing = [dep for dep in imported if dep.startswith("Submission.") and dep not in sources]
        if missing:
            raise ValueError(f"Missing local import(s) in {name}: {missing}")
        dependencies[name] = sorted(dep for dep in imported if dep in sources)
    return sources, dependencies


def topological_order(dependencies: dict[str, list[str]], target: str) -> list[str]:
    if target not in dependencies:
        raise ValueError(f"No local Lean source for target {target}")
    active: set[str] = set()
    visited: set[str] = set()
    result: list[str] = []

    def visit(name: str) -> None:
        if name in visited:
            return
        if name in active:
            raise ValueError(f"Local import cycle at {name}")
        active.add(name)
        for dependency in dependencies[name]:
            visit(dependency)
        active.remove(name)
        visited.add(name)
        result.append(name)

    visit(target)
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--target", default="Submission")
    parser.add_argument("--log", default="verification/sequential-build.log")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    sources, dependencies = source_graph()
    order = topological_order(dependencies, args.target)
    position = {name: index for index, name in enumerate(order)}
    for name in order:
        if any(position[dep] >= position[name] for dep in dependencies[name]):
            raise ValueError(f"Invalid dependency order at {name}")
    if args.dry_run:
        print(json.dumps({"target": args.target, "local_source_count": len(sources),
                          "reachable_count": len(order), "order": order}, indent=2))
        return 0
    lake = shutil.which("lake")
    if lake is None:
        raise SystemExit("lake is not on PATH; install the pinned toolchain first")
    log_path = Path(args.log)
    if not log_path.is_absolute():
        log_path = ROOT / log_path
    log_path.parent.mkdir(parents=True, exist_ok=True)
    environment = dict(os.environ)
    environment["LEAN_NUM_THREADS"] = "1"
    started = time.monotonic()
    with log_path.open("a", buffering=1) as transcript:
        def emit(message: str) -> None:
            print(message, flush=True)
            transcript.write(message + "\n")

        emit(f"Sequential build started {datetime.now(timezone.utc).isoformat()}")
        emit(f"Root: {ROOT}")
        emit(f"Target: {args.target}; local dependency closure: {len(order)} modules")
        emit("LEAN_NUM_THREADS=1; ordinary Lake dependency/content hash validation is enabled")
        for index, module in enumerate(order, 1):
            command = [lake, "build", "+" + module]
            emit(f"[{index}/{len(order)}] {' '.join(command)}")
            tick = time.monotonic()
            # Exactly one Lake invocation is active. Its local imports have
            # already been checked in this run; Lake still revalidates them.
            with subprocess.Popen(command, cwd=ROOT, env=environment, text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                  bufsize=1) as process:
                assert process.stdout is not None
                for line in process.stdout:
                    sys.stdout.write(line)
                    sys.stdout.flush()
                    transcript.write(line)
                status = process.wait()
            emit(f"[{index}/{len(order)}] exit={status}; seconds={time.monotonic() - tick:.1f}")
            if status:
                emit(f"BUILD FAILED at {module}; full output is in {log_path}")
                return status if status > 0 else 128 - status
        emit(f"SEQUENTIAL BUILD PASSED in {time.monotonic() - started:.1f}s")
        emit("Next run python3 verify.py to check the exact theorem type and transitive axioms.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
