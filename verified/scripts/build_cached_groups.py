#!/usr/bin/env python3
"""Build local Lean modules sequentially, validating cached groups with Lake.

An existing .olean is only a grouping hint. A group is accepted exclusively
after normal `lake --no-build build +A +B ...` succeeds. Lake exit code 3 means
a rebuild is needed: split the group in topological order, then normally build
each stale singleton. Any other failed command stops this script.

This does not edit build traces, use --old, or treat artifact existence as proof
of freshness. It uses the same import parser as build_sequential.py. All actual
local-module builds remain sequential with LEAN_NUM_THREADS=1. The final target
receives an additional normal Lake --no-build validation before success.

Author: Joshua Wharton <joshua@qfex.com>, QFEX, 2026.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import time
from typing import TextIO

from build_sequential import ROOT, source_graph, topological_order


# Lake 4.33.1, Lake/Build/Run.lean: noBuildCode. Other failures are fatal.
NEEDS_BUILD = 3


class BuildFailure(Exception):
    def __init__(self, status: int, description: str) -> None:
        super().__init__(description)
        self.status = status if status > 0 else 128 - status


def artifact_present(module: str) -> bool:
    """A scheduling hint only; Lake must still validate every accepted target."""
    return (ROOT / ".lake/build/lib/lean" / Path(*module.split("."))).with_suffix(".olean").is_file()


def scheduling_groups(order: list[str], limit: int) -> list[tuple[int, list[str], bool]]:
    groups: list[tuple[int, list[str], bool]] = []
    index = 0
    while index < len(order):
        present = artifact_present(order[index])
        end = index + 1
        if present:
            while end < len(order) and end - index < limit and artifact_present(order[end]):
                end += 1
        groups.append((index, order[index:end], present))
        index = end
    return groups


class Builder:
    def __init__(self, lake: str, transcript: TextIO, total: int) -> None:
        self.lake = lake
        self.transcript = transcript
        self.total = total
        self.environment = dict(os.environ)
        self.environment["LEAN_NUM_THREADS"] = "1"
        self.accepted = 0
        self.build_calls = 0
        self.validation_calls = 0

    def emit(self, message: str) -> None:
        print(message, flush=True)
        self.transcript.write(message + "\n")

    def run(self, command: list[str], description: str) -> int:
        self.emit(description)
        # Keep the full argv in the log without printing very long cached groups.
        self.transcript.write("COMMAND " + shlex.join(command) + "\n")
        started = time.monotonic()
        with subprocess.Popen(command, cwd=ROOT, env=self.environment, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                              bufsize=1) as process:
            if process.stdout is None:
                raise RuntimeError("The requested subprocess output pipe is missing")
            for line in process.stdout:
                sys.stdout.write(line)
                sys.stdout.flush()
                self.transcript.write(line)
            status = process.wait()
        self.emit(f"Command exit={status}; seconds={time.monotonic() - started:.1f}")
        return status

    def build_one(self, module: str, position: int) -> None:
        self.build_calls += 1
        status = self.run([self.lake, "build", "+" + module],
                          f"[{position + 1}/{self.total}] Normal build: {module}")
        if status != 0:
            raise BuildFailure(status, f"Normal build failed at {module}")
        self.accepted += 1

    def validate_group(self, modules: list[str], position: int) -> None:
        self.validation_calls += 1
        count = len(modules)
        description = (f"[{position + 1}-{position + count}/{self.total}] "
                       f"Lake validation of {count} cached candidate(s): "
                       f"{modules[0]} ... {modules[-1]}")
        status = self.run([self.lake, "--no-build", "build", *("+" + m for m in modules)],
                          description)
        if status == 0:
            self.accepted += count
            self.emit(f"Accepted {count} module(s) after successful Lake validation")
            return
        if status != NEEDS_BUILD:
            raise BuildFailure(status, "Unexpected failure during cached-group validation")
        if count == 1:
            self.build_one(modules[0], position)
            return
        middle = count // 2
        self.emit("Lake requires a rebuild; validating the two halves in topological order")
        self.validate_group(modules[:middle], position)
        self.validate_group(modules[middle:], position + middle)

    def validate_final_target(self, target: str) -> None:
        self.validation_calls += 1
        status = self.run([self.lake, "--no-build", "build", "+" + target],
                          f"Final normal Lake validation of the complete target: {target}")
        if status != 0:
            raise BuildFailure(status, "Final target is not validated; refusing to report success")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--target", default="Submission")
    parser.add_argument("--log", default="verification/cached-group-build.log")
    parser.add_argument("--group-size", type=int, default=128)
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    if args.group_size < 1:
        parser.error("--group-size must be positive")
    sources, dependencies = source_graph()
    order = topological_order(dependencies, args.target)
    positions = {name: index for index, name in enumerate(order)}
    for name in order:
        if any(positions[dep] >= positions[name] for dep in dependencies[name]):
            raise ValueError(f"Invalid dependency order at {name}")
    groups = scheduling_groups(order, args.group_size)
    if args.dry_run:
        print(json.dumps({
            "target": args.target,
            "local_source_count": len(sources),
            "reachable_count": len(order),
            "group_size": args.group_size,
            "groups": [
                {"first_position": position + 1,
                 "mode": "lake_no_build_validation" if present else "normal_singleton_build",
                 "targets": modules}
                for position, modules, present in groups
            ],
        }, indent=2))
        return 0
    lake = shutil.which("lake")
    if lake is None:
        raise SystemExit("lake is not on PATH; install the pinned toolchain first")
    log_path = Path(args.log)
    if not log_path.is_absolute():
        log_path = ROOT / log_path
    log_path.parent.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    with log_path.open("a", buffering=1) as transcript:
        builder = Builder(lake, transcript, len(order))
        builder.emit(f"Cached-group build started {datetime.now(timezone.utc).isoformat()}")
        builder.emit(f"Root: {ROOT}")
        builder.emit(f"Target: {args.target}; local dependency closure: {len(order)} modules")
        builder.emit("LEAN_NUM_THREADS=1; standard Lake trace validation; no --old")
        try:
            for position, modules, present in groups:
                if present:
                    builder.validate_group(modules, position)
                else:
                    builder.build_one(modules[0], position)
            if builder.accepted != len(order):
                raise RuntimeError("Internal error: not every module received successful Lake validation")
            builder.validate_final_target(args.target)
        except BuildFailure as failure:
            builder.emit(f"BUILD FAILED: {failure}; full output is in {log_path}")
            return failure.status
        builder.emit(f"CACHED-GROUP BUILD PASSED in {time.monotonic() - started:.1f}s")
        builder.emit(f"Normal single-module builds: {builder.build_calls}; "
                     f"Lake no-build validations: {builder.validation_calls}")
        builder.emit("Next run python3 verify.py to check the exact theorem type and transitive axioms.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
