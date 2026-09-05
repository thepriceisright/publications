#!/usr/bin/python3
"""Restricted bubblewrap adapter for Comparator's landrun command interface."""
from __future__ import annotations

import json
import os
from pathlib import Path
import sys


def main() -> None:
    args = sys.argv[1:]
    writable = []
    i = 0
    while i < len(args) and args[i] != "--":
        flag = args[i]
        if flag in ("--ro", "--rw", "--rox", "--rwx", "--env"):
            value = args[i + 1]
            if flag in ("--rw", "--rwx") and value != "/dev":
                writable.append(str(Path(value).resolve()))
            i += 2
        elif flag in ("--best-effort", "-ldd", "-add-exec"):
            i += 1
        else:
            raise SystemExit(f"Unsupported sandbox option: {flag}")
    if i == len(args):
        raise SystemExit("Missing sandbox command")
    project = Path.cwd().resolve()
    allowed_write = project / ".lake"
    if any(Path(p) != allowed_write for p in writable):
        raise SystemExit("Only the verification project's .lake may be written")
    roots = [Path(p).resolve() for p in json.loads(os.environ["ERDOS_PROOF_READ_ROOTS"])]
    command = ["/usr/bin/bwrap", "--unshare-all", "--die-with-parent", "--new-session",
               "--clearenv", "--proc", "/proc", "--dev", "/dev", "--tmpfs", "/tmp"]
    for p in ("/usr", "/bin", "/lib", "/lib64"):
        if Path(p).exists():
            command += ["--ro-bind", p, p]
    for path in [project, *roots]:
        command += ["--ro-bind", str(path), str(path)]
    for path in writable:
        command += ["--bind", path, path]
    for key in ("PATH", "LEAN_PATH", "LEAN_ABORT_ON_PANIC"):
        if key in os.environ:
            command += ["--setenv", key, os.environ[key]]
    child = args[i + 1:]
    if len(child) == 3 and child[:2] == ["lake", "build"]:
        module = child[2]
        if module not in ("Challenge", "Solution") or not writable:
            raise SystemExit("Only the two verification modules may be compiled")
        output = allowed_write / "build" / "lib" / "lean"
        output.mkdir(parents=True, exist_ok=True)
        child = ["lean", "-o", str(output / f"{module}.olean"), f"{module}.lean"]
    command += ["--setenv", "HOME", "/tmp", "--chdir", str(project), "--", *child]
    os.execv(command[0], command)


if __name__ == "__main__":
    main()
