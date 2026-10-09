#!/usr/bin/env python3
"""Run the Plonky3 adapter fixture driver in a resource-limited process.

Capturing an AIR runs its ``Air::eval``, which is arbitrary host code. The
driver bounds artifact sizes in-process; this wrapper additionally bounds the
whole process's address space, CPU time and wall-clock time.

    regenerate.py --binary PATH write NEW_DIRECTORY
    regenerate.py --binary PATH check FIXTURE_DIRECTORY
"""

import argparse
import resource
import subprocess
import sys
from pathlib import Path


def limits(address_space: int, cpu_seconds: int):
    def apply():
        resource.setrlimit(resource.RLIMIT_AS, (address_space, address_space))
        resource.setrlimit(resource.RLIMIT_CPU, (cpu_seconds, cpu_seconds))

    return apply


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--binary", type=Path, required=True, help="zkc-plonky3-air-fixtures executable")
    parser.add_argument("--address-space-mib", type=int, default=2048)
    parser.add_argument("--cpu-seconds", type=int, default=60)
    parser.add_argument("--timeout-seconds", type=int, default=120)
    parser.add_argument("command", choices=["write", "check"])
    parser.add_argument("directory", type=Path)
    args = parser.parse_args()
    if not args.binary.is_file():
        parser.error(f"{args.binary} is not a file")
    if args.command == "write" and args.directory.exists():
        parser.error(f"{args.directory} already exists")
    try:
        completed = subprocess.run(
            [str(args.binary), args.command, str(args.directory)],
            preexec_fn=limits(args.address_space_mib << 20, args.cpu_seconds),
            timeout=args.timeout_seconds,
            check=False,
        )
    except subprocess.TimeoutExpired:
        print(f"fixture driver exceeded {args.timeout_seconds} seconds", file=sys.stderr)
        return 1
    if completed.returncode < 0:
        print(f"fixture driver stopped by signal {-completed.returncode}", file=sys.stderr)
        return 1
    return completed.returncode


if __name__ == "__main__":
    sys.exit(main())
