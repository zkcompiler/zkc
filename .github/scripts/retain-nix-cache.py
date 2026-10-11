#!/usr/bin/env python3
"""Keep the successful build graph alive until the CI store snapshot is saved."""

import os
from pathlib import Path
import subprocess
import sys


def main():
    directory = os.environ.get("ZKC_NIX_CACHE_ROOTS")
    if not directory:
        return
    roots = Path(directory)
    roots.mkdir(parents=True, exist_ok=True)
    graph = subprocess.check_output(
        ["nix-store", "--query", "--requisites", "--include-outputs", *sys.argv[1:]],
        text=True,
    ).splitlines()
    # Include compiled build-time artifacts (not just runtime closures). Realise
    # only existing non-derivation paths, so retention cannot start new builds.
    paths = sorted({path for path in graph if not path.endswith(".drv")})
    if paths:
        subprocess.run(
            ["nix-store", "--realise", "--max-jobs", "0", "--builders", "",
             "--add-root", str(roots / "build"), "--indirect", *paths],
            check=True, stdout=subprocess.DEVNULL,
        )
    print(f"Retained {len(paths)} paths from the successful Nix build graph.")


if __name__ == "__main__":
    main()
