#!/usr/bin/env python3
"""Provide a stale-safe handoff from zkc-seal's directory to one artifact."""

import argparse
import shutil
from pathlib import Path


def require_artifact_directory(path: Path) -> None:
    if not path.name.endswith(".artifacts"):
        raise SystemExit("artifact directory must end in '.artifacts'")


def reset(path: Path) -> None:
    require_artifact_directory(path)
    if path.is_symlink() or (path.exists() and not path.is_dir()):
        raise SystemExit("refusing to reset a non-directory artifact path")
    if path.exists():
        shutil.rmtree(path)
    path.mkdir(parents=True)


def stage(directory: Path, destination: Path) -> None:
    require_artifact_directory(directory)
    artifacts = sorted(directory.glob("*.mlirbc"))
    if len(artifacts) != 1:
        raise SystemExit(f"expected exactly one artifact, found {len(artifacts)}")
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(artifacts[0], destination)


def main() -> None:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    reset_parser = subparsers.add_parser("reset")
    reset_parser.add_argument("directory", type=Path)
    stage_parser = subparsers.add_parser("stage")
    stage_parser.add_argument("directory", type=Path)
    stage_parser.add_argument("destination", type=Path)
    args = parser.parse_args()
    if args.command == "reset":
        reset(args.directory)
    else:
        stage(args.directory, args.destination)


if __name__ == "__main__":
    main()
