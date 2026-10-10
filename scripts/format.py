#!/usr/bin/env python3
"""Check or format maintained C++ sources with the selected LLVM formatter."""
import argparse
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def sources():
    excluded = {"build", "target", ".cache", ".git"}
    return sorted(path for folder in (ROOT / "compiler", ROOT / "common/tests/consumer")
                  for path in folder.rglob("*")
                  if path.suffix in {".h", ".cpp"} and not excluded.intersection(path.relative_to(ROOT).parts))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="apply formatting to maintained sources")
    parser.add_argument("--tool", default="clang-format")
    args = parser.parse_args()
    tested = re.search(r'set\(ZKC_TESTED_LLVM_VERSION\s+"(\d+)',
                      (ROOT / "compiler/CMakeLists.txt").read_text())[1]
    version = subprocess.check_output([args.tool, "--version"], text=True)
    if not re.search(rf'clang-format version {tested}\.', version):
        parser.error(f"use clang-format {tested} from the compiler toolchain; found {version.strip()}")
    command = [args.tool, "-i"] if args.write else [args.tool, "--dry-run", "--Werror"]
    files = sources()
    if not files:
        parser.error("no maintained C++ sources found")
    subprocess.run([*command, *map(str, files)], check=True)
    print(f"{'Formatted' if args.write else 'Checked'} {len(files)} C++ files.")


if __name__ == "__main__":
    main()
