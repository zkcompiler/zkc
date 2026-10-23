#!/usr/bin/env python3
"""Install the public HEIR header closure with portable LLVM include spellings."""

import argparse
from pathlib import Path
import re

# Public dialect and pass headers; implementation-only sources are not an SDK.
ROOTS = [
    f'lib/Dialect/{dialect}/IR/{dialect}{kind}.h'
    for dialect in ('Polynomial', 'ModArith', 'RNS')
    for kind in ('Dialect', 'Types', 'Attributes', 'Ops')
]
INCLUDE = re.compile(r'^\s*#\s*include\s*"([^"\n]+)"', re.MULTILINE)
PREFIX = re.compile(r'(#\s*include\s*")((?:llvm|mlir)/)include/')


def install(source, generated, output):
    pending = list(ROOTS)
    visited = set()
    while pending:
        relative = pending.pop()
        if relative in visited:
            continue
        if not relative.startswith('lib/') or '..' in Path(relative).parts:
            raise ValueError(f'invalid HEIR header path: {relative}')
        visited.add(relative)
        path = source / relative
        if not path.is_file():
            path = generated / relative
        if not path.is_file():
            raise ValueError(f'missing public HEIR header dependency: {relative}')
        text = path.read_text()
        pending.extend(item for item in INCLUDE.findall(text) if item.startswith('lib/'))
        # Only include spellings change. Definitions remain the pinned upstream
        # source/generated text. No absolute paths or symlinks escape the build.
        text = PREFIX.sub(r'\1', text)
        destination = output / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(text)
    return sorted(visited)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('source', 'generated', 'output'):
        parser.add_argument('--' + name, type=Path, required=True)
    args = parser.parse_args()
    installed = install(args.source, args.generated, args.output)
    print(f'Installed {len(installed)} public HEIR headers')


if __name__ == '__main__':
    main()
