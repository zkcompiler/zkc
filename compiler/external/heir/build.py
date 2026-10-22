#!/usr/bin/env python3
"""Build the pinned HEIR arithmetic library from a verified source archive."""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tarfile

HERE = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', type=Path, required=True)
    parser.add_argument('--work', type=Path, required=True)
    parser.add_argument('--llvm-dir', type=Path, required=True)
    parser.add_argument('--mlir-dir', type=Path, required=True)
    parser.add_argument('--ortools-dir', type=Path, required=True)
    parser.add_argument('--mlir-tblgen', type=Path, required=True)
    parser.add_argument('--cc', required=True)
    parser.add_argument('--cxx', required=True)
    parser.add_argument('--jobs', type=int, default=2)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error('jobs must be positive')
    pins = json.loads((HERE / 'pins.json').read_text())
    if digest(args.archive) != pins['heir']['sha256']:
        parser.error('HEIR archive does not match pins.json')
    for patch in pins['patches']:
        if digest(HERE / patch['path']) != patch['sha256']:
            parser.error('HEIR patch does not match pins.json')
    work = args.work.resolve()
    if work == HERE or work in HERE.parents:
        parser.error('work must not contain the integration sources')
    work.mkdir(parents=True, exist_ok=True)
    source = work / 'source'
    # Never edit the upstream checkout or silently reuse a modified source tree.
    if source.exists():
        manifest = work / 'source-manifest.json'
        inputs = work / 'source-inputs.json'
        if not manifest.is_file() or not inputs.is_file():
            parser.error('existing source has no manifest; select a fresh work directory')
        if json.loads(inputs.read_text()) != pins:
            parser.error('prepared source uses different pins; select a fresh work directory')
        expected = json.loads(manifest.read_text())
        actual = {str(p.relative_to(source)): digest(p)
                  for p in sorted(source.rglob('*')) if p.is_file()}
        if expected != actual:
            parser.error('prepared source has changed; select a fresh work directory')
    else:
        with tarfile.open(args.archive) as archive:
            members = archive.getmembers()
            prefix = 'heir-' + pins['heir']['revision'] + '/'
            if any(not m.name.startswith(prefix) or m.issym() or m.islnk()
                   for m in members if m.name != prefix[:-1]):
                parser.error('unexpected archive member')
            archive.extractall(work / 'unpacked', filter='data')
        shutil.move(work / 'unpacked' / prefix, source)
        for patch in pins['patches']:
            subprocess.run(['patch', '--batch', '--fuzz=0', '-p1', '-i',
                            str(HERE / patch['path'])], cwd=source, check=True)
        manifest = {str(p.relative_to(source)): digest(p)
                    for p in sorted(source.rglob('*')) if p.is_file()}
        (work / 'source-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
        (work / 'source-inputs.json').write_text(json.dumps(pins, indent=2) + '\n')
    command = ['cmake', '-S', str(HERE), '-B', str(work / 'build'), '-G', 'Ninja',
               '-DCMAKE_BUILD_TYPE=Release', f'-DZKC_HEIR_SOURCE_DIR={source}',
               f'-DLLVM_DIR={args.llvm_dir.resolve()}',
               f'-DMLIR_DIR={args.mlir_dir.resolve()}',
               f'-Dortools_DIR={args.ortools_dir.resolve()}',
               f'-DCMAKE_PREFIX_PATH={args.ortools_dir.resolve().parents[2]}',
               f'-DMLIR_TABLEGEN_EXE={args.mlir_tblgen.resolve()}',
               f'-DCMAKE_C_COMPILER={args.cc}', f'-DCMAKE_CXX_COMPILER={args.cxx}']
    for cmd in (command, ['cmake', '--build', str(work / 'build'), '-j', str(args.jobs)]):
        subprocess.run(cmd, check=True)
    (work / 'build-inputs.json').write_text(json.dumps({
        'pins': pins, 'configure': command,
        'source_manifest_sha256': digest(work / 'source-manifest.json'),
    }, indent=2) + '\n')


if __name__ == '__main__':
    main()
