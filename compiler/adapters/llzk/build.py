#!/usr/bin/env python3
"""Build the isolated LLZK adapter from a verified archive and explicit toolchain."""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tarfile

HERE = Path(__file__).resolve().parent
TARGETS = ['LLZKDialectRegistration', 'LLZKTransforms',
           'R1CSDialectRegistration', 'R1CSTransforms', 'R1CSTarget']


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def manifest(source):
    result = {}
    for path in sorted(source.rglob('*')):
        if path.is_symlink():
            raise ValueError('prepared source contains a symbolic link')
        if path.is_file():
            result[str(path.relative_to(source))] = digest(path)
    return result


def prepare(archive, work, pins):
    pin = pins['llzk-current']
    if digest(archive) != pin['sha256']:
        raise ValueError('LLZK archive does not match pins.json')
    for patch in pins['patches']:
        if digest(HERE / patch['path']) != patch['sha256']:
            raise ValueError('LLZK patch does not match pins.json')
    source = work / 'source'
    inputs = {'llzk': pin, 'llvm': pins['llvm'], 'patches': pins['patches']}
    inputs_file, manifest_file = work / 'source-inputs.json', work / 'source-manifest.json'
    if source.exists():
        if not inputs_file.is_file() or not manifest_file.is_file():
            raise ValueError('existing source has no manifest; choose a fresh work directory')
        if inputs != json.loads(inputs_file.read_text()):
            raise ValueError('prepared source uses different pins; choose a fresh work directory')
        if manifest(source) != json.loads(manifest_file.read_text()):
            raise ValueError('prepared source has changed; choose a fresh work directory')
        return source
    prefix = 'llzk-lib-' + pin['revision'] + '/'
    with tarfile.open(archive) as package:
        for member in package.getmembers():
            if ((member.name != prefix[:-1] and not member.name.startswith(prefix))
                    or member.issym() or member.islnk()):
                raise ValueError('unexpected LLZK archive member')
        package.extractall(work / 'unpacked', filter='data')
    shutil.move(work / 'unpacked' / prefix, source)
    for patch in pins['patches']:
        subprocess.run(['patch', '--batch', '--fuzz=0', '-p1', '-i',
                        str(HERE / patch['path'])], cwd=source, check=True)
    inputs_file.write_text(json.dumps(inputs, indent=2) + '\n')
    manifest_file.write_text(json.dumps(manifest(source), indent=2) + '\n')
    return source


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', type=Path, required=True)
    parser.add_argument('--work', type=Path, required=True)
    for name in ['llvm-dir', 'mlir-dir', 'clang-dir', 'mlir-tblgen']:
        parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--cc', required=True)
    parser.add_argument('--cxx', required=True)
    parser.add_argument('--native', type=Path, help='Enable the independent native relation corpus')
    parser.add_argument('--cmake-arg', action='append', default=[],
                        help='Additional explicit build input, recorded in build-inputs.json')
    parser.add_argument('--jobs', type=int, default=2)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error('jobs must be positive')
    work = args.work.resolve()
    if work == HERE or work in HERE.parents:
        parser.error('work must not contain the adapter sources')
    work.mkdir(parents=True, exist_ok=True)
    pins = json.loads((HERE / 'pins.json').read_text())
    try:
        source = prepare(args.archive, work, pins)
    except (OSError, ValueError) as error:
        parser.error(str(error))
    upstream, adapter = work / 'upstream', work / 'adapter'
    common = ['-G', 'Ninja', '-DCMAKE_BUILD_TYPE=Release', *args.cmake_arg,
              f'-DCMAKE_C_COMPILER={args.cc}', f'-DCMAKE_CXX_COMPILER={args.cxx}',
              f'-DLLVM_DIR={args.llvm_dir.resolve()}',
              f'-DMLIR_DIR={args.mlir_dir.resolve()}']
    configure_upstream = ['cmake', '-S', str(source), '-B', str(upstream), *common,
        f'-DClang_DIR={args.clang_dir.resolve()}',
        f'-DMLIR_TABLEGEN_EXE={args.mlir_tblgen.resolve()}',
        f"-DLLZK_VERSION_OVERRIDE={pins['llzk-current']['version']}",
        '-DLLZK_WITH_PCL=OFF', '-DLLZK_ENABLE_BINDINGS_PYTHON=OFF',
        '-DLLZK_TBLGEN_USE_LIBCLANGCPP=ON', '-DBUILD_TESTING=OFF']
    configure_adapter = ['cmake', '-S', str(HERE), '-B', str(adapter), *common,
        f'-DLLZK_DIR={upstream}', '-DBUILD_TESTING=ON',
        f"-DZKC_LLZK_REVISION={pins['llzk-current']['revision']}"]
    configure_adapter.append(
        f'-DZKC_NATIVE_COMPILER={args.native.resolve() if args.native else ""}')
    commands = [configure_upstream,
        ['cmake', '--build', str(upstream), '-j', str(args.jobs), '--target', *TARGETS],
        configure_adapter, ['cmake', '--build', str(adapter), '-j', str(args.jobs)],
        ['ctest', '--test-dir', str(adapter), '--output-on-failure']]
    # Record inputs even if compilation or validation fails.
    (work / 'build-inputs.json').write_text(json.dumps({
        'pins': pins, 'commands': commands,
        'source_manifest_sha256': digest(work / 'source-manifest.json'),
    }, indent=2) + '\n')
    for command in commands:
        subprocess.run(command, check=True)
    (work / 'build-results.json').write_text(json.dumps({
        'binary_sha256': digest(adapter / 'zkc-llzk'),
        'adapter_sources': {str(p.relative_to(HERE)): digest(p)
                            for p in sorted(HERE.rglob('*')) if p.is_file()},
        'upstream_libraries': {str(p.relative_to(upstream)): digest(p)
                               for p in sorted(upstream.rglob('*.a'))},
    }, indent=2) + '\n')


if __name__ == '__main__':
    main()
