#!/usr/bin/env python3
"""Build and execute a consumer using only a relocated HEIR installation."""

import argparse
from pathlib import Path
import shutil
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('build', 'work', 'llvm-dir', 'mlir-dir', 'ortools-dir', 'cc', 'cxx'):
        parser.add_argument('--' + name, type=Path, required=True)
    args = parser.parse_args()
    args.work.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='installed-', dir=args.work) as tmp:
        root = Path(tmp)
        stage = root / 'stage'
        relocated = root / 'relocated'
        consumer = root / 'consumer'
        log = args.work / 'installed-consumer.log'
        with log.open('w') as output:
            def run(command, *, success=True):
                output.write(' '.join(map(str, command)) + '\n')
                output.flush()
                result = subprocess.run(list(map(str, command)), stdout=output,
                                        stderr=subprocess.STDOUT, timeout=120)
                assert (result.returncode == 0) == success, command
            run(['cmake', '--install', args.build, '--prefix', stage])
            shutil.move(stage, relocated)
            for path in relocated.rglob('*'):
                assert not path.is_symlink(), path
                if path.suffix in ('.cmake', '.h', '.inc'):
                    assert str(args.build.resolve()) not in path.read_text(), path
            run(['cmake', '-S', Path(__file__).parent / 'installed', '-B', consumer,
                 '-G', 'Ninja', '-DCMAKE_EXPORT_COMPILE_COMMANDS=ON',
                 f'-DZkcHeirArithmetic_DIR={relocated}/lib/cmake/ZkcHeirArithmetic',
                 f'-DLLVM_DIR={args.llvm_dir}', f'-DMLIR_DIR={args.mlir_dir}',
                 f'-Dortools_DIR={args.ortools_dir}',
                 f'-DCMAKE_PREFIX_PATH={args.ortools_dir.parents[2]}',
                 f'-DCMAKE_C_COMPILER={args.cc}', f'-DCMAKE_CXX_COMPILER={args.cxx}'])
            commands = (consumer / 'compile_commands.json').read_text()
            assert str(args.build.resolve() / 'generated') not in commands
            assert str(args.build.resolve() / 'include-shims') not in commands
            assert str(args.build.resolve().parent / 'source') not in commands
            run(['cmake', '--build', consumer, '-j2'])
            run([consumer / 'consumer'])
            for version in ('9.14.0', ''):
                control = root / ('wrong-version' if version else 'missing-version')
                control.mkdir()
                (control / 'CMakeLists.txt').write_text(f'''
cmake_minimum_required(VERSION 3.24)
project(IncompatibleSolver LANGUAGES C CXX)
add_library(ortools::ortools INTERFACE IMPORTED)
{'set(ORTOOLS_VERSION ' + version + ')' if version else ''}
find_package(ZkcHeirArithmetic 0.0.0 EXACT CONFIG QUIET)
if(ZkcHeirArithmetic_FOUND OR TARGET ZkcHeir::Admission OR
   NOT ZkcHeirArithmetic_NOT_FOUND_MESSAGE MATCHES "Loaded OR-Tools")
  message(FATAL_ERROR "incompatible preloaded solver was accepted or replaced")
endif()
''')
                run(['cmake', '-S', control, '-B', control / 'build',
                     f'-DZkcHeirArithmetic_DIR={relocated}/lib/cmake/ZkcHeirArithmetic',
                     f'-DLLVM_DIR={args.llvm_dir}', f'-DMLIR_DIR={args.mlir_dir}',
                     f'-DCMAKE_C_COMPILER={args.cc}', f'-DCMAKE_CXX_COMPILER={args.cxx}'])
    print('Relocated HEIR SDK consumer passed')


if __name__ == '__main__':
    main()
