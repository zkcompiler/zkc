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
            def run(command):
                output.write(' '.join(map(str, command)) + '\n')
                output.flush()
                subprocess.run(list(map(str, command)), stdout=output,
                               stderr=subprocess.STDOUT, check=True, timeout=120)
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
    print('Relocated HEIR SDK consumer passed')


if __name__ == '__main__':
    main()
