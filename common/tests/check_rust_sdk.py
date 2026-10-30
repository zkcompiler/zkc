#!/usr/bin/env python3
"""Prepare packages separately; build staged Rust SDK sources and execute tool-free."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[2]
CRATES = ('zkc', 'zkc-format', 'zkc-catalog', 'zkc-runtime', 'zkc-cpu', 'zkc-kernels', 'zkc-test-support')
SOURCE = '''module application;
entry fn Twice(値:index) { return 値 + 2; }
entry fn Checked(value:index,valid:bool){require valid;return value+1;}
protocol Echo roles(P,V)(value:bool@P)->(received:bool@V){
  let received=send P->V(value); return received;
}
protocol Equality roles(P,V)(expected:bool@(P,V),candidate:bool@P)->(accepted:bool@V){
  let received=send P->V(candidate); let accepted@V=received==expected; return accepted;
}
proof Core = Equality {
  prover P; verifier V; public{expected}; accept accepted; construction authored;
}
entry fn Withhold(public:Core::Public,witness:Core::Witness,complete:bool){
  let produced=Core::prove(public,witness);require complete;return produced.proof;
}
'''


def run(command, *, cwd, env=None):
    result = subprocess.run([str(s) for s in command], cwd=cwd, env=env,
                            text=True, capture_output=True, check=False)
    if result.returncode:
        raise RuntimeError(f'{command}\n{result.stdout}\n{result.stderr}')
    return result.stdout


def prepare(output, cli, compiler):
    output.mkdir(parents=True)
    source = output / '数学.zkc'
    source.write_text(SOURCE)
    for name, entry in [('numerical', 'Twice'), ('joint', 'Echo'), ('proof', 'Core'),
                        ('checked', 'Checked'), ('withhold', 'Withhold')]:
        package = output / f'{name}.zkpkg'
        result = json.loads(run([cli, '--json', 'compile', f'application::{entry}',
                                 f'--module=application={source}', f'--compiler={compiler}',
                                 f'--output={package}'], cwd=output))
        assert result['status'] == 'compiled', result
        result = json.loads(run([cli, '--json', 'bindings', f'--package={package}',
                                 f'--sha256={result["package_sha256"]}',
                                 f'--output={output / (name + ".rs")}'], cwd=output))
        assert result['status'] == 'generated', result


def stage(output, sdk_source, prepared):
    output.mkdir(parents=True)
    shutil.copyfile(sdk_source / 'rust-toolchain.toml', output / 'rust-toolchain.toml')
    if (sdk_source / '.cargo/config.toml').is_file():
        (output / '.cargo').mkdir()
        shutil.copyfile(sdk_source / '.cargo/config.toml', output / '.cargo/config.toml')
    staged = output / 'sdk'
    staged.mkdir()
    for name in CRATES:
        shutil.copytree(sdk_source / 'crates' / name, staged / 'crates' / name)
    shutil.copytree(sdk_source / 'common/unicode', staged / 'common/unicode')
    (staged / 'common/catalog').mkdir()
    shutil.copyfile(sdk_source / 'common/catalog/declarations.json',
                    staged / 'common/catalog/declarations.json')
    for name in ('Cargo.lock', 'rust-toolchain.toml'):
        shutil.copyfile(sdk_source / name, staged / name)
    # Preserve owning manifests and exact pins; select only the installed SDK closure.
    manifest = (sdk_source / 'Cargo.toml').read_text()
    start = manifest.index('members = [')
    end = manifest.index('resolver =', start)
    manifest = (manifest[:start] + 'members = ' + json.dumps([f'crates/{n}' for n in CRATES])
                + '\ndefault-members = ["crates/zkc"]\n' + manifest[end:])
    (staged / 'Cargo.toml').write_text(manifest)
    consumer = output / 'consumer'
    consumer.mkdir()
    for path in prepared.iterdir():
        if path.suffix in ('.rs', '.zkpkg'):
            shutil.copyfile(path, consumer / path.name)
    shutil.copyfile(sdk_source / 'common/tests/consumer/rust/main.rs', consumer / 'main.rs')
    shutil.copyfile(sdk_source / 'Cargo.lock', consumer / 'Cargo.lock')
    (consumer / 'Cargo.toml').write_text('''[package]
name = "installed-rust-consumer"
version = "0.0.0"
edition = "2024"
[workspace]
[dependencies]
zkc = { path = "../sdk/crates/zkc", default-features = false, features = ["cpu"] }
[[bin]]
name = "installed-rust-consumer"
path = "main.rs"
''')
    portable = output / 'portable'
    portable.mkdir()
    shutil.copyfile(sdk_source / 'common/tests/consumer/rust/portable.rs', portable / 'main.rs')
    packages = []
    for path in sorted(prepared.glob('*.zkpkg')):
        shutil.copyfile(path, portable / path.name)
        packages.append(f'({json.dumps(path.stem)}, include_bytes!({json.dumps(path.name)}), '
                        f'&{list(hashlib.sha256(path.read_bytes()).digest())}),')
    (portable / 'pins.rs').write_text(
        'const PACKAGES: &[(&str, &[u8], &[u8; 32])] = &[\n' + '\n'.join(packages) + '\n];\n')
    (portable / 'Cargo.toml').write_text('''[package]
name = "portable-rust-consumer"
version = "0.0.0"
edition = "2024"
[workspace]
[dependencies]
zkc = { path = "../sdk/crates/zkc", default-features = false }
[features]
files = ["zkc/files"]
project = ["zkc/project", "files"]
[[bin]]
name = "portable-rust-consumer"
path = "main.rs"
''')
    return consumer


def normal_build_graph(metadata):
    """Reach only active normal/build edges from this detached application."""
    nodes = {node['id']: node for node in metadata['resolve']['nodes']}
    reached, pending = set(), [metadata['resolve']['root']]
    while pending:
        package = pending.pop()
        if package in reached:
            continue
        reached.add(package)
        for dependency in nodes[package]['deps']:
            if any(kind['kind'] in (None, 'build') for kind in dependency['dep_kinds']):
                pending.append(dependency['pkg'])
    return sorted(({'name': package['name'], 'version': package['version'],
                    'features': nodes[package['id']]['features']}
                   for package in metadata['packages'] if package['id'] in reached),
                  key=lambda package: (package['name'], package['version']))


def check_portable(output, target, env, prepared, compiler):
    consumer = output / 'portable'
    cargo = ['cargo', '--offline']
    runtime_env = dict(os.environ, PATH='', ZKC_COMPILER_BIN='/unavailable',
                       ZKC_NATIVE_BIN='/unavailable', ZKC_COMPILER='/unavailable')
    runtime_env.pop('ZKC_PORTABLE_COMPILER', None)
    receipts = []
    for features in ([], ['files'], ['project']):
        flags = ['--no-default-features']
        if features:
            flags += ['--features', ','.join(features)]
        metadata = json.loads(run([*cargo, 'metadata', '--format-version=1', *flags],
                                  cwd=consumer, env=env))
        graph = normal_build_graph(metadata)
        forbidden = [package['name'] for package in graph
                     if package['name'] in ('zkc-runtime', 'zkc-cpu', 'zkc-kernels', 'rand')
                     or package['name'].startswith(('ark', 'plonky', 'p3-'))]
        assert not forbidden, forbidden
        assert not any('cpu' in package['features'] for package in graph
                       if package['name'] == 'zkc'), graph
        run([*cargo, 'build', '--target-dir', target, '--jobs', '2', *flags], cwd=consumer, env=env)
        result = run([target / 'debug/portable-rust-consumer'], cwd=consumer, env=runtime_env)
        if features == ['project'] and compiler:
            project_env = dict(os.environ, ZKC_PORTABLE_COMPILER=str(compiler),
                               ZKC_PORTABLE_SOURCE=str(prepared / '数学.zkc'))
            result += run([target / 'debug/portable-rust-consumer'], cwd=consumer, env=project_env)
        receipts.append({'features': features, 'normal_build_graph': graph, 'result': result})
    (output / 'portable-results.json').write_text(json.dumps(receipts, indent=2) + '\n')


def check(output, sdk_source, prepared, compiler=None):
    consumer = stage(output, sdk_source, prepared)
    target = Path(os.environ.get('CARGO_TARGET_DIR', output / 'consumer-target')).resolve()
    env = dict(os.environ, CARGO_BUILD_JOBS='2', CARGO_INCREMENTAL='0',
               CARGO_PROFILE_DEV_DEBUG='0', CARGO_PROFILE_TEST_DEBUG='0')
    check_portable(output, target, env, prepared, compiler)
    cargo = ['cargo', '--offline']
    metadata = json.loads(run([*cargo, 'metadata', '--format-version=1'], cwd=consumer, env=env))
    graph = normal_build_graph(metadata)
    for package in graph:
        if package['name'] in ('zkc', 'zkc-cpu', 'zkc-runtime', 'zkc-kernels'):
            assert not {'test-utils', 'execution-counts'} & set(package['features']), package
    assert {'zkc-runtime', 'zkc-cpu', 'zkc-kernels'} <= {package['name'] for package in graph}
    (output / 'cpu-graph.json').write_text(json.dumps(graph, indent=2) + '\n')
    run([*cargo, 'build', '--target-dir', target, '--jobs', '2'], cwd=consumer, env=env)
    execution = output / 'execution'
    execution.mkdir()
    binary = execution / 'installed-rust-consumer'
    shutil.copyfile(target / 'debug/installed-rust-consumer', binary)
    binary.chmod(0o700)
    runtime_env = dict(os.environ, PATH='', ZKC_COMPILER_BIN='/unavailable',
                       ZKC_NATIVE_BIN='/unavailable', ZKC_COMPILER='/unavailable')
    result = run([binary], cwd=execution, env=runtime_env)
    (output / 'result.txt').write_text(result)
    print(result, end='')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    phases = parser.add_subparsers(dest='phase', required=True)
    prep = phases.add_parser('prepare')
    prep.add_argument('--cli', type=Path, required=True)
    prep.add_argument('--compiler', type=Path, required=True)
    prep.add_argument('--output', type=Path, required=True)
    verify = phases.add_parser('check')
    verify.add_argument('--compiler', type=Path)
    verify.add_argument('--sdk-source', type=Path, default=ROOT)
    verify.add_argument('--prepared', type=Path, required=True)
    verify.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.phase == 'prepare':
        prepare(args.output.resolve(), args.cli.resolve(), args.compiler.resolve())
    else:
        check(args.output.resolve(), args.sdk_source.resolve(), args.prepared.resolve(),
              args.compiler.resolve() if args.compiler else None)


if __name__ == '__main__':
    main()
