#!/usr/bin/env python3
"""Build standalone consumers through real Lake path dependencies."""

import argparse
import hashlib
import json
import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import support.evidence  # noqa: E402

import support.lake
from bridges.common.lean_render import source_package
from support.packages import NAMES, PACKAGES, add_selection, selection  # noqa: E402
import shutil
import subprocess


HERE = Path(__file__).resolve().parents[1]


def check(root, output, packages=None, lake="lake", requested_clients=None):
    lake = support.lake.resolve(lake)
    lake = str(Path(lake).absolute())
    output.mkdir(parents=True, exist_ok=False)
    environment = dict(os.environ)
    for key in ('LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LAKE_HOME'):
        environment.pop(key, None)
    results = {}
    selected_packages = set(PACKAGES if packages is None else packages)
    clients = []
    sources = sorted((root / "clients").glob("*.lean"))
    requested = set(requested_clients or (source.stem for source in sources))
    unknown = requested - {source.stem for source in sources}
    if unknown:
        raise ValueError(f"unknown standalone clients: {sorted(unknown)}")
    for source in sources:
        if source.stem not in requested:
            continue
        filename = source.name
        upstream = source_package((root / "clients" / filename).read_text(), root=root)
        owner = next(name for name, (directory, _) in PACKAGES.items() if directory.relative_to(HERE) == upstream.relative_to(root))
        if owner in selected_packages:
            clients.append((filename.removesuffix(".lean"), filename, upstream, NAMES[owner]))
    if not clients:
        raise ValueError("selected packages have no maintained standalone clients")
    for kind, filename, upstream, dependency in clients:
        client = output / kind
        client.mkdir()
        shutil.copy2(upstream / 'lean-toolchain', client / 'lean-toolchain')
        source = root / 'clients' / filename
        source_hash = hashlib.sha256(source.read_bytes()).hexdigest()
        compiled_source = client / 'Client.lean'
        shutil.copy2(source, compiled_source)
        (client / 'Audit.lean').write_text(
            'import Client\nimport Zkc.Tools.Program.DeclarationAudit\n\n'
            'run_cmd ZkcTools.DeclarationAudit.check [`Client]\n')
        (client / 'lakefile.toml').write_text(
            'name = "zkc_client"\ndefaultTargets = ["Client"]\n\n'
            '[[require]]\nname = ' + json.dumps(dependency) + '\n'
            'path = ' + json.dumps(str(upstream)) + '\n\n'
            '[[lean_lib]]\nname = "Client"\nroots = ["Client", "Audit"]\nallowNonModules = true\n')
        manifest = json.loads((upstream / 'lake-manifest.json').read_text())
        manifest['name'] = 'zkc_client'
        manifest['packages'].append({
            'type': 'path', 'name': dependency, 'dir': str(upstream),
            'inherited': False, 'manifestFile': 'lake-manifest.json',
            'configFile': 'lakefile.toml',
        })
        packages = client / '.lake/packages'
        packages.mkdir(parents=True)
        for package in manifest['packages']:
            if package['type'] == 'path':
                package['dir'] = str((upstream / package['dir']).resolve())
                continue
            name = package['name'].removeprefix('«').removesuffix('»')
            (packages / name).symlink_to((upstream / '.lake/packages' / name).resolve())
        (client / 'lake-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
        lake_version = subprocess.check_output([lake, '--version'], cwd=client, env=environment, text=True).strip()
        lean_version = subprocess.check_output([lake, 'env', 'lean', '--version'],
                                               cwd=client, env=environment, text=True).strip()
        log_path = output / f'{kind}.log'
        with log_path.open('w') as log:
            run = subprocess.run([lake, '--no-cache', 'build'], cwd=client,
                                 env=environment, stdout=log, stderr=subprocess.STDOUT)
        text = log_path.read_text()
        compiled_hash = hashlib.sha256(compiled_source.read_bytes()).hexdigest()
        drift = compiled_hash != source_hash or hashlib.sha256(source.read_bytes()).hexdigest() != source_hash
        passed = run.returncode == 0 and 'DEPENDENCY-AUDIT-PASS' in text and not drift
        results[kind] = {
            'status': 'pass' if passed else 'fail', 'exit_code': run.returncode,
            'lake_executable': lake, 'lake_version': lake_version, 'lean_version': lean_version,
            'toolchain': (client / 'lean-toolchain').read_text().strip(),
            'client_sha256': compiled_hash, 'source_drift': drift,
            'log_sha256': hashlib.sha256(log_path.read_bytes()).hexdigest(),
        }
        if not passed:
            break
    record = {'format': 'zkc.library-clients.v0', 'clients': results,
              'inherited_lean_paths': False,
              'status': 'pass' if all(x['status'] == 'pass' for x in results.values()) else 'fail'}
    (output / 'result.json').write_text(json.dumps(record, indent=2) + '\n')
    return record


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=support.evidence.records("clients", ""))
    add_selection(parser)
    parser.add_argument('--lake', default='lake')
    parser.add_argument('--client', action='append', help='check only named clients; repeat (default: all)')
    args = parser.parse_args()
    record = check(HERE, args.output.resolve(), selection(args), args.lake, args.client)
    print(json.dumps(record, indent=2))
    raise SystemExit(0 if record['status'] == 'pass' else 1)
