#!/usr/bin/env python3
"""Build standalone consumers through real Lake path dependencies."""

import argparse
import hashlib
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import support.evidence  # noqa: E402

import support.lake
import shutil
import subprocess


HERE = Path(__file__).resolve().parents[1]


def check(root, output, with_arklib=False, lake="lake"):
    lake = support.lake.resolve(lake)
    lake = str(Path(lake).absolute())
    output.mkdir(parents=True, exist_ok=False)
    results = {}
    for kind in (['main', 'arklib'] if with_arklib else ['main']):
        upstream = root if kind == 'main' else root / 'integrations/arklib'
        dependency = 'zkc' if kind == 'main' else 'zkc_arklib'
        client = output / kind
        client.mkdir()
        shutil.copy2(root / 'lean-toolchain', client / 'lean-toolchain')
        source = root / 'clients' / ('Main.lean' if kind == 'main' else 'ArkLib.lean')
        source_hash = hashlib.sha256(source.read_bytes()).hexdigest()
        compiled_source = client / 'Client.lean'
        shutil.copy2(source, compiled_source)
        (client / 'Audit.lean').write_text(
            'import Client\nimport Tools.DeclarationAudit\n\n'
            'run_cmd Tools.DeclarationAudit.check [`Client]\n')
        (client / 'lakefile.toml').write_text(
            'name = "zkc_client"\ndefaultTargets = ["Client"]\n\n'
            '[[require]]\nname = ' + json.dumps(dependency) + '\n'
            'path = ' + json.dumps(str(upstream)) + '\n\n'
            '[[lean_lib]]\nname = "Client"\nroots = ["Client", "Audit"]\n')
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
                if package['name'] == 'zkc':
                    package['dir'] = str(root)
                continue
            name = package['name'].removeprefix('«').removesuffix('»')
            (packages / name).symlink_to((upstream / '.lake/packages' / name).resolve())
        (client / 'lake-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
        lake_version = subprocess.check_output([lake, '--version'], cwd=client, text=True).strip()
        lean_version = subprocess.check_output([lake, 'env', 'lean', '--version'],
                                               cwd=client, text=True).strip()
        log_path = output / f'{kind}.log'
        with log_path.open('w') as log:
            run = subprocess.run([lake, '--no-cache', 'build'], cwd=client,
                                 stdout=log, stderr=subprocess.STDOUT)
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
    record = {'format': 'zkc.library-clients.v2', 'clients': results,
              'status': 'pass' if all(x['status'] == 'pass' for x in results.values()) else 'fail'}
    (output / 'result.json').write_text(json.dumps(record, indent=2) + '\n')
    return record


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=support.evidence.records("clients", ""))
    parser.add_argument('--with-arklib', action='store_true')
    parser.add_argument('--lake', default='lake')
    args = parser.parse_args()
    record = check(HERE, args.output.resolve(), args.with_arklib, args.lake)
    print(json.dumps(record, indent=2))
    raise SystemExit(0 if record['status'] == 'pass' else 1)
