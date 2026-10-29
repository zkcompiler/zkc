#!/usr/bin/env python3
"""Regenerate actual Structured fixtures and Lean-owned scalar admission/views.

This fixture catalogue selects source subjects, not semantic implementations.
The native exporter and generic Lean printer own the generated representations.
"""
import argparse
import json
from pathlib import Path
import subprocess
import tempfile

from native_entry import native_subject
from structured import views
from verify import read_json, render_client

ROOT = Path(__file__).resolve().parents[3]


def subjects():
    yield ('schnorr', 'Schnorr',
           {'example': 'examples/projects/schnorr/main.zkc',
            'schnorr': 'libraries/protocols/sigma/schnorr/lib.zkc'},
           'schnorr::Schnorr<example::G>')
    yield ('sumcheck', 'Sumcheck',
           {'scalar_sumcheck': 'lean/bridges/common/fixtures/sumcheck.zkc'},
           'scalar_sumcheck::Sumcheck')
    for family, forms in [('Schnorr', ['Helpers', 'Reordered', 'EarlyChallenge']),
                          ('Sumcheck', ['Helpers', 'Horner', 'WrongResidual']),
                          ('Factor', ['Expanded', 'Horner', 'WrongPoint', 'WrongResidual'])]:
        module = 'factor_openings' if family == 'Factor' else family.lower() + '_forms'
        fixture = 'factor-openings' if family == 'Factor' else family.lower() + '-forms'
        for form in forms:
            yield (family.lower() + '-' + form.lower(), 'Variants.' + family + form,
                   {module: 'lean/bridges/common/fixtures/' + fixture + '.zkc'},
                   module + '::' + form + 'Protocol')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', type=Path, default=ROOT / 'build/compiler/zkc-compile')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    compiler = args.compiler.resolve()
    count = 0
    def execute(command):
        return subprocess.check_output(list(map(str, command)), cwd=ROOT, text=True, timeout=30)
    def install(relative, content):
        nonlocal count
        target = ROOT / 'lean' / relative
        if args.check:
            if not target.exists() or target.read_text() != content:
                raise AssertionError('Stale generated file: ' + str(target))
        else:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(content)
        count += 1
    with tempfile.TemporaryDirectory(prefix='zkc-scalar-generation-') as temporary:
        directory = Path(temporary)
        for stem, name, modules, subject in subjects():
            flags = ['--source-format=zkc',
                     *['--module=' + key + '=' + str(ROOT / path) for key, path in modules.items()],
                     '--subject=' + subject]
            source, _, interface = native_subject(execute, compiler, flags)
            mlir = directory / (stem + '.mlir')
            mlir.write_text(source)
            data = json.loads(execute([compiler, 'protocol-structured', mlir,
                                       '--symbol=' + interface['protocol']]))
            install(Path('ZkcExamples/NativePrograms/fixtures') / (stem + '.json'),
                    json.dumps(data, indent=2) + '\n')
            prefix = 'ZkcExamples.NativePrograms.' + name
            for module in views(data, directory, prefix, 1):
                path = Path(module.replace('.', '/') + '.lean')
                install(path, (directory / path).read_text())
            if name.startswith('Variants.'):
                client = name.removeprefix('Variants.')
                family = 'schnorr' if client.startswith('Schnorr') else (
                    'sumcheck' if client.startswith('Sumcheck') else 'factor-openings')
                request = read_json(ROOT / 'lean/bridges/common/requests' / (family + '.json'))
                positive = not stem.endswith(('earlychallenge', 'wrongresidual', 'wrongpoint'))
                relative = Path('ZkcExamples/NativePrograms') / (client + '.lean')
                if family == 'factor-openings':
                    relative = Path('security/ZkcSecurity/Examples/NativePrograms') / (client + '.lean')
                install(relative, render_client(data, request, client, positive=positive))
            print(stem, flush=True)
    print(json.dumps({'status': 'pass', 'mode': 'check' if args.check else 'write',
                      'subjects': 12, 'generated_files': count}))


if __name__ == '__main__':
    main()
