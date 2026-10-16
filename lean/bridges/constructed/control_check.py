#!/usr/bin/env python3
"""Actual runtime-loop exports versus an independent generic-native SSA runner.

These controls use token values and a deterministic transcript, not a native
cryptographic provider. Kernel correspondence is supplied by Control's theorem;
the generated artifact is separately checked below with no assumed source map.
"""
import argparse
import copy
import json
from pathlib import Path
import subprocess

from check import execute, lean
from extract import ROOT, extract
from native import Native


def subject(args, name, module, inputs, service):
    directory = args.output / name
    directory.mkdir(parents=True, exist_ok=True)
    source = ROOT / f'lean/bridges/constructed/fixtures/{name}.zkc'
    options = ['--source-format=zkc', f'--entry={module}::Demo', f'--module={module}={source}']
    original = directory / 'source.mlir'
    original.write_text(execute([args.compiler, 'language-emit', *options]))
    interface = json.loads(execute([args.compiler, 'language-interface', *options]))
    policy = ['zkc.native-proof-policy/0', interface['protocol'], 'role00000000', 'role00000001',
              '0', 'merlin3.bls12-381.fr64be/0', [str(service)], list(map(str, inputs)),
              [['label_6368616c6c656e6765', 'label_64656c6976657279_0']], 'zkc.framed/0', '']
    policy_path = directory / 'policy.json'
    policy_path.write_text(json.dumps(policy))
    candidate = directory / 'candidate.mlir'
    candidate.write_text(execute([args.compiler, 'protocol-construct-proof', original, policy_path]))
    snapshot = directory / 'Snapshot.json'
    data = extract(args.compiler, original, policy_path, candidate, snapshot, 'ConstructedControl')
    assert data[0] == 'zkc.constructed-control/0'
    extract(args.compiler, original, policy_path, candidate, snapshot, 'ConstructedControl', check=True)
    assert json.loads(lean(snapshot))['status'] == 'admitted'
    generic = execute([args.optimizer, candidate, '--mlir-print-op-generic'])
    (directory / 'generic.mlir').write_text(generic)
    return directory, snapshot, data, generic


def compare(directory, snapshot, data, generic, name, inputs, receive, stop_at=None):
    native = Native(generic, receive, stop_at=stop_at)
    expected = native.run(data[5], inputs)
    path = directory / (name + '.run.json')
    path.write_text(json.dumps(['zkc.constructed-run/0', inputs, native.entries]))
    result = json.loads(lean(snapshot, path))
    assert result == ['zkc.constructed-result/0', expected, len(native.entries),
                      [[entry[0], entry] for entry in native.entries]], (name, expected, result)
    return {'case': name, 'outcome': expected, 'primitive_calls': len(native.entries)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', type=Path, default=ROOT / 'build/compiler/zkc-compile')
    parser.add_argument('--optimizer', type=Path, default=ROOT / 'build/compiler/zkc-opt')
    parser.add_argument('--output', type=Path, default=ROOT / 'build/experiments/constructed/control')
    parser.add_argument('--kernel-timeout', type=int, default=120)
    args = parser.parse_args()
    args.compiler, args.optimizer, args.output = args.compiler.resolve(), args.optimizer.resolve(), args.output.resolve()
    records = []
    subjects = [('bounded-control', 'bounded', [0], 2), ('nested-control', 'nested_control', [0, 1, 2], 3)]
    for name, module, shared, service in subjects:
        directory, snapshot, data, generic = subject(args, name, module, shared, service)
        requests = ([[count, 19] for count in range(4)] if name == 'bounded-control' else
                    [[outer, inner, 7, 19] for outer in range(4) for inner in range(4)])
        for number, inputs in enumerate(requests):
            records.append(compare(directory, snapshot, data, generic, f'counts-{number}',
                                   inputs, lambda *_: 14))
        inputs = [2, 19] if name == 'bounded-control' else [2, 2, 7, 19]
        for position in [0, 1, 5, 10, 18]:
            records.append(compare(directory, snapshot, data, generic, f'stop-{position}',
                                   inputs, lambda *_: 14, position))
        if name == 'nested-control':
            records.append(compare(directory, snapshot, data, generic, 'dishonest', inputs, lambda *_: 15))
            assert records[-1]['outcome'] == ['stopped', 'reject']
        # Runtime selection must use an index-typed operand, even if a test
        # execution could avoid entering the loop.
        changed = copy.deepcopy(data)
        loop = changed[10][3]
        assert loop[0] == 'loop'
        loop[2] = next(i for i, ty in enumerate(changed[10][1]) if ty != 'ui64')
        altered = directory / 'altered.json'
        altered.write_text(json.dumps(changed))
        refused = subprocess.run([ROOT / 'lean/.lake/build/bin/constructed-source', altered],
                                 text=True, capture_output=True, timeout=30)
        assert refused.returncode == 1 and 'constructed-control-count' in refused.stdout, refused
        refusal_controls = [
            ('unknown-field', lambda value: value.append('ignored'), 'invalid-shape'),
            ('unknown-body', lambda value: value[10].__setitem__(0, 'opaque'), 'invalid-shape'),
            ('natural-limit', lambda value: value[10][3].__setitem__(1, 8193), 'expected-natural'),
            ('expansion-limit', lambda value: value[10][3].__setitem__(1, 8192), 'constructed-control-shape'),
            ('carried-type', lambda value: value[10][3][4].__setitem__(0,
                next(i for i, ty in enumerate(value[10][1]) if ty != value[10][3][3][0])),
             'constructed-control-carried'),
        ]
        for control_name, mutate, code in refusal_controls:
            changed = copy.deepcopy(data)
            mutate(changed)
            altered = directory / (control_name + '.json')
            altered.write_text(json.dumps(changed))
            refused = subprocess.run([ROOT / 'lean/.lake/build/bin/constructed-source', altered],
                                     text=True, capture_output=True, timeout=30)
            assert refused.returncode == 1 and json.loads(refused.stdout)['code'] == code, refused
        proof = subprocess.run(['lake', 'env', 'lean', snapshot.with_suffix('.lean')],
                               cwd=ROOT / 'lean', text=True, capture_output=True,
                               timeout=args.kernel_timeout)
        (directory / 'kernel.log').write_text(proof.stdout + proof.stderr)
        if proof.returncode != 0:
            raise AssertionError(f'{name}: kernel admission failed\n{proof.stdout}\n{proof.stderr}')
        # The separately retained JSON must describe the very same Snapshot.
        # A well-formed constructor with another entry is insufficient.
        changed_proof = snapshot.with_name('Detached.lean')
        changed_proof.write_text(snapshot.with_suffix('.lean').read_text().replace(
            '  entry := ', '  entry := "different-entry" ++ ', 1))
        detached = subprocess.run(['lake', 'env', 'lean', changed_proof], cwd=ROOT / 'lean',
                                  text=True, capture_output=True, timeout=args.kernel_timeout)
        (directory / 'detached.log').write_text(detached.stdout + detached.stderr)
        assert detached.returncode == 1 and 'error:' in detached.stdout, detached
        print(json.dumps({'subject': name, 'kernel': 'checked', 'cases': len(requests),
                          'detached_constructor': 'refused'}), flush=True)
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / 'report.json').write_text(json.dumps(records, indent=2) + '\n')
    print(json.dumps({'status': 'passed', 'comparisons': len(records)}))


if __name__ == '__main__':
    main()
