#!/usr/bin/env python3
"""Fresh native examples and failure controls for constructed realization.

All positive equations are kernel checked from actual freshly exported bodies.
A negative Lean check must exit 1; timeout, crash or missing tools fail this test.
"""
import argparse
import copy
import json
from pathlib import Path
import re
import subprocess
import sys

from realization import CHALLENGE, OBSERVE, read_snapshot, render, validate

ROOT = Path(__file__).resolve().parents[3]


def execute(command, cwd=ROOT, timeout=240):
    return subprocess.run(list(map(str, command)), cwd=cwd, text=True,
                          capture_output=True, timeout=timeout, check=False)


def native(compiler, arguments):
    result = execute([compiler, *arguments])
    if result.returncode != 0:
        raise AssertionError(f'native command failed: {arguments}\n{result.stdout}\n{result.stderr}')
    return result.stdout


def subject(compiler, protocol, variant, directory):
    directory.mkdir(parents=True, exist_ok=True)
    module = protocol + '_forms'
    fixture = ROOT / f'lean/bridges/common/fixtures/{protocol}-forms.zkc'
    options = ['--source-format=zkc', f'--entry={module}::{variant}', f'--module={module}={fixture}']
    source = directory / 'source.mlir'
    source.write_text(native(compiler, ['language-emit', *options]))
    interface = json.loads(native(compiler, ['language-interface', *options]))
    (directory / 'interface.json').write_text(json.dumps(interface, indent=2) + '\n')
    lines = source.read_text().splitlines()
    draws = []
    for line in lines:
        if '"protocol.query"' not in line or 'owner = "role00000001"' not in line:
            continue
        result = re.search(r'(%[0-9]+) =', line)[1]
        site = re.search(r'site = "([^"]+)"', line)[1]
        deliveries = [line for line in lines if f'"protocol.exchange"({result})' in line]
        if len(deliveries) != 1:
            raise AssertionError('native delivery selection is ambiguous')
        draws.append([site, re.search(r'site = "([^"]+)"', deliveries[0])[1]])
    fields = 2 if protocol == 'schnorr' else 10
    policy = ['zkc.native-proof-policy/0', interface['protocol'], 'role00000000', 'role00000001',
              '0', 'merlin3.bls12-381.fr64be/0', ['4' if protocol == 'schnorr' else '10'],
              [str(i) for i in range(fields)], draws, 'zkc.framed/0', '']
    policy_path = directory / 'policy.json'
    policy_path.write_text(json.dumps(policy, indent=2) + '\n')
    candidate = directory / 'candidate.mlir'
    candidate.write_text(native(compiler, ['protocol-construct-proof', source, policy_path]))
    data = json.loads(native(compiler, ['protocol-constructed-lean', source, policy_path, candidate]))
    (directory / 'Snapshot.json').write_text(json.dumps(data, indent=2) + '\n')
    return data


def kernel(data, protocol, directory, *, success, timeout):
    directory.mkdir(parents=True, exist_ok=True)
    (directory / 'Snapshot.json').write_text(json.dumps(data, indent=2) + '\n')
    path = directory / 'Realization.lean'
    path.write_text(render(data, protocol))
    result = execute(['lake', 'env', 'lean', path], cwd=ROOT / 'lean', timeout=timeout)
    (directory / 'lean.log').write_text(result.stdout + result.stderr)
    check_kernel_result(result, directory.name, success=success)


def check_kernel_result(result, subject_name, *, success):
    """Only an actual equation proof failure is a successful negative control."""
    expected = 0 if success else 1
    if result.returncode != expected:
        raise AssertionError(f'{subject_name}: expected exit {expected}, got {result.returncode}\n{result.stdout}\n{result.stderr}')
    if success and 'CONSTRUCTED-REALIZATION-PASS' not in result.stdout:
        raise AssertionError('missing realization audit marker')
    if not success:
        expected_error = re.search(r'error: (?:unsolved goals|Tactic `rfl` failed:)', result.stdout)
        errors = [line for line in result.stdout.splitlines() if 'error:' in line]
        allowed_errors = ('error: unsolved goals', 'error: Tactic `rfl` failed:',
                          'error: constructed realization uses unexpected axiom: sorryAx')
        if (not expected_error or 'CONSTRUCTED-REALIZATION-PASS' in result.stdout or
                any(not any(marker in line for marker in allowed_errors) for line in errors)):
            raise AssertionError('negative control did not fail its equation proof')


def harness_controls(directory):
    """A broken tool or parser must not look like a checked counterexample."""
    directory.mkdir(parents=True, exist_ok=True)
    controls = [
        ('signal', 'import os, signal; os.kill(os.getpid(), signal.SIGTERM)'),
        ('exit-two', 'raise SystemExit(2)'),
        ('missing-import', 'print("error: unknown module prefix"); raise SystemExit(1)'),
    ]
    checked = []
    for name, code in controls:
        result = execute([sys.executable, '-c', code])
        try:
            check_kernel_result(result, name, success=False)
        except AssertionError:
            checked.append(name)
        else:
            raise AssertionError(f'{name}: tool failure counted as a proof refusal')
    for name, contents in [('json-depth', '[' * 129 + '0' + ']' * 129),
                           ('json-bytes', ' ' * 16_000_001)]:
        path = directory / (name + '.json')
        path.write_text(contents)
        try:
            read_snapshot(path)
        except ValueError as error:
            if str(error) != 'constructed-realization-limit':
                raise AssertionError(f'{name}: wrong refusal: {error}') from error
            checked.append(name)
        else:
            raise AssertionError(f'{name}: oversized input admitted')
        finally:
            path.unlink()
    return checked


def stale_state(data):
    altered = copy.deepcopy(data)
    initial = len(data[8]) - 1
    for instruction in altered[10]:
        if instruction[0] == 'apply' and instruction[1][0] == CHALLENGE:
            instruction[2][0] = initial
            return altered
        if instruction[0] in ('apply', 'project'):
            initial += 1
    raise AssertionError('missing challenge')


def omitted_final_observation(data):
    """Return the prior transcript after executing the final observation.

This is well typed and preserves the acceptance Boolean, so an acceptance-only
normalizer would incorrectly accept this control.
"""
    altered = copy.deepcopy(data)
    candidates = [(i, x[2][0]) for i, x in enumerate(altered[10])
                  if x[0] == 'apply' and x[1][0] == OBSERVE]
    index, old = candidates[-1]
    after = sum(x[0] in ('apply', 'project') for x in altered[10][index:])
    altered[11][1] = old + after
    return altered



def omitted_message(data):
    altered = copy.deepcopy(data)
    public_input = 0
    for instruction in altered[10]:
        if instruction[0] == 'apply' and instruction[1][0] == OBSERVE:
            instruction[2][1] = public_input
            return altered
        if instruction[0] in ('apply', 'project'):
            public_input += 1
    raise AssertionError('missing observation')


def changed_arithmetic(data):
    altered = copy.deepcopy(data)
    operation = next(x[1] for x in altered[10] if x[0] == 'apply' and x[1][0] == 'algebra.field_add')
    operation[0] = 'algebra.field_multiply'
    return altered

def incorrect_math(data):
    altered = copy.deepcopy(data)
    equality = next(x for x in reversed(altered[10]) if x[0] == 'apply' and
                    x[1][0] in ('algebra.group_equal', 'algebra.field_equal'))
    equality[2][1] = equality[2][0]
    return altered


def metadata_controls(data, protocol):
    def refused(name, mutation, expected):
        altered = copy.deepcopy(data)
        mutation(altered)
        try:
            validate(altered, protocol)
        except ValueError as error:
            if str(error) != 'constructed-realization-' + expected:
                raise AssertionError(f'{name}: wrong refusal: {error}') from error
            return name
        raise AssertionError(f'{name}: admitted')

    def unknown(d):
        next(x for x in d[10] if x[0] == 'apply')[1][0] = 'arbitrary.operation'

    def foreign_binding(d):
        op = next(x[1] for x in d[10] if x[0] == 'apply' and x[1][0] == CHALLENGE)
        op[2] = op[2].replace('implementation = ""', 'implementation = "foreign"')

    def missing_message(d):
        op = next(x[1] for x in d[10] if x[0] == 'apply' and x[1][0] == OBSERVE)
        # Retain well-formed framing but give it an unrelated entry identity.
        match = re.search(r'parameters = \["([0-9a-f]+)"\]', op[1])
        before = d[3].encode().hex()
        after = ('x' + d[3][1:]).encode().hex()
        op[1] = op[1].replace(match[1], match[1].replace(before, after))

    def unknown_local(d):
        next(x for x in d[10] if x[0] == 'apply')[1][3] += '/UnselectedHandler:call'

    def too_many_instructions(d):
        d[10] = [d[10][0]] * 257

    def invalid_reference(d):
        next(x for x in d[10] if x[0] == 'apply' and x[2])[2][0] = 8192

    return [refused('unknown-primitive', unknown, 'primitive'),
            refused('foreign-binding', foreign_binding, 'binding'),
            refused('wrong-occurrence', missing_message, 'occurrence-entry'),
            refused('unknown-local-origin', unknown_local, 'local-origin'),
            refused('instruction-limit', too_many_instructions, 'limit'),
            refused('invalid-reference', invalid_reference, 'reference')]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', type=Path, required=True)
    parser.add_argument('--output', type=Path, default=ROOT / 'build/experiments/constructed-realization')
    parser.add_argument('--timeout', type=int, default=300)
    parser.add_argument('--reuse-exports', action='store_true', help='reuse only local exports, rerun every Lean proof')
    args = parser.parse_args()
    output = args.output.resolve()
    controls = harness_controls(output / 'harness-controls')
    (output / 'harness-controls.json').write_text(json.dumps(controls, indent=2) + '\n')
    records = []
    for protocol, variants in [('schnorr', ['Helpers', 'Reordered']), ('sumcheck', ['Helpers', 'Horner'])]:
        for variant in variants:
            directory = output / f'{protocol}-{variant.lower()}'
            data = (json.loads((directory / 'Snapshot.json').read_text()) if args.reuse_exports else
                    subject(args.compiler, protocol, variant, directory))
            kernel(data, protocol, directory, success=True, timeout=args.timeout)
            records.append({'subject': directory.name, 'status': 'kernel-checked',
                            'metadata_controls': metadata_controls(data, protocol)})
            print(json.dumps(records[-1]), flush=True)
        for name, mutate in [('stale-state', stale_state), ('omitted-message', omitted_message),
                             ('omitted-final-observation', omitted_final_observation),
                             ('incorrect-math', incorrect_math)]:
            kernel(mutate(data), protocol, output / f'{protocol}-{name}', success=False, timeout=args.timeout)
            records.append({'subject': protocol + '-' + name, 'status': 'kernel-refused'})
            print(json.dumps(records[-1]), flush=True)
    kernel(changed_arithmetic(data), 'sumcheck', output / 'sumcheck-changed-arithmetic',
           success=False, timeout=args.timeout)
    records.append({'subject': 'sumcheck-changed-arithmetic', 'status': 'kernel-refused'})
    directory = output / 'sumcheck-wrongresidual'
    data = (json.loads((directory / 'Snapshot.json').read_text()) if args.reuse_exports else
            subject(args.compiler, 'sumcheck', 'WrongResidual', directory))
    kernel(data, 'sumcheck', directory, success=False, timeout=args.timeout)
    records.append({'subject': directory.name, 'status': 'kernel-refused'})
    (output / 'report.json').write_text(json.dumps(records, indent=2) + '\n')
    print(json.dumps({'status': 'passed', 'checks': len(records)}))


if __name__ == '__main__':
    main()
