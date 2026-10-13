#!/usr/bin/env python3
"""Actual native-to-Lean controls for Schnorr and two-round Sumcheck variants."""
import argparse
import copy
import json
from pathlib import Path
import random
import re
import subprocess
import sys

from extract import ROOT, extract
from native import Native


def execute(command, cwd=ROOT, success=True):
    result = subprocess.run(list(map(str, command)), cwd=cwd, text=True,
                            capture_output=True, timeout=120)
    if result.returncode != (0 if success else 1):
        raise AssertionError(f'{command}\n{result.stdout}\n{result.stderr}')
    return result.stdout if success else result.stdout + result.stderr


def lean(snapshot, run=None, success=True):
    command = [ROOT / 'lean/.lake/build/bin/constructed-source', snapshot]
    if run is not None:
        command.append(run)
    return execute(command, cwd=ROOT / 'lean', success=success)


def source_subject(compiler, optimizer, protocol, variant, directory):
    module = protocol + '_forms'
    source = ROOT / f'lean/bridges/common/fixtures/{protocol}-forms.zkc'
    options = ['--source-format=zkc', f'--entry={module}::{variant}', f'--module={module}={source}']
    original = directory / 'source.mlir'
    original.write_text(execute([compiler, 'language-emit', *options]))
    interface = json.loads(execute([compiler, 'language-interface', *options]))
    (directory / 'interface.json').write_text(json.dumps(interface, indent=2) + '\n')
    symbol = interface['protocol']
    shared = [str(i) for i in range(2 if protocol == 'schnorr' else 10)]
    service = '4' if protocol == 'schnorr' else '10'
    source_text = original.read_text()
    draws = []
    for line in source_text.splitlines():
        if '"protocol.query"' not in line or 'owner = "role00000001"' not in line:
            continue
        result = re.search(r'(%[0-9]+) =', line)[1]
        site = re.search(r'site = "([^"]+)"', line)[1]
        deliveries = [delivery for delivery in source_text.splitlines()
                      if f'"protocol.exchange"({result})' in delivery]
        if len(deliveries) != 1:
            raise ValueError('construction-control-delivery')
        draws.append([site, re.search(r'site = "([^"]+)"', deliveries[0])[1]])
    policy = ['zkc.native-proof-policy/0', symbol, 'role00000000', 'role00000001',
              '0', 'merlin3.bls12-381.fr64be/0', [service], shared, draws, 'zkc.framed/0', '']
    policy_path = directory / 'policy.json'
    policy_path.write_text(json.dumps(policy))
    candidate = directory / 'candidate.mlir'
    candidate.write_text(execute([compiler, 'protocol-construct-proof', original, policy_path]))
    generic = execute([optimizer, candidate, '--mlir-print-op-generic'])
    (directory / 'generic.mlir').write_text(generic)
    output = directory / 'Snapshot.json'
    namespace = 'Constructed' + protocol.title() + variant
    data = extract(compiler, original, policy_path, candidate, output, namespace)
    extract(compiler, original, policy_path, candidate, output, namespace, check=True)
    # Repeated exporter invocation must be byte-stable, including origin strings.
    assert json.loads(execute([compiler, 'protocol-constructed-lean', original, policy_path, candidate])) == data
    audit = directory / 'Audit.lean'
    audit.write_text(output.with_suffix('.lean').read_text() +
                     f'\n#print axioms {namespace}.admitted\n' +
                     f'#print axioms {namespace}.imported_checked\n')
    (directory / 'axioms.log').write_text(
        execute(['lake', 'env', 'lean', audit], cwd=ROOT / 'lean'))
    assert json.loads(lean(output))['status'] == 'admitted'
    return data, generic, output, original, policy_path, candidate


def vectors(protocol, rng):
    for trial in range(10):
        initial = rng.randrange(65521)
        if protocol == 'schnorr':
            base, secret, nonce = [rng.randrange(1, 97) for _ in range(3)]
            inputs = [base, base * secret % 97, initial]

            def receive(i, challenges, b=base, x=secret, n=nonce):
                return b * n % 97 if i == 0 else (n + challenges[0] * x) % 97
        else:
            coefficients = [rng.randrange(97) for _ in range(9)]
            def boundary(a, b, c):
                return (2 * a + b + c) % 97
            first = [boundary(*coefficients[i:i + 3]) for i in range(0, 9, 3)]
            inputs = coefficients + [boundary(*first), initial]

            def receive(i, challenges, a=coefficients, first=first):
                if i < 3:
                    return first[i]
                j = i - 3
                r = challenges[0]
                return (a[j] + r * a[j + 3] + r * r * a[j + 6]) % 97
        yield 'honest', inputs, receive, None, 'abort'
        # Dishonest payloads must be the values observed and checked by Lean.
        for corrupt_at in ([0, 1] if protocol == 'schnorr' else [0, 3, 5]):
            def corrupt(i, challenges, receive=receive, at=corrupt_at):
                return (receive(i, challenges) + (1 if i == at else 0)) % 97
            yield 'dishonest', inputs, corrupt, None, 'abort'
        if trial == 0:
            for reason in ('reject', 'abort', 'exhausted', 'incomplete', 'refused'):
                yield 'provider-stop', inputs, receive, 2, reason


def check_outcome(label, outcome, reason):
    if label == 'honest':
        assert outcome[0] == 'returned' and outcome[1][0] == 1, outcome
    elif label == 'dishonest':
        assert outcome == ['stopped', 'reject'] or (outcome[0] == 'returned' and outcome[1][0] == 0), outcome
    elif label == 'provider-stop':
        assert outcome == ['stopped', reason], outcome


def controls(compiler, optimizer, protocol, variant, directory):
    directory.mkdir(parents=True, exist_ok=True)
    data, generic, output, original, policy, candidate = source_subject(
        compiler, optimizer, protocol, variant, directory)
    requests, expected = [], []
    for label, inputs, receive, stop_at, reason in vectors(protocol, random.Random(20261013)):
        native = Native(generic, receive, stop_at, reason)
        outcome = native.run(data[5], inputs)
        check_outcome(label, outcome, reason)
        requests.append(['zkc.constructed-run/0', inputs, native.entries])
        expected.append(['zkc.constructed-result/0', outcome, len(native.entries),
                         [[entry[0], entry] for entry in native.entries]])
    runs = directory / 'runs.json'
    runs.write_text(json.dumps(['zkc.constructed-runs/0', requests]))
    actual = json.loads(lean(output, runs))
    assert actual == expected, next((i, a, b) for i, (a, b) in enumerate(zip(actual, expected)) if a != b)
    negatives = []
    for name, mutate, code in [
        ('unknown-field', lambda x: x.append('ignored'), 'invalid-shape'),
        ('bad-reference', lambda x: x[11].__setitem__(0, 8192), 'constructed-source-operands'),
        ('bad-result-type', lambda x: x[9].__setitem__(0, 'different'), 'constructed-source-operands'),
        ('bad-project', lambda x: next(i for i in x[10] if i[0] == 'project').__setitem__(2, 8192), 'constructed-source-project'),
        ('version', lambda x: x.__setitem__(0, 'zkc.constructed-source/1'), 'invalid-shape'),
    ]:
        mutated = copy.deepcopy(data)
        mutate(mutated)
        path = directory / f'{name}.json'
        path.write_text(json.dumps(mutated))
        refusal = json.loads(lean(path, success=False))
        assert refusal['code'] == code, refusal
        negatives.append(name)
    # Well-typed substitutions still have observable consequences. Admission
    # alone is deliberately not authentication or construction correspondence.
    contexts = [[ty] for ty in data[8]]
    observation = 0
    mutations = []
    for position, instruction in enumerate(data[10]):
        if instruction[0] == 'apply':
            op, operands = instruction[1:]
            if op[0] == 'crypto.exec.indexed_transcript_observe_data':
                observation += 1
                operand = 0 if observation == 2 else 1
                alternatives = [i for i, ty in enumerate(contexts)
                                if ty == [op[4][operand]] and i != operands[operand]]
                if alternatives and observation <= 2:
                    changed = copy.deepcopy(data)
                    changed[10][position][2][operand] = alternatives[-1]
                    mutations.append(('stale-state' if operand == 0 else 'wrong-payload', changed))
            contexts.insert(0, op[5])
        elif instruction[0] == 'project':
            contexts.insert(0, [instruction[1][instruction[2]]])
    first_run = directory / 'first-run.json'
    first_run.write_text(json.dumps(requests[0]))
    for name, changed in mutations:
        path = directory / (name + '.json')
        path.write_text(json.dumps(changed))
        assert json.loads(lean(path))['status'] == 'admitted'
        assert json.loads(lean(path, first_run))[1] == ['stopped', 'refused']
        negatives.append(name)
    # Wrong provider reply arity and missing reply remain actual stopped runs.
    bad = copy.deepcopy(requests[0])
    bad[2][0][1][1] = []
    path = directory / 'bad-reply.json'
    path.write_text(json.dumps(bad))
    assert json.loads(lean(output, path))[1] == ['stopped', 'refused']
    missing = copy.deepcopy(requests[0])
    missing[2] = []
    path.write_text(json.dumps(missing))
    assert json.loads(lean(output, path))[1] == ['stopped', 'incomplete']
    negatives += ['bad-reply', 'missing-reply']
    # Same-typed native arithmetic mutation survives formation but fails complete
    # source-relative candidate comparison before the bridge exports anything.
    additions = re.finditer(r'("algebra\.(?:field_add|group_add)"\()(%[^,]+), (%[^)]+)(\))', generic)
    addition = next(match for match in additions if match[2] != match[3])
    changed = (generic[:addition.start()] + addition[1] + addition[3] + ', ' +
               addition[2] + addition[4] + generic[addition.end():])
    assert changed != generic
    mutated_candidate = directory / 'mutated-candidate.mlir'
    mutated_candidate.write_text(changed)
    refusal = execute([compiler, 'protocol-constructed-lean', original, policy, mutated_candidate], success=False)
    assert 'native-proof-correspondence' in refusal, refusal
    negatives.append('native-candidate')
    # Detached carrier mutation is rejected by exact regeneration even if it
    # remains well-typed (this is distinct from Lean formation).
    mutated = copy.deepcopy(data)
    mutated[4] += '-changed'
    output.write_text(json.dumps(mutated, indent=2) + '\n')
    try:
        extract(compiler, original, policy, candidate, output,
                'Constructed' + protocol.title() + variant, check=True)
    except ValueError as error:
        assert str(error) == 'constructed-source-mismatch'
    else:
        raise AssertionError('detached carrier accepted')
    output.write_text(json.dumps(data, indent=2) + '\n')
    negatives.append('detached-carrier')
    return {'protocol': protocol, 'variant': variant, 'candidate': data[2],
            'instructions': len(data[10]), 'handlers': len(data[7]),
            'runs': len(requests), 'outcomes': {kind: sum(e[1][0] == kind for e in expected)
                                             for kind in ('returned', 'stopped')},
            'negative_controls': negatives}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', type=Path, default=ROOT / 'build/compiler/zkc-compile')
    parser.add_argument('--optimizer', type=Path, default=ROOT / 'build/compiler/zkc-opt')
    parser.add_argument('--output', type=Path, default=ROOT / 'build/experiments/constructed/controls')
    parser.add_argument('--protocol', choices=['schnorr', 'sumcheck'])
    args = parser.parse_args()
    args.compiler = args.compiler.resolve()
    args.optimizer = args.optimizer.resolve()
    args.output = args.output.resolve()
    # A tool crash or unrelated failure is not an ordinary tested refusal.
    for command in ([sys.executable, '-c', 'raise SystemExit(2)'],
                    [sys.executable, '-c', 'import os, signal; os.kill(os.getpid(), signal.SIGTERM)']):
        try:
            execute(command, success=False)
        except AssertionError:
            pass
        else:
            raise AssertionError('non-refusal exit accepted by test helper')
    results = []
    for protocol, variants in [('schnorr', ['Helpers', 'Reordered']), ('sumcheck', ['Helpers', 'Horner'])]:
        if args.protocol and args.protocol != protocol:
            continue
        for variant in variants:
            result = controls(args.compiler, args.optimizer, protocol, variant,
                              args.output / (protocol + '-' + variant.lower()))
            results.append(result)
            (args.output / (protocol + '-' + variant.lower()) / 'report.json').write_text(
                json.dumps(result, indent=2) + '\n')
            print(json.dumps(result), flush=True)
    (args.output / 'report.json').write_text(json.dumps(results, indent=2) + '\n')


if __name__ == '__main__':
    main()
