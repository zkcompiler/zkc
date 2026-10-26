#!/usr/bin/env python3
"""Reproducible source/property matrix and refusal controls for proof requests."""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import time

from native_entry import native_subject
from contracts import label
from verify import verify, read_json

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
FIXTURES = ROOT / 'lean/ZkcExamples/NativePrograms/fixtures'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--compiler', type=Path, default=ROOT / 'build/compiler/zkc-compile')
    parser.add_argument('--lake', default='lake')
    args = parser.parse_args()
    args.output = args.output.resolve()
    args.output.mkdir(parents=True, exist_ok=True)
    requests = {name: read_json(HERE / 'requests' / f'{name}.json')
                for name in ('schnorr', 'sumcheck', 'factor-openings')}
    rows = []

    def check(name, data, request, expected):
        start = time.monotonic()
        receipt = verify(data, request, args.output / name, args.lake, timeout=90)
        code = receipt['obligations'][0]['code'] if receipt['obligations'] else None
        actual = receipt['status'] if code is None else code
        if not (actual == expected):
            raise AssertionError((name, expected, actual, args.output / name / 'lean.log'))
        row = {'case': name, 'status': actual, 'properties': len(receipt['verified_properties']),
               'seconds': round(time.monotonic() - start, 3)}
        rows.append(row)
        print(json.dumps(row), flush=True)

    # Each source certificate is reused for two independent property consumers.
    for family, forms in [('schnorr', ['', '-helpers', '-reordered']),
                          ('sumcheck', ['', '-helpers', '-horner']),
                          ('factor', ['-expanded', '-horner'])]:
        request = requests['factor-openings' if family == 'factor' else family]
        for form in forms:
            check(family + (form or '-original'), read_json(FIXTURES / f'{family}{form}.json'),
                  request, 'verified-in-model')

    for source, family in [('schnorr-earlychallenge', 'schnorr'), ('sumcheck-wrongresidual', 'sumcheck'),
                           ('factor-wrongpoint', 'factor-openings'), ('factor-wrongresidual', 'factor-openings')]:
        check(source, read_json(FIXTURES / f'{source}.json'), requests[family], 'correspondence-unproved')

    # A genuinely new native source: renamed module, protocol, inputs and sites,
    # reordered public inputs, helper functions and Horner arithmetic.
    native = (HERE / 'fixtures/factor-openings.zkc').read_text()
    native = native.replace('module factor_openings;', 'module alternative;')
    native = native.replace('HornerProtocol', 'EvaluationVerifier')
    native = native.replace('l00: F @(P,V), l01: F @(P,V)', 'l01: F @(P,V), l00: F @(P,V)')
    native = native.replace('site(left)', 'site(open_factor_a)').replace('site(right)', 'site(open_factor_b)')
    native = native.replace('claim:', 'target:').replace('== claim;', '== target;')
    source = args.output / 'alternative.zkc'
    source.write_text(native)
    flags = ['--source-format=zkc', f'--module=alternative={source}', '--subject=alternative::EvaluationVerifier']
    def execute(command):
        return subprocess.check_output(list(map(str, command)), cwd=ROOT, text=True, timeout=30)
    mlir, interface_text, interface = native_subject(execute, args.compiler, flags)
    if not (interface['original'] == hashlib.sha256(mlir.encode()).hexdigest()):
        raise AssertionError("bridges/common/verify_tests.py:70: interface['original'] == hashlib.sha256(mlir.encode()).hexdigest()")
    path = args.output / 'alternative.mlir'
    path.write_text(mlir)
    data = json.loads(execute([args.compiler, 'protocol-lean', path, '--symbol=' + interface['protocol']]))
    if not (data[1] == 'sha256:' + interface['original']):
        raise AssertionError("bridges/common/verify_tests.py:74: data[1] == 'sha256:' + interface['original']")
    request = copy.deepcopy(requests['factor-openings'])
    request['inputs'][0], request['inputs'][1] = request['inputs'][1], request['inputs'][0]
    request['wiring']['leftSite'] = label('open_factor_a')
    request['wiring']['rightSite'] = label('open_factor_b')
    check('native-renamed-reordered', data, request, 'verified-in-model')
    stale = copy.deepcopy(request)
    stale['wiring']['leftSite'] = label('left')
    check('stale-site-binding', data, stale, 'correspondence-unproved')
    stale = copy.deepcopy(request)
    stale['inputs'][0], stale['inputs'][1] = stale['inputs'][1], stale['inputs'][0]
    check('stale-input-binding', data, stale, 'correspondence-unproved')

    original = read_json(FIXTURES / 'factor-expanded.json')
    mutations = [
        ('unknown-contract', 'contract', 'unregistered/0', 'contract-unregistered'),
        ('unknown-property', 'properties', ['knowledge-soundness'], 'property-unregistered'),
        ('missing-pcs-adapter', 'properties', ['pcs-soundness'], 'property-unregistered'),
        ('missing-fiat-shamir-reduction', 'properties', ['fiat-shamir-soundness'], 'property-unregistered'),
        ('correlated-coins', 'experiment', 'interactive.uniform-marginals/0', 'experiment-mismatch'),
        ('unjustified-sampler', 'experiment', 'native-random-handle/0', 'experiment-mismatch'),
        ('wrong-role', 'role', 0, 'role-selection'),
        ('request-version', 'format', 'zkc.proof-request/999', 'request-version'),
    ]
    for name, key, value, expected in mutations:
        request = copy.deepcopy(requests['factor-openings'])
        request[key] = value
        check(name, original, request, expected)
    request = copy.deepcopy(requests['factor-openings'])
    request['inputs'][0] = 'by exact Classical.choice'
    check('lean-code-as-input', original, request, 'input-bindings')
    request = copy.deepcopy(requests['factor-openings'])
    request['wiring']['fieldDomain'] = 'another-field'
    check('different-field', original, request, 'input-domain')
    changed = copy.deepcopy(original)
    changed[8].append(['pure', ['field.add', 'bls12-381.fr'], [2048, 2048]])
    check('malformed-dormant-binding', changed, requests['factor-openings'], 'unsupported-input')
    # Copying a positive hash/name onto a semantically wrong source grants no proof.
    changed = read_json(FIXTURES / 'factor-wrongpoint.json')
    changed[1:3] = original[1:3]
    check('copied-positive-identity', changed, requests['factor-openings'], 'correspondence-unproved')
    changed = copy.deepcopy(original)
    changed[8][0].append('ignored-field')
    check('instruction-extra-field', changed, requests['factor-openings'], 'unsupported-input')
    for name, operation in [('boolean-extra-field', ['bool.constant', True, 'ignored']),
                            ('constant-extra-field', ['field.constant', 'bls12-381.fr', '1', 'ignored'])]:
        changed = copy.deepcopy(original)
        changed[8].append(['pure', operation, []])
        changed[9] += 1
        check(name, changed, requests['factor-openings'], 'unsupported-input')
    changed = copy.deepcopy(original)
    changed[1] = 'sha256:not-a-digest'
    check('malformed-source-identity', changed, requests['factor-openings'], 'unsupported-input')
    # Test the checker boundary itself: a corrupted generator candidate cannot be
    # admitted by its own success marker or by other valid property aliases.
    import verify as implementation
    original_generator = implementation.generate
    for name, proposal in [('candidate-not-object', '.ret .here'),
                           ('candidate-missing-program', {}),
                           ('candidate-extra-field', {'program': '.ret .here', 'extra': True}),
                           ('candidate-retired-process', {'program': '.ret .here', 'process': '.done none'})]:
        implementation.generate = lambda _data, _request, proposal=proposal: proposal
        try:
            check(name, read_json(FIXTURES / 'sumcheck.json'), requests['sumcheck'], 'candidate-shape')
        finally:
            implementation.generate = original_generator
    def corrupted_generator(data, request):
        candidate = original_generator(data, request)
        candidate['program'] = 'by sorry'
        return candidate
    implementation.generate = corrupted_generator
    try:
        check('generator-sorry-control', read_json(FIXTURES / 'sumcheck.json'),
              requests['sumcheck'], 'candidate-syntax')
    finally:
        implementation.generate = original_generator
    for name, payload in [
            ('generator-exit-control', 'run_cmd Lean.logInfo "PROOF-REQUEST-KERNEL-PASS"\n'
             'run_cmd Lean.logInfo "PROOF-REQUEST-BOUNDARY-PASS"\n#exit'),
            ('generator-comment-control', '.ret .here /-'),
            ('generator-line-comment-control', '.ret .here --'),
            ('generator-command-control', '.ret .here\ndef approvedContract := true')]:
        def active_generator(data, request, payload=payload):
            return {'program': payload}
        implementation.generate = active_generator
        try:
            check(name, read_json(FIXTURES / 'sumcheck.json'), requests['sumcheck'], 'candidate-syntax')
        finally:
            implementation.generate = original_generator
    def wrong_subject_generator(data, request):
        return original_generator(read_json(FIXTURES / 'factor-horner.json'), request)
    implementation.generate = wrong_subject_generator
    try:
        check('wrong-subject-certificate-control', read_json(FIXTURES / 'factor-wrongpoint.json'),
              requests['factor-openings'], 'correspondence-unproved')
    finally:
        implementation.generate = original_generator
    def mutating_generator(data, request):
        data[8][:] = read_json(FIXTURES / 'factor-horner.json')[8]
        return original_generator(data, request)
    implementation.generate = mutating_generator
    try:
        check('mutated-source-control', read_json(FIXTURES / 'factor-wrongpoint.json'),
              requests['factor-openings'], 'correspondence-unproved')
    finally:
        implementation.generate = original_generator
    def mutating_request_generator(data, request):
        request['properties'][:] = ['perfect-completeness']
        return original_generator(data, request)
    implementation.generate = mutating_request_generator
    try:
        original_request = copy.deepcopy(requests['sumcheck'])
        receipt = verify(read_json(FIXTURES / 'sumcheck.json'), original_request,
                         args.output / 'mutated-request-control', args.lake)
        if not (receipt['status'] == 'verified-in-model'):
            raise AssertionError("bridges/common/verify_tests.py:188: receipt['status'] == 'verified-in-model'")
        if not ([p['property'] for p in receipt['verified_properties']] == original_request['properties']):
            raise AssertionError("bridges/common/verify_tests.py:189: [p['property'] for p in receipt['verified_properties']] == original_request['properties']")
        if not (read_json(args.output / 'mutated-request-control/request.json') == original_request):
            raise AssertionError("bridges/common/verify_tests.py:190: read_json(args.output / 'mutated-request-control/request.json') == original_request")
        rows.append({'case': 'mutated-request-control', 'status': 'verified-in-model',
                     'properties': len(receipt['verified_properties'])})
    finally:
        implementation.generate = original_generator
    # A deliberately tiny external budget must never become a verified receipt.
    limited = verify(original, requests['factor-openings'], args.output / 'proof-budget-control',
                     args.lake, timeout=0.001)
    if not (limited['status'] == 'unresolved' and limited['obligations'][0]['code'] == 'proof-budget'):
        raise AssertionError("bridges/common/verify_tests.py:198: limited['status'] == 'unresolved' and limited['obligations'][0]['code'] == 'proof-budget'")
    rows.append({'case': 'proof-budget-control', 'status': 'proof-budget', 'properties': 0})
    duplicate = args.output / 'duplicate-members.json'
    duplicate.write_text('{"format":"a","format":"b"}')
    deep = args.output / 'deep-json.json'
    deep.write_text('[' * 5000 + '0' + ']' * 5000)
    for path in (duplicate, deep):
        try:
            read_json(path)
        except ValueError:
            pass
        else:
            raise AssertionError('malformed JSON was accepted')
    quoted = args.output / 'quoted-delimiters.json'
    quoted_value = '[\\"' * 5000
    quoted.write_text(json.dumps(quoted_value))
    if not (read_json(quoted) == quoted_value):
        raise AssertionError('bridges/common/verify_tests.py:214: read_json(quoted) == quoted_value')
    report = {'cases': rows, 'verified_requests': sum(r['status'] == 'verified-in-model' for r in rows),
              'property_instances': sum(r['properties'] for r in rows),
              'unresolved_controls': sum(r['status'] != 'verified-in-model' for r in rows),
              'parser_controls': 3,
              'interpretation': 'bounded semantic proof generation; native/runtime edges are separate'}
    (args.output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'cases'}))


if __name__ == '__main__':
    main()
