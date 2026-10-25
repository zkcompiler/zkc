#!/usr/bin/env python3
"""Exercise authored targets, external consumers and wrong-relation controls."""
import argparse
import copy
import json
from pathlib import Path
import subprocess
import sys

import intent
from verify import read_json, verify

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    compiler = args.compiler.resolve()
    spec = read_json(HERE / 'requests/schnorr-dsl.json')
    original = (ROOT / 'libraries/protocols/sigma/schnorr/lib.zkc').read_text()
    rows = []

    def invoke(name, request, source, expected):
        directory = output / name
        directory.mkdir(exist_ok=True)
        (directory / 'spec.json').write_text(json.dumps(request))
        (directory / 'library.zkc').write_text(source)
        command = [sys.executable, str(HERE / 'verify.py'), '--spec', str(directory / 'spec.json'),
            '--module=example=' + str(ROOT / 'examples/projects/schnorr/main.zkc'),
            '--module=schnorr=' + str(directory / 'library.zkc'), '--subject=schnorr::Schnorr<example::G>',
            '--compiler', str(compiler), '--output', str(directory)]
        run = subprocess.run(command, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=240)
        (directory / 'driver.log').write_text(run.stdout)
        receipt = read_json(directory / 'receipt.json')
        result = receipt['obligations'][0]['code'] if receipt['obligations'] else receipt['status']
        if not (result == expected):
            raise AssertionError((name, result, expected, directory))
        if not ((run.returncode == 0) == (result == 'verified-in-model')):
            raise AssertionError(name)
        rows.append({'case': name, 'result': result})
        print(json.dumps(rows[-1]), flush=True)
        return receipt, directory

    _, positive = invoke('authored-dlog', spec, original, 'verified-in-model')
    simulation = copy.deepcopy(spec)
    simulation['properties'] = ['honest-verifier-zero-knowledge']
    simulation['experiment'] = 'interactive.honest-verifier-view/0'
    invoke('authored-dlog-simulation', simulation, original, 'verified-in-model')
    false_relation = original.replace('return point == base * scalar;', 'return true;')
    if not (false_relation != original):
        raise AssertionError('bridges/common/intent_tests.py:54: false_relation != original')
    _, negative = invoke('true-is-not-dlog', spec, false_relation, 'correspondence-unproved')
    bad = copy.deepcopy(spec)
    bad['target']['clause'] = 'unknown'
    invoke('unknown-target', bad, original, 'intent-clause')
    bad = copy.deepcopy(spec)
    bad['target']['relation'] = 'arbitrary-opaque-relation/0'
    invoke('unknown-relation-adapter', bad, original, 'intent-relation-adapter')
    bad = copy.deepcopy(spec)
    bad['inputs']['key'] = 'base'
    invoke('duplicate-input-binding', bad, original, 'intent-inputs')
    bad = copy.deepcopy(spec)
    bad['role'] = 'unknown'
    invoke('unknown-role', bad, original, 'intent-role')
    bad = copy.deepcopy(spec)
    bad['wiring']['prover'] = 'unknown'
    invoke('unknown-prover', bad, original, 'intent-prover')
    swapped = original.replace('DLog<G>(in.base@V, in.point@V, in.scalar)',
                               'DLog<G>(in.point@V, in.base@V, in.scalar)')
    if not (swapped != original):
        raise AssertionError('bridges/common/intent_tests.py:73: swapped != original')
    invoke('swapped-target-operands', spec, swapped, 'intent-relation-bindings')
    # Corrupt the untrusted relation candidate while retaining the requested subject.
    data, request = read_json(negative / 'source.json'), read_json(negative / 'request.json')
    wrong, correct = read_json(negative / 'relation.json'), read_json(positive / 'relation.json')
    generator = intent.relation_candidate
    intent.relation_candidate = lambda _data, req: generator(correct, req)
    try:
        receipt = verify(data, request, output / 'wrong-relation-subject', relation=wrong)
        if not (receipt['status'] == 'unresolved'):
            raise AssertionError("bridges/common/intent_tests.py:82: receipt['status'] == 'unresolved'")
        log = (output / 'wrong-relation-subject/lean.log').read_text()
        if not ('PROOF-REQUEST-BOUNDARY-PASS' in log and 'error:' in log):
            raise AssertionError("bridges/common/intent_tests.py:84: 'PROOF-REQUEST-BOUNDARY-PASS' in log and 'error:' in log")
        rows.append({'case': 'wrong-relation-subject', 'result': 'refused'})
    finally:
        intent.relation_candidate = generator
    def changing_relation(data, request):
        data[8][:] = correct[8]
        return generator(data, request)
    intent.relation_candidate = changing_relation
    try:
        original_relation = copy.deepcopy(wrong)
        receipt = verify(data, request, output / 'changed-relation-input', relation=wrong)
        if not (receipt['status'] == 'unresolved'):
            raise AssertionError("bridges/common/intent_tests.py:95: receipt['status'] == 'unresolved'")
        if not (wrong == original_relation):
            raise AssertionError('bridges/common/intent_tests.py:96: wrong == original_relation')
        rows.append({'case': 'changed-relation-input', 'result': 'refused'})
    finally:
        intent.relation_candidate = generator
    # Independent external theorem reuse across all three admitted source forms.
    for family, forms, request_name in [('sumcheck', ['', '-helpers', '-horner'], 'sumcheck-arklib'),
                                        ('schnorr', ['', '-helpers', '-reordered'], 'schnorr-simulation')]:
        request = read_json(HERE / 'requests' / (request_name + '.json'))
        for form in forms:
            name = 'external-' + family + (form or '-original')
            receipt = verify(read_json(ROOT / 'lean/ZkcExamples/NativePrograms/fixtures' / (family + form + '.json')),
                             request, output / name)
            if not (receipt['status'] == 'verified-in-model'):
                raise AssertionError((name, receipt))
            rows.append({'case': name, 'result': receipt['status']})
            print(json.dumps(rows[-1]), flush=True)
    (output / 'result.json').write_text(json.dumps({'status': 'pass', 'cases': rows}, indent=2) + '\n')


if __name__ == '__main__':
    main()
