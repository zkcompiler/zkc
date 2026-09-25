#!/usr/bin/env python3
"""Check the retained Lean executables against finite, explicit expected outcomes."""

import argparse
import importlib.util
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import support.evidence  # noqa: E402

import support.lake
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parents[1]




def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def check(formal):
    binaries = formal / '.lake/build/bin'
    source = load('source_controls', Path(__file__).resolve().parents[1] / 'source_plan_controls.py')
    direct = source.check(binaries / 'source-plan-example')
    # The shared harness inventories the live checkout; bind these results to
    # the selected package explicitly, including its executable examples.
    direct['source_sha256'] = {
        str(p.relative_to(formal)): support.lake.sha(p)
        for folder in ['Zkc', 'Tests', 'Examples', 'Tools']
        for p in sorted((formal / folder).rglob('*.lean'))}
    cases = []
    with tempfile.TemporaryDirectory(prefix='zkc-round-controls-') as temporary:
        directory = Path(temporary)
        paths = [str(directory / name) for name in ['request.json', 'plan.json', 'certificate.json']]
        tool = binaries / 'interactive-round'
        written = subprocess.run([str(tool), 'write', *paths], capture_output=True, text=True, timeout=30)
        if written.returncode or written.stdout or written.stderr:
            raise AssertionError(written)

        def expect(name, arguments, expected, code=0):
            result = subprocess.run([str(tool), *arguments], capture_output=True, text=True, timeout=30)
            actual = json.loads(result.stdout)
            if result.returncode != code or result.stderr or actual != expected:
                raise AssertionError((name, result.returncode, result.stderr, actual, expected))
            cases.append({'name': name, 'status': 'pass', 'response': actual})

        expect('source-check', ['check', *paths[:2]],
               {'status': 'checked', 'claim': 'complete-logical-execution'})
        expect('phase-admission', ['admit', *paths],
               {'status': 'admitted', 'profile': 'interactive-round/1',
                'claim': 'phase-conformance-and-normal-return'})
        events = [['commit', 5], ['challenge'], ['respond', 11],
                  ['commit', 11], ['challenge'], ['respond', 14],
                  ['commit', 14], ['challenge'], ['respond', 17]]
        expect('three-round-success', ['run', *paths, 'true', '5'],
               {'status': 'executed', 'outcome': ['returned', 17], 'phase': 'ready', 'state': 9,
                'events': events, 'calls': list(map(list, zip(['ready', 'committed', 'challenged'] * 3, events)))})
        expect('failed-first-call', ['run', *paths, 'true', '0'],
               {'status': 'executed', 'outcome': ['stopped', 'abort'], 'phase': 'ready', 'state': 1,
                'events': [['commit', 0]], 'calls': [['ready', ['commit', 0]]]})
        expect('source-rejection', ['run', *paths, 'false', '5'],
               {'status': 'executed', 'outcome': ['stopped', 'reject'], 'phase': 'ready', 'state': 0,
                'events': [], 'calls': []})
        certificate = json.loads(Path(paths[2]).read_text())
        certificate[1][1] = ['committed']
        Path(paths[2]).write_text(json.dumps(certificate))
        expect('wrong-loop-phase', ['admit', *paths],
               {'status': 'refused', 'code': 'phase-not-admitted'}, 1)
    # The relation reference: the library under it is proved in
    # Tests/RelationTransport.lean, so what is left to check is the command --
    # its arity, its three exit codes, and the framing it answers in.
    relations = []
    with tempfile.TemporaryDirectory(prefix='zkc-relation-reference-') as temporary:
        directory = Path(temporary)
        relation = ROOT / 'examples/relations/multiply.r1cs.json'

        def write(name, value):
            path = directory / name
            path.write_text(json.dumps(value))
            return str(path)

        # z = [1, 6, 2, 3] over the multiply relation: 2 * 3 = 6, and the
        # statement is the public prefix the assignment has to answer.
        assignment = write('assignment.json', ['1', '6', '2', '3'])
        answered = write('statement.json', ['6'])
        other = write('other.json', ['1'])
        malformed = directory / 'malformed.json'
        malformed.write_text('not json')
        for name, args, expected, code in [
            ('satisfied', [str(relation), answered, assignment],
             {'bound': True, 'products': [['2'], ['3'], ['6']], 'satisfied': True}, 0),
            ('statement-not-answered', [str(relation), other, assignment],
             {'bound': False, 'products': [['2'], ['3'], ['6']], 'satisfied': False}, 0),
            ('malformed-relation', [str(malformed), answered, assignment],
             {'status': 'refused', 'code': 'relation-json'}, 1),
            ('absent-relation', [str(directory / 'nothing.json'), answered, assignment],
             {'status': 'refused', 'code': 'relation-io'}, 1),
        ]:
            got = subprocess.run([str(binaries / 'relation-reference'), *args],
                                 capture_output=True, text=True, timeout=30)
            if got.returncode != code or json.loads(got.stdout) != expected:
                raise AssertionError((name, got.returncode, got.stdout, got.stderr))
            relations.append({'name': name, 'exit': code, 'answer': expected})
        usage = subprocess.run([str(binaries / 'relation-reference'), str(relation)],
                               capture_output=True, text=True, timeout=30)
        if usage.returncode != 2 or 'usage:' not in usage.stderr or usage.stdout:
            raise AssertionError(('relation-reference arity', usage))
        relations.append({'name': 'wrong-arity', 'exit': 2, 'answer': 'usage'})
    result = subprocess.run([str(binaries / 'block-checker'), str(ROOT / 'tests/fixtures/blocks/blocks.json')],
                            capture_output=True, text=True, timeout=30)
    blocks = [json.loads(line) for line in result.stdout.splitlines()]
    expected = [json.loads(line) for line in (ROOT / 'tests/fixtures/blocks/block-results.jsonl').read_text().splitlines()]
    if result.returncode or result.stderr or blocks != expected:
        raise AssertionError(('block controls', result, expected))
    return {
        'format': 'zkc.formal-tool-controls.v1', 'status': 'pass',
        'cases': direct['cases'] + len(cases) + len(blocks) + len(relations),
        'source_plan': direct, 'interactive_round': cases, 'blocks': blocks,
        'relation_reference': relations,
        'executable_sha256': {name: support.lake.sha(binaries / name) for name in
                              ['source-plan-example', 'interactive-round', 'block-checker',
                               'relation-reference']},
        'harness_sha256': {str(p.relative_to(ROOT)): support.lake.sha(p) for p in
                          [Path(__file__), Path(__file__).resolve().parents[1] / 'source_plan_controls.py',
                           ROOT / 'tests/fixtures/blocks/blocks.json', ROOT / 'tests/fixtures/blocks/block-results.jsonl']},
        'scope': 'finite compiled-tool checks, including failure state and exact ordered calls/events; '
                 'not a parser, Lean code-generator, C++/Rust or protocol-security theorem',
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--formal', type=Path, default=ROOT / 'formal')
    parser.add_argument("--output", type=Path,
                        default=support.evidence.records("tools", ".json"))
    args = parser.parse_args()
    result = check(args.formal.resolve())
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'status': result['status'], 'cases': result['cases']}))
