#!/usr/bin/env python3
"""Compare independent Rust/Lean identities with handwritten expected trees."""
import copy
import hashlib
import json
from pathlib import Path

from journal import Journal
from toolchain import Toolchain, records


# The independent Lean identity implementation. The interactive reference has no
# identity command and refuses these descriptors, so the name belongs here.
REFERENCE = "artifact-reference"


# The handwritten vectors these implementations are compared against.
VECTORS = Path(__file__).resolve().parents[2] / 'tests/fixtures/identity-vectors'


def main():
    tools = Toolchain()
    host, compiler = tools.runtime, tools.compiler
    reference = tools.checker(REFERENCE)
    journal = Journal(records())
    report_path = journal.directory / 'report.json'
    cases = []
    refusals = []
    for source in sorted(VECTORS.glob('*.source.json')):
        name = source.name.removesuffix('.source.json')
        paths = [source, VECTORS / (name + '.descriptor.json')]
        config = VECTORS / (name + '.configuration.json')
        if config.exists():
            paths.append(config)
        reports = []
        for tool, command in [(host, 'inspect-artifact-identity'),
                              (reference, 'identity')]:
            result = journal.attempt([tool, command, *paths], timeout=30)
            assert result.returncode == 0, (name, result.stdout, result.stderr)
            reports.append(json.loads(result.stdout))
        rust, lean = reports
        assert rust['admission'] == 'not-checked'
        assert lean[0] == 'zkc.identity-inspection/1'
        assert lean[1:4] == [rust[k] for k in ('resolved_source', 'resolved_descriptor',
                                             'normalized_protocol')], name
        expected = (VECTORS / (name + '.normalized.json')).read_bytes()
        assert lean[3] == json.loads(expected), name
        if config.exists():
            assert lean[4] == rust['resolved_configuration'], name
        native = journal.attempt([compiler, 'protocol-import', source], timeout=30)
        assert native.returncode == 0, (name, native.stderr)
        original = json.loads(source.read_text())
        for mutation in ('empty-origin', 'duplicate-symbol'):
            malformed = copy.deepcopy(original)
            common = malformed[3] if malformed[0] == 'zkc.library/1' else malformed
            if mutation == 'empty-origin':
                common[2][0][5] = []
            else:
                common[1].append([common[3][0][1], 'bool.and', [], ''])
            tmp = journal.directory / name / mutation
            tmp.mkdir(parents=True, exist_ok=True)
            invalid = Path(tmp) / 'source.json'
            invalid.write_text(json.dumps(malformed))
            for tool, command, extra in (
                    (compiler, 'protocol-import', []),
                    (host, 'inspect-artifact-identity', paths[1:]),
                    (reference, 'identity', paths[1:])):
                result = journal.attempt([tool, command, invalid, *extra], timeout=30)
                assert result.returncode > 0, (name, mutation, tool,
                                               result.stdout, result.stderr)
            refusals.append({'name': name, 'mutation': mutation,
                             'cpp_rust_lean': 'refused'})
        cases.append({'name': name, 'status': 'equal',
                      'handwritten_expected_sha256': hashlib.sha256(expected).hexdigest()})
    assert len(cases) == 4, 'all four independent vector families must be present'
    report = {'status': 'pass', 'cases': cases, 'carrier_controls': refusals, 'tools': {
        name: {'path': str(tool), 'sha256': hashlib.sha256(tool.read_bytes()).hexdigest()}
        for name, tool in [('cpp', compiler), ('rust', host),
                           ('lean', reference)]}}
    report_path.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'status': 'pass', 'families': len(cases)}))



def test_identity_reference():
    main()

if __name__ == '__main__':
    main()
