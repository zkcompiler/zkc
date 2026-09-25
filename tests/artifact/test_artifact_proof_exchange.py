#!/usr/bin/env python3
"""Proofs the direct library and the native host each produce and the other accepts.

Both sides run the same construction. For the committed family the proof bytes
must be identical; for the family whose nonces the host seeds from the operating
system only the length can be, so what is compared there is that each accepts
what the other produced. Both must refuse a trailing byte and a changed
statement context.
"""
import json
import pathlib
from types import SimpleNamespace

from journal import Journal
from toolchain import Toolchain, records

# The Lean reference the native host is given to check participants with.
def main():
    CHECKER = "interactive-protocol"

    # The runtime's own direct implementation, which owes the host nothing.
    BASELINE = "artifact_baseline"

    ROOT = pathlib.Path(__file__).resolve().parents[2]

    tools = Toolchain()
    args = SimpleNamespace(zkc=tools.runtime, compiler=tools.compiler,
                              lean=tools.checker(CHECKER), baseline=tools.example(BASELINE))
    journal = Journal(records())
    out = journal.directory
    fixtures = ROOT / 'crates/zkc-tools/tests/fixtures/artifact'
    checks = []


    def run(argv, status, success=True):
        """Run one step of a family, and say which answer it owed."""
        result = journal.attempt(argv, text=False)
        assert result.returncode >= 0 and (result.returncode == 0) == success, (argv, result.stdout, result.stderr)
        value = json.loads(result.stdout)
        if status:
            assert value['status'] == status, value
        return value

    for name in ['dleq', 'committed-two-factor']:
        case = out / name
        case.mkdir(exist_ok=True)
        original = json.loads((fixtures / (name + '.json')).read_text())
        if name == 'committed-two-factor':
            original[4][0][3][0][1] = '1'
            original[4][2][3][0][1] = '1'
        source = journal.write(case / 'source.json', original)
        descriptor = journal.write(case / 'descriptor.json', json.loads(
            (fixtures / (name + '.construction.json')).read_text()))
        construction = run([args.compiler, 'protocol-construct', source, descriptor], None)
        constructed = journal.write(case / 'construction.json', construction)
        common = journal.write(case / 'common.json', construction[2])
        physical = journal.write(case / 'physical.json', run(
            [args.compiler, 'protocol-compile', common], None))
        direct_fixture = case / 'direct-fixture'
        run([args.baseline, 'fixture', source, descriptor, direct_fixture], 'fixture-generated')
        producer = direct_fixture / 'producer/inputs.json'
        validator = direct_fixture / 'validator/inputs.json'
        direct_proof = case / 'direct.proof'
        native_proof = case / 'native.proof'
        run([args.baseline, 'prove-development', source, descriptor, producer, direct_proof, '1'], 'proved')
        native_prefix = [args.zkc, 'validate-artifact', source, descriptor, constructed, physical]
        run(native_prefix + [validator, args.compiler, args.lean, direct_proof, '1000'], 'accepted')
        run([args.zkc, 'produce-artifact', source, descriptor, constructed, physical,
             producer, args.compiler, args.lean, native_proof, '1000'], 'produced')
        run([args.baseline, 'validate', source, descriptor, validator, native_proof, '1'], 'accepted')
        if name == 'committed-two-factor':
            assert direct_proof.read_bytes() == native_proof.read_bytes()
            checks.append(name + ': exact direct/native proof bytes')
        else:
            # Direct development nonces are public constants; native nonce issuance is OS seeded.
            assert len(direct_proof.read_bytes()) == len(native_proof.read_bytes())
        checks.extend([name + ': native accepts direct proof', name + ': direct accepts native proof'])
        bad = case / 'trailing.proof'
        bad.write_bytes(direct_proof.read_bytes() + b'\x00')
        run([args.baseline, 'validate', source, descriptor, validator, bad, '1'], 'refused', False)
        run(native_prefix + [validator, args.compiler, args.lean, bad, '1000'], 'refused', False)
        checks.append(name + ': both reject trailing proof bytes')
        changed = json.loads(validator.read_text())
        changed[1] = '00'
        changed_path = journal.write(case / 'changed-context.json', changed)
        run([args.baseline, 'validate', source, descriptor, changed_path, direct_proof, '1'], 'refused', False)
        run(native_prefix + [changed_path, args.compiler, args.lean, direct_proof, '1000'], 'refused', False)
        checks.append(name + ': both reject changed statement context')

    report = {'checks': checks, 'commands': journal.commands}
    journal.write(out / 'report.json', report)
    print(json.dumps({'passed': len(checks), 'commands': journal.save()}))



def test_artifact_proof_exchange():
    main()


if __name__ == "__main__":
    main()
