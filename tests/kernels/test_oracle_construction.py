"""Source construction and independent artifact replay for authenticated queries.

Both field carriers share the construction and oracle interface. Exact events
include selected field/index draws, typed messages and authentication guards.
"""
import json
from pathlib import Path

from run_reference import run_reference
from journal import Journal
from toolchain import Toolchain, records

# The Lean reference these cases are compared against. Which reference a
# test uses is part of what the test is, not of how it is invoked.
def main():
    CHECKER = "interactive-protocol"

    tools = Toolchain()
    compiler = tools.compiler
    runtime = tools.runtime
    lean = tools.checker(CHECKER)
    output = records()

    repo = Path(__file__).resolve().parents[2]
    output.mkdir(parents=True, exist_ok=True)
    journal = Journal(output)



    def run(args, path, success=True):
        """Run a step, keeping what it printed at the path the next one reads.

        `success=False` is for a step this test judges itself, from the report
        rather than from the exit code.
        """
        result = journal.attempt(args, keep=path)
        assert result.returncode >= 0 and (not success or result.returncode == 0), (args, result.stdout, result.stderr)
        return json.loads(result.stdout)


    def index(n):
        return (b'ZKCV\x01\x1f' + n.to_bytes(8, 'little')).hex()


    for extension in (False, True):
        folder = output / ('extension' if extension else 'base')
        folder.mkdir(exist_ok=True)
        source_text = (repo / 'tests/fixtures/oracle-construction.pir').read_text()
        if extension:
            source_text = source_text.replace('rows.merkle-keccak256.koala-bear/1',
                'rows.merkle-keccak256.koala-bear.ext8-binomial3/1')
            source_text = source_text.replace('Vector<koala-bear::Element>', 'Vector<"koala-bear.ext8-binomial3"::Element>')
        source_path = folder / 'source.pir'
        source_path.write_text(source_text)
        descriptor_path = repo / 'tests/fixtures/oracle-construction.construction.pir'
        source = folder / 'source.json'
        descriptor = folder / 'descriptor.json'
        construction = folder / 'construction.json'
        plan = folder / 'plan.json'
        run([compiler, 'protocol-source', source_path], source)
        run([compiler, 'protocol-source', descriptor_path], descriptor)
        result = run([compiler, 'protocol-construct', source_path, descriptor_path], construction)
        common = journal.write(folder / 'common.json', result[2])
        run([compiler, 'protocol-compile', common], plan)
        field = 'koala-bear' + ('.ext8-binomial3' if extension else '')
        coordinates = [x for i in range(16) for x in ([i, i+1, 0, 0, 0, 0, 0, 0] if extension else [i])]
        wire = b'ZKCV\x01' + bytes([27 if extension else 20]) + (16).to_bytes(4, 'little')
        wire += b''.join(x.to_bytes(4, 'little') for x in coordinates)
        envelope = ['zkc.artifact-inputs/1', b'oracle-test'.hex(),
                    [['width', 'index', index(2)], ['height', 'index', index(8)]], [],
                    ['zkc.public-configuration/1', [], [], []]]
        validator = journal.write(folder / 'validator.json', envelope)
        envelope[3] = [['values', 'vector:'+field, wire.hex()]]
        producer = journal.write(folder / 'producer.json', envelope)
        shared = [source, descriptor, construction, plan]
        proof = folder / 'proof'
        run([runtime, 'produce-artifact', *shared, producer, compiler, lean,
             proof, 100000, '--trace=full'], folder / 'produce.json')

        def compare(label, candidate):
            actual = run([runtime, 'validate-artifact', *shared, validator, compiler, lean,
                          candidate, 100000, '--trace=full'], folder / (label+'.json'), False)
            expected = run_reference(
                lean.with_name('artifact-reference'), runtime.with_name('artifact-primitive'),
                source, descriptor, validator, candidate, folder / (label+'-reference'))
            assert expected[0] == 'zkc.artifact-observation/1', expected
            assert (actual['status'] == 'accepted') == (expected[1][0] == 'accepted'), label
            assert actual['events'] == expected[2], (label, 'event mismatch')
            if label == 'hash-change':
                assert actual['code'] == 'rejected:require', actual['code']
                assert expected[1][:2] == ['reject', 'require-false'], expected[1][:2]
            assert actual['candidate_bytes'] == len(candidate.read_bytes())
            if label == 'valid':
                assert actual['status'] == 'accepted', actual
                assert expected[4] == str(len(candidate.read_bytes())) or expected[4] == len(candidate.read_bytes())
            else:
                assert actual['status'] != 'accepted', actual

        compare('valid', proof)
        data = proof.read_bytes()
        for label, bad in [('hash-change', data[:-1]+bytes([data[-1]^1])),
                           ('truncated', data[:-1]), ('trailing', data+b'\0')]:
            path = folder / label
            path.write_bytes(bad)
            compare(label, path)

    print(json.dumps({'status': 'pass', 'checks': journal.save(), 'domains': 2,
                      'comparison': 'exact artifact events and terminal outcome'}))



def test_oracle_construction():
    main()


if __name__ == "__main__":
    main()
