#!/usr/bin/env python3
"""Public matrix root binding and original-source artifact reference checks."""
import copy
import json
from types import SimpleNamespace

from matrix_wire import FIELDS, encode_matrix
from run_reference import run_reference
from construction import constructed_plan
from journal import Journal
from toolchain import Toolchain, records

# The two Lean references this drives: one consumes the admitted source, the
# other interprets the artifact the runtime produced.
def main():
    CHECKER = "interactive-protocol"
    REFERENCE = "artifact-reference"

    tools = Toolchain()
    a = SimpleNamespace(zkc=tools.runtime, compiler=tools.compiler,
                           lean=tools.checker(CHECKER), reference=tools.checker(REFERENCE),
                           primitive=tools.primitive)
    journal = Journal(records(), timeout=120)
    checks = []

    def call(directory, label, argv, success=True):
        """Run one step of a case, keeping its output under that case's name."""
        result = journal.attempt(argv, text=False, keep=directory / label)
        if success:
            assert result.returncode == 0, (label, result.stderr.decode(), result.stdout.decode())
        return json.loads(result.stdout)


    def vector_wire(field, xs):
        tag = {'bls12-381.fr': 11, 'ristretto255.scalar': 14, 'koala-bear': 20}[field]
        width = FIELDS[field][1]
        return (b'ZKCV\x01' + bytes([tag]) + len(xs).to_bytes(4, 'little') +
                b''.join(x.to_bytes(width, 'little') for x in xs)).hex()


    for field in FIELDS:
        directory = journal.directory / field
        directory.mkdir(parents=True, exist_ok=True)
        transcript_field = field if field != 'koala-bear' else 'bls12-381.fr'
        suite = ('merlin3.ristretto255.scalar64le/1' if field == 'ristretto255.scalar'
                 else 'merlin3.bls12-381.fr64be/1')
        mt, vt, ft, ct = 'matrix:' + field, 'vector:' + field, 'field:' + field, 'field:' + transcript_field
        rng = 'rng:' + transcript_field
        bindings = [[key, op, args, ''] for key, op, args in [
            ('eval', 'matrix.bilinear', [field]), ('eq', 'field.equal', [field]),
            ('require', 'control.require', []), ('draw', 'random.draw', [transcript_field])]]
        def op(site, binding, attrs, inputs, outputs):
            return ['op', site, binding, attrs, inputs, outputs]
        def fn(name, inputs, outputs, body):
            return ['function', name, inputs, outputs, body, [name, []]]
        functions = [
            fn('Eval', [['m', mt], ['y', vt], ['x', vt]], [ft],
               [op('eval', 'eval', [], ['m', 'y', 'x'], ['b']), ['return', ['b']]]),
            fn('Check', [['expected', ft], ['actual', ft]], ['bool'],
               [op('eq', 'eq', [], ['expected', 'actual'], ['ok']),
                op('require', 'require', [], ['ok'], []), ['return', ['ok']]]),
            fn('Draw', [['rng', rng]], [ct, rng],
               [op('draw', 'draw', [], ['rng'], ['c', 'next']), ['return', ['c', 'next']]])]
        ports = [['mp', 'P', mt], ['yp', 'P', vt], ['xp', 'P', vt],
                 ['mv', 'V', mt], ['yv', 'V', vt], ['xv', 'V', vt], ['coins', 'V', rng]]
        body = [['local', 'product', 'P', 'Eval', ['mp', 'yp', 'xp'], ['product']],
                ['message', 'product_message', 'product', 'P', 'V', 'product', 'received'],
                ['local', 'challenge', 'V', 'Draw', ['coins'], ['c', 'after']],
                ['message', 'challenge_message', 'challenge', 'V', 'P', 'c', 'challenge'],
                ['local', 'expected', 'V', 'Eval', ['mv', 'yv', 'xv'], ['expected']],
                ['local', 'check', 'V', 'Check', ['expected', 'received'], ['ok']],
                ['return', ['ok', 'after']]]
        if field == 'koala-bear':
            # The installed BLS transcript cannot observe a KoalaBear scalar.
            # Use an ordinary Bool message while the public root binds KB matrix data.
            bindings += [['constant', 'field.constant', [field], ''], ['and', 'bool.and', [], '']]
            functions += [
                fn('Claim', [['value', ft]], ['bool'],
                   [op('target', 'constant', ['48'], [], ['target']),
                    op('claim', 'eq', [], ['value', 'target'], ['ok']), ['return', ['ok']]]),
                fn('Both', [['x', 'bool'], ['y', 'bool']], ['bool'],
                   [op('and', 'and', [], ['x', 'y'], ['ok']),
                    op('require', 'require', [], ['ok'], []), ['return', ['ok']]])]
            body[1:2] = [['local', 'claim', 'P', 'Claim', ['product'], ['flag']],
                         ['message', 'product_message', 'product', 'P', 'V', 'flag', 'received']]
            body[-2:-1] = [['local', 'expected_claim', 'V', 'Claim', ['expected'], ['expected_flag']],
                           ['local', 'check', 'V', 'Both', ['expected_flag', 'received'], ['ok']]]
        source = ['zkc.protocol/1', bindings, functions,
                  [['protocol', 'Main', ['P', 'V'], [], ports, [['V', 'bool'], ['V', rng]], [], body]],
                  [['instance', 'root', 'Main', [], [], [['P', 'P'], ['V', 'V']]]], [['entry', 'main', 'root']]]
        public = [['M', [['P', 'mp'], ['V', 'mv']]], ['Y', [['P', 'yp'], ['V', 'yv']]], ['X', [['P', 'xp'], ['V', 'xv']]]]
        descriptor = ['zkc.construction/1', 'main', 'P', 'V', public, ['coins', [['Draw', 'draw']]], '0', suite, 'normalized']
        src = journal.write(directory / 'source.json', source)
        desc = journal.write(directory / 'descriptor.json', descriptor)
        paths = constructed_plan(journal, a.compiler, src, desc, f'{directory}/')
        matrix = encode_matrix(field, 2, 3, [(0, 0, 5), (0, 1, 3), (1, 2, 7)]).hex()
        inputs = ['zkc.artifact-inputs/1', '', [
            ['M', mt, matrix], ['Y', vt, vector_wire(field, [2, 3])],
            ['X', vt, vector_wire(field, [0, 1, 2])]], [], ['zkc.public-configuration/1', [], [], []]]
        inp = journal.write(directory / 'inputs.json', inputs)
        proof = directory / 'proof.bin'
        produced = call(directory, 'produce', [a.zkc, 'produce-artifact', *paths, inp, a.compiler, a.lean, proof, '1000'])
        assert produced['status'] == 'produced', produced
        for label, change, expected in [
            ('honest', None, 'accepted'),
            ('same-result-matrix-substitution', encode_matrix(field, 2, 3, [(0, 0, 6), (0, 1, 3), (1, 2, 7)]).hex(), 'proof-header'),
            ('matrix-shape-substitution', encode_matrix(field, 3, 3, [(0, 0, 5), (0, 1, 3), (1, 2, 7)]).hex(), 'proof-header'),
        ]:
            candidate = copy.deepcopy(inputs)
            if change is not None:
                candidate[2][0][2] = change
            vi = journal.write(directory / (label + '.json'), candidate)
            native = call(directory, label, [a.zkc, 'validate-artifact', *paths, vi, a.compiler, a.lean, proof, '1000'], success=expected == 'accepted')
            refdir = directory / (label + '-reference')
            ref = run_reference(a.reference, a.primitive, src, desc, vi, proof, refdir)
            assert ref[0] == 'zkc.artifact-observation/1', ref
            if expected == 'accepted':
                assert native['status'] == ref[1][0] == 'accepted', (native, ref)
                assert native['binding_sha256'] == produced['binding_sha256']
                requests = json.loads((refdir / 'replies.json').read_text())[1]
                validations = [r[0] for r in requests if r[0][0] == 'zkc.public-primitive/1']
                assert not any(r[2].startswith('matrix.') for r in validations)
                request = journal.write(directory / 'validate-matrix.request.json', ['zkc.public-primitive/1', [], 'validate', [], [], [[mt, matrix]]])
                assert call(directory, 'validate-matrix-primitive', [a.primitive, request]) == ['ok']
                assert all(r[2] != 'matrix.bilinear' for r in validations) # Lean computes the matrix arithmetic.
            else:
                assert native['code'] == 'proof-header' and ref[1][:2] == ['refused', 'proof-header'], (native, ref)
                assert native['binding_sha256'] != produced['binding_sha256']
            assert native['events'] == ref[2], (native, ref)
            assert native['proof_bytes'] == int(ref[4]), (native, ref)
            checks.append([field, label, native['code'], ref[1], len(native['events'])])
        # Peer-controlled malformed matrix bytes fail before transcript work.
        for label, mutate in [
            ('zero', lambda b: b.__setitem__(slice(26, 26+FIELDS[field][1]), b'\0'*FIELDS[field][1])),
            ('wrong-field', lambda b: b.__setitem__(5, 23 + ((FIELDS[field][0]-23+1) % 3))),
            ('truncated', lambda b: b.pop()),
            ('duplicate', lambda b: b.__setitem__(slice(18+8+FIELDS[field][1], 26+8+FIELDS[field][1]), b[:0] + b[18:26])),
        ]:
            bad = bytearray.fromhex(matrix)
            mutate(bad)
            candidate = copy.deepcopy(inputs)
            candidate[2][0][2] = bad.hex()
            vi = journal.write(directory / (label + '.json'), candidate)
            native = call(directory, label, [a.zkc, 'validate-artifact', *paths, vi, a.compiler, a.lean, proof, '1000'], success=False)
            ref = run_reference(a.reference, a.primitive, src, desc, vi, proof, directory / (label + '-reference'))
            assert native['status'] == 'refused' and native.get('events', []) == [], native
            assert ref[0] == 'refused', ref
            checks.append([field, label, native['code'], ref[:2]])

    journal.write('checks.json', checks)
    print(json.dumps({'status': 'passed', 'checks': len(checks), 'fields': list(FIELDS)}))



def test_matrix_artifact():
    main()


if __name__ == "__main__":
    main()
