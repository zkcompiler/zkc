#!/usr/bin/env python3
"""Matrix source/MLIR/native/Lean differential checks with an integer oracle.

Run: matrix_contracts.py COMPILER OPTIMIZER RUNTIME LEAN OUTPUT_DIRECTORY
"""
import copy
import json
from pathlib import Path
import random

from journal import Journal
from toolchain import Toolchain, records
import sys

# The Lean reference these cases are compared against. Which reference a
# test uses is part of what the test is, not of how it is invoked.
def main():
    CHECKER = "interactive-protocol"

    tools = Toolchain()
    compiler = tools.compiler
    optimizer = tools.optimizer
    runtime = tools.runtime
    lean = tools.checker(CHECKER)
    output = records()

    root = Path(output)
    root.mkdir(parents=True, exist_ok=True)
    sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'tests/support'))
    from matrix_wire import FIELDS, encode_matrix, encode_matrix_json  # noqa: E402
    journal = Journal(output)
    helper = 0
    executions = 0

    def source(field, rows, columns, concrete=False):
        function = f'''fn Work<F: domain Field>(m:Matrix<F::Element>,x:Vector<F::Element>,y:Vector<F::Element>) -> (Vector<F::Element>,Vector<F::Element>,F::Element,bool) requires (Field(F)) {{
          [mv] let v = matrix::mul_vector::<F>(m,x);
          [tmv] let t = matrix::transpose_mul_vector::<F>(m,y);
          [bi] let b = matrix::bilinear::<F>(m,y,x);
          [sh] let s = matrix::shape_check::<F>(m) attributes ("{rows}","{columns}");
          return (v,t,b,s);
        }}
        configure Concrete = Work(F={field});'''
        if concrete:
            function = f'''bind M = matrix::mul_vector({field});
            bind T = matrix::transpose_mul_vector({field});
            bind B = matrix::bilinear({field});
            bind S = matrix::shape_check({field});
            fn Concrete(m:Matrix<{field}::Element>,x:Vector<{field}::Element>,y:Vector<{field}::Element>) -> (Vector<{field}::Element>,Vector<{field}::Element>,{field}::Element,bool) {{
              [mv] let v = M(m,x); [tmv] let t = T(m,y); [bi] let b = B(m,y,x);
              [sh] let s = S(m) attributes ("{rows}","{columns}"); return (v,t,b,s);
            }}'''
        return f'''module {{ {function}
          protocol Main {{ roles (P);
            inputs (P m:Matrix<{field}::Element>,P x:Vector<{field}::Element>,P y:Vector<{field}::Element>);
            outputs (P Vector<{field}::Element>,P Vector<{field}::Element>,P {field}::Element,P bool);
            local [call] P: let (v,t,b,s) = Concrete(m,x,y); return (v,t,b,s);
          }}
          instance concrete: Main {{roles (P=P);}} entry main = concrete;
        }}'''


    def pipeline(field, rows, columns, concrete=False):
        text = source(field, rows, columns, concrete)
        authored = json.loads(journal.run([compiler, 'protocol-source', '-'], text))
        plan = json.loads(journal.run([compiler, 'protocol-compile', '-'], text))
        logical = journal.run([compiler, 'protocol-import', '-'], text)
        assert '!algebra.matrix<' in logical and 'sparse-coo' not in logical
        for op in ['mul_vector', 'transpose_mul_vector', 'bilinear', 'shape_check']:
            assert 'algebra.matrix_' + op in logical
        optimized = journal.run([optimizer, '--verify-each', '--canonicalize', '--cse'], logical)
        for op in ['mul_vector', 'transpose_mul_vector', 'bilinear', 'shape_check']:
            assert 'algebra.matrix_' + op in optimized
        ir = journal.run([compiler, 'protocol-physical-ir', '-'], text)
        journal.run([optimizer, '--verify-each'], ir)
        assert 'sparse-coo/1' in ir
        assert json.loads(journal.run([compiler, 'protocol-export', '-'], ir)) == plan
        return authored, plan, ir, text


    def exercise(field, label, rows, columns, entries, x, y, failure=False, concrete=False):
        nonlocal executions
        directory = root / field / label
        directory.mkdir(parents=True, exist_ok=True)
        authored, plan, ir, text = pipeline(field, rows, columns, concrete)
        (directory / 'source.pir').write_text(text)
        sp = journal.write(directory / 'source.json', authored)
        pp = journal.write(directory / 'plan.json', plan)
        journal.run([lean, '--check-generic', sp, pp])
        matrix = [str(rows), str(columns), [[str(r), str(c), str(a)] for r, c, a in entries]]
        wire = encode_matrix(field, rows, columns, entries)
        assert wire == encode_matrix_json(field, matrix)
        native_input = ['zkc.run/2', 'main', 'matrix-test', [], [['P', [], [
            ['m', ['wire', wire.hex()]], ['x', ['vector', list(map(str, x))]],
            ['y', ['vector', list(map(str, y))]]], []]], []]
        ref_input = ['zkc.reference-inputs/1', 'main', 'matrix-test', [['P', [
            ['m', ['matrix:' + field, matrix]], ['x', ['vector:' + field, list(map(str, x))]],
            ['y', ['vector:' + field, list(map(str, y))]]]]], [], [], []]
        np = journal.write(directory / 'inputs.json', native_input)
        rp = journal.write(directory / 'reference-inputs.json', ref_input)
        native = json.loads(journal.run([runtime, 'run-protocol', sp, pp, np, lean]))
        reference = json.loads(journal.run([lean, '--generic-reference', sp, rp]))
        executions += 1
        journal.write(directory / 'native.json', native)
        journal.write(directory / 'lean.json', reference)
        if failure:
            assert native['stop']['detail'] == 'refused:matrix-shape', native
            assert reference[3][:2] == ['refused', 'matrix-shape'], reference
        else:
            _, width, p = FIELDS[field]
            # Mathematical dense coordinate formula, independent of native scatter
            # accumulation and the Lean COO filter/sum reference.
            dense = [[0] * columns for _ in range(rows)]
            for r, c, a in entries:
                dense[r][c] = a
            mv = [sum(dense[r][c] * x[c] for c in range(columns)) % p for r in range(rows)]
            tv = [sum(y[r] * dense[r][c] for r in range(rows)) % p for c in range(columns)]
            bi = sum(y[r] * dense[r][c] * x[c] for r in range(rows) for c in range(columns)) % p
            expected = [['vector:' + field, list(map(str, mv))], ['vector:' + field, list(map(str, tv))],
                        ['field:' + field, str(bi)], ['bool', 'true']]
            assert reference[3] == ['returned', expected], reference
            assert native['outcome'][0] == 'returned', native
            for output, values in zip(native['outcome'][1]['P'], [mv, tv, [bi], [1]], strict=True):
                if output[0] in ('field', 'bool'):
                    assert output[1] == (bool(values[0]) if output[0] == 'bool' else str(values[0])), output
                    continue
                assert output[0] == 'wire', output
                encoded = bytes.fromhex(output[2])
                if output[1] == 'bool':
                    assert encoded == b'ZKCV\x01\x05\x01'
                else:
                    body = encoded[10:] if output[1] == 'vector' else encoded[6:]
                    assert [int.from_bytes(body[i:i+width], 'little') for i in range(0, len(body), width)] == values
        assert native['resources'] == [] and native['wire']['messages'] == 0
        return directory, authored, plan, ir


    for field, (_, _, p) in FIELDS.items():
        rng = random.Random(82731)
        for rows, columns in [(0, 0), (0, 7), (9, 0), (1, 1), (5, 7), (17, 31), (73, 97)]:
            entries = [(r, c, rng.randrange(1, p)) for r in range(rows) for c in range(columns) if rng.randrange(5) == 0]
            x = [rng.randrange(p) for _ in range(columns)]
            y = [rng.randrange(p) for _ in range(rows)]
            directory, authored, plan, ir = exercise(field, f'random-{rows}-{columns}', rows, columns, entries, x, y)
            if rows == 73:
                assert len(json.dumps(plan)) < 6000
                assert len(encode_matrix(field, rows, columns, entries)) > 15000
        exercise(field, 'wraparound', 2, 3, [(0, 1, p-1), (1, 0, p-2), (1, 2, 3)], [p-1, 5, 7], [2, p-1], concrete=True)
        exercise(field, 'bad-columns', 2, 3, [(0, 1, 1)], [1, 2], [1, 2], failure=True)
        exercise(field, 'bad-rows', 2, 3, [(0, 1, 1)], [1, 2, 3], [1], failure=True)
        for bad, code in [('', 'expected-natural'), ('01', 'noncanonical-natural'),
                          ('-1', 'expected-natural'), ('65537', 'interactive-kernel-parameters'),
                          ('18446744073709551616', 'interactive-kernel-parameters')]:
            text = source(field, bad, 3)
            journal.run([compiler, 'protocol-import', '-'], text, code)
            # Mutate admitted common JSON so Lean checks the actual bad attribute.
            parsed = json.loads(journal.run([compiler, 'protocol-source', '-'], source(field, 2, 3)))
            parsed[1][0][6][3][4] = [bad, '3']
            path = journal.write(root / field / 'bad-attribute.json', parsed)
            journal.run([lean, '--generic-declarations', path], refuses='refused')
        # Independent signature admission catches a nominal matrix substitution.
        changed = copy.deepcopy(plan)
        other = next(d for d in FIELDS if d != field)
        changed[3][0][2][0][1] = changed[3][0][2][0][1].replace(field, other)
        path = journal.write(directory / 'bad-field-plan.json', changed)
        journal.run([lean, '--check-generic', str(directory / 'source.json'), path], refuses='refused')
        wrong = ir.replace('matrix<' + json.dumps(field) + '>', 'matrix<' + json.dumps(other) + '>', 1)
        assert wrong != ir
        journal.run([optimizer, '--verify-each'], wrong, 'binding')
        # Unknown matrix storage and legacy profile matrix typing fail closed.
        wrong = ir.replace('sparse-coo/1', 'invented-coo/1')
        journal.run([optimizer, '--verify-each'], wrong, 'binding')
        journal.run([compiler, 'protocol-import', '-'], source(field, 2, 3).replace('requires (Field(F))', ''), 'generic-public-requirement')

    # Helper refuses to repair caller mistakes or reduce coefficients.
    for rows, columns, es in [(2, 3, [(0, 1, 0)]), (2, 3, [(0, 1, 1), (0, 1, 2)]),
                               (2, 3, [(1, 1, 1), (0, 1, 2)]), (2, 3, [(0, 3, 1)]),
                               (65537, 0, []), (1, 1, [(0, 0, 2130706433)])]:
        try:
            encode_matrix('koala-bear', rows, columns, es)
        except ValueError:
            helper += 1
        else:
            raise AssertionError((rows, columns, es))
    print(f'matrix contracts: {journal.save() + helper} tool/helper checks; {executions} native/Lean/integer executions')



def test_matrix_contracts():
    main()


if __name__ == "__main__":
    main()
