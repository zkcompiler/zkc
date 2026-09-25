#!/usr/bin/env python3
"""Compare vector assembly through source/MLIR, native execution and Lean.

Run: vector_scatter.py COMPILER OPTIMIZER RUNTIME LEAN OUTPUT_DIRECTORY
The integer sparse matrix oracle does not evaluate compiler operations.
"""
import copy
import json
from pathlib import Path
import random

from journal import Journal
from toolchain import Toolchain, records

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
    journal = Journal(output)

    root = Path(output)
    root.mkdir(parents=True, exist_ok=True)
    DOMAINS = [
        ('bls12-381.fr', 52435875175126190479447740508185965837690552500527637822603658699938581184513, 11, 32),
        ('ristretto255.scalar', 2**252 + 27742317777372353535851937790883648493, 14, 32),
        ('koala-bear', 2130706433, 20, 4),
    ]

    def attributes(values):
        return ', '.join(json.dumps(str(v)) for v in values)


    def constant(name, values):
        return f'[{name}] let ({name}) = vector::constant::<F>() attributes ({attributes(values)});'


    def scatter(name, values, length, indices):
        return f'[{name}] let ({name}) = vector::scatter_sum::<F>({values}) attributes ({attributes([length, *indices])});'


    def source(domain, body):
        return f'''module {{
          fn Work<F: domain Field>() -> (Vector<F::Element>) requires (Field(F)) {{
            {body}
            return (result);
          }}
          configure Concrete = Work(F = {domain});
          protocol Main {{
            roles (P); inputs (); outputs (P Vector<{domain}::Element>);
            local [call] P: let out = Concrete(); return (out);
          }}
          instance concrete: Main {{ roles (P = P); }}
          entry main = concrete;
        }}'''


    def exercise(domain, label, body, expected=None, failure=None):
        field, modulus, tag, width = domain
        directory = root / field / label
        directory.mkdir(parents=True, exist_ok=True)
        text = source(field, body)
        (directory / 'source.pir').write_text(text)
        authored = json.loads(journal.run([compiler, 'protocol-source', '-'], text))
        plan = json.loads(journal.run([compiler, 'protocol-compile', '-'], text))
        ir = journal.run([compiler, 'protocol-physical-ir', '-'], text)
        journal.run([optimizer, '--verify-each'], ir)
        assert json.loads(journal.run([compiler, 'protocol-export', '-'], ir)) == plan
        sp = journal.write(directory / 'source.json', authored)
        pp = journal.write(directory / 'plan.json', plan)
        journal.run([lean, '--check-generic', sp, pp])
        rp = journal.write(directory / 'reference-inputs.json',
                   ['zkc.reference-inputs/1', 'main', 'vector-assembly', [['P', []]], [], [], []])
        np = journal.write(directory / 'inputs.json',
                   ['zkc.run/2', 'main', 'vector-assembly', [], [['P', [], [], []]], []])
        reference = json.loads(journal.run([lean, '--generic-reference', sp, rp]))
        native = json.loads(journal.run([runtime, 'run-protocol', sp, pp, np, lean]))
        journal.write(directory / 'lean.json', reference)
        journal.write(directory / 'native.json', native)
        assert native['resources'] == [] and native['wire']['messages'] == 0
        if failure:
            lcode, ncode = failure
            assert reference[3][:2] == ['refused', lcode], reference
            assert native['outcome'][0] == 'stopped' and native['stop']['detail'] == ncode, native
        else:
            assert reference[3] == ['returned', [['vector:' + field, list(map(str, expected))]]], reference
            assert native['outcome'][0] == 'returned', native
            value = native['outcome'][1]['P'][0]
            assert value[:2] == ['wire', 'vector'], value
            wire = bytes.fromhex(value[2])
            assert wire[:6] == b'ZKCV\x01' + bytes([tag])
            count = int.from_bytes(wire[6:10], 'little')
            assert len(wire) == 10 + width * count
            actual = [int.from_bytes(wire[10 + width*i:10 + width*(i+1)], 'little') for i in range(count)]
            assert actual == expected and all(0 <= n < modulus for n in actual), actual
        return authored, plan, ir


    for domain in DOMAINS:
        field, p, _, _ = domain
        for label, values, n, indices, expected in [
            ('empty', [], 0, [], []),
            ('zero-fill', [], 4, [], [0, 0, 0, 0]),
            ('collision', [5, 7, 9], 4, [2, 0, 2], [7, 0, 14, 0]),
            ('reduce-literals', [p - 1, p + 2, 10**120 + p], 2, [0, 0, 1], [1, 10**120 % p]),
        ]:
            authored, plan, ir = exercise(domain, label, constant('values', values) + scatter('result', 'values', n, indices), expected)
            if label == 'reduce-literals':
                attrs = plan[3][0][4][0][3]
                assert attrs == list(map(str, [p - 1, 2, 10**120 % p])), attrs
                bad = ir.replace('parameters = ["' + str(p - 1) + '"', 'parameters = ["' + str(p) + '"', 1)
                assert bad != ir
                journal.run([optimizer, '--verify-each'], bad, 'interactive-constant')
                changed = copy.deepcopy(plan)
                changed[3][0][4][0][3][-1] = str(p)
                directory = root / field / label
                badpath = journal.write(directory / 'noncanonical-plan.json', changed)
                journal.run([lean, '--check-generic', str(directory / 'source.json'), badpath], refuses='interactive-constant')
        for label, n, indices, values, lcode, ncode in [
            ('missing-index', 2, [0], [3, 4], 'vector-shape', 'refused:length-mismatch'),
            ('extra-index', 2, [0, 0], [3], 'vector-shape', 'refused:length-mismatch'),
            ('late-index', 2, [0, 2], [3, 4], 'vector-index', 'refused:vector-index'),
            ('zero-index', 0, [0], [3], 'vector-index', 'refused:vector-index'),
        ]:
            exercise(domain, label, constant('values', values) + scatter('result', 'values', n, indices), failure=(lcode, ncode))
        # A sparse matrix and its transpose share exactly the new ordinary operations.
        rng = random.Random(731)
        rows, columns = 5, 7
        entries = [(rng.randrange(rows), rng.randrange(columns), rng.randrange(p)) for _ in range(23)]
        assignment = [rng.randrange(p) for _ in range(columns)]
        weights = [rng.randrange(p) for _ in range(rows)]
        for transpose, vector in [(False, assignment), (True, weights)]:
            length = columns if transpose else rows
            gather = [r if transpose else c for r, c, _ in entries]
            indices = [c if transpose else r for r, c, _ in entries]
            expected = [sum(a * vector[r if transpose else c] for r, c, a in entries
                            if (c if transpose else r) == i) % p for i in range(length)]
            body = constant('input', vector) + constant('coefficients', [a for _, _, a in entries])
            body += f'[gather] let selected = vector::gather::<F>(input) attributes ({attributes(gather)});'
            body += '[multiply] let products = vector::mul::<F>(selected, coefficients);'
            body += scatter('result', 'products', length, indices)
            exercise(domain, 'transpose' if transpose else 'matrix', body, expected)
        # A valid binding in a different field cannot consume the constant vector.
        directory = root / field / 'collision'
        changed = json.loads((directory / 'plan.json').read_text())
        other, provider = ('koala-bear', 'plonky3') if field != 'koala-bear' else ('bls12-381.fr', 'arkworks')
        changed[1][1][2] = [other]
        changed[1][1][3] = provider + '/vector.scatter_sum'
        badpath = journal.write(directory / 'field-mismatch-plan.json', changed)
        journal.run([lean, '--check-generic', str(directory / 'source.json'), badpath], refuses='binding-operation-signature')
        # The readable bound spelling has the same canonical ABI.
        bound = f'''module {{
          bind Constant = vector::constant({field});
          bind Scatter = vector::scatter_sum({field});
          fn Work() -> (Vector<{field}::Element>) {{
            [c] let v = Constant() attributes ("0", "7");
            [s] let r = Scatter(v) attributes ("1", "0", "0"); return (r);
          }}
          protocol Main {{ roles (P); inputs (); outputs (P Vector<{field}::Element>);
            local [call] P: let out = Work(); return (out); }}
          instance concrete: Main {{ roles (P = P); }} entry main = concrete;
        }}'''
        journal.run([compiler, 'protocol-compile', '-'], bound)
        journal.run([compiler, 'protocol-import', '-'], bound.replace('"0", "7"', f'"0", "{p}"'), 'interactive-constant')
        for bad, code in [('01', 'generic-field-literal'), ('-1', 'generic-field-literal')]:
            malformed = source(field, constant('result', [bad]))
            journal.run([compiler, 'protocol-import', '-'], malformed, code)
            parsed = json.loads(journal.run([compiler, 'protocol-source', '-'], source(field, constant('result', [0]))))
            parsed[1][0][6][0][4] = [bad]
            path = journal.write(root / field / 'bad-literal.json', parsed)
            journal.run([lean, '--generic-declarations', path], refuses='refused')
        for attrs, code in [([], 'interactive-kernel-parameters'),
                            (['01'], 'noncanonical-natural'),
                            (['1', '-1'], 'expected-natural'),
                            (['18446744073709551616'], 'interactive-kernel-parameters')]:
            malformed = source(field, constant('values', []) +
                f'[scatter] let result = vector::scatter_sum::<F>(values) attributes ({attributes(attrs)});')
            journal.run([compiler, 'protocol-import', '-'], malformed, code)
            parsed = json.loads(journal.run([compiler, 'protocol-source', '-'],
                source(field, constant('values', []) + scatter('result', 'values', 0, []))))
            parsed[1][0][6][1][4] = attrs
            path = journal.write(root / field / 'bad-shape.json', parsed)
            journal.run([lean, '--generic-declarations', path], refuses='refused')

    print(f'vector scatter: {journal.save()} tool checks; 30 native/Lean/integer executions across three fields')



def test_vector_scatter():
    main()


if __name__ == "__main__":
    main()
