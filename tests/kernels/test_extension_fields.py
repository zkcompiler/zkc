#!/usr/bin/env python3
"""Nominal octic source/MLIR/native/Lean differential checks.

Run: extension_fields.py COMPILER OPTIMIZER RUNTIME LEAN OUTPUT_DIRECTORY
The integer coordinate oracle implements convolution modulo X^8-3 independently.
"""
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

    root = Path(output)
    journal = Journal(root)
    P = 2130706433
    EXT = 'koala-bear.ext8-binomial3'
    ZERO = [0] * 8
    ONE = [1] + [0] * 7
    X = [0, 1] + [0] * 6
    X7 = [0] * 7 + [1]

    def mul(a, b):
        out = [0] * 15
        for i in range(8):
            for j in range(8):
                out[i+j] += a[i] * b[j]
        for i in range(8, 15):
            out[i-8] += 3*out[i]
        return [x % P for x in out[:8]]


    def add(a, b):
        return [(x+y) % P for x, y in zip(a, b, strict=True)]


    def power(a, n):
        result = ONE
        while n:
            if n % 2:
                result = mul(result, a)
            a, n = mul(a, a), n // 2
        return result


    def coordinate_wire(a):
        return b''.join(x.to_bytes(4, 'little') for x in a)


    def wire(kind, value):
        tag = {'field': 26, 'vector': 27, 'polynomial': 28, 'round': 29, 'matrix': 30}[kind]
        header = b'ZKCV\x01' + bytes([tag])
        if kind == 'field':
            return header + coordinate_wire(value)
        if kind == 'matrix':
            rows, columns, entries = value
            return header + b''.join(n.to_bytes(4, 'little') for n in [rows, columns, len(entries)]) + b''.join(
                r.to_bytes(4, 'little') + c.to_bytes(4, 'little') + coordinate_wire(a) for r, c, a in entries)
        return header + (len(value).to_bytes(4, 'little') if kind != 'round' else b'') + b''.join(map(coordinate_wire, value))


    def strings(value):
        return [strings(x) for x in value] if isinstance(value, list) else str(value)


    text = f'''module {{
      fn Work<E: domain Field>(a:E::Element,b:E::Element,k:E::BaseField::Element,xs:Vector<E::Element>,m:Matrix<E::Element>,q:Round<E>)
          -> (E::Element,E::Element,E::Element,Vector<E::Element>,E::Element,E::Element,E::Element,Vector<E::Element>,Vector<E::Element>,E::Element,E::Element)
          requires (ExtensionField(E)) {{
        [mul] let product = field::mul::<E>(a,b);
        [inv] let inverse = field::inverse::<E>(a);
        [embed] let embedded = field::embed::<E>(k);
        [scale] let scaled = vector::scale::<E>(xs,b);
        [dot] let dot = vector::dot::<E>(xs,scaled);
        [coeff] let poly = poly::from_coefficients::<E>(xs);
        [eval] let evaluated = poly::univariate_evaluate::<E>(poly,a);
        [round] let round = poly::round_evaluate::<E>(q,a);
        [matrix] let mv = matrix::mul_vector::<E>(m,xs);
        [transpose] let tmv = matrix::transpose_mul_vector::<E>(m,xs);
        [bilinear] let bilinear = matrix::bilinear::<E>(m,xs,xs);
        [constant] let constant = field::constant::<E>() attributes ("{P + 7}");
        return (product,inverse,embedded,scaled,dot,evaluated,round,mv,tmv,bilinear,constant);
      }}
      configure Concrete = Work(E={EXT});
      protocol Main {{ roles (P);
        inputs (P a:{EXT}::Element,P b:{EXT}::Element,P k:koala-bear::Element,P xs:Vector<{EXT}::Element>,P m:Matrix<{EXT}::Element>,P q:Round<{EXT}>);
        outputs (P {EXT}::Element,P {EXT}::Element,P {EXT}::Element,P Vector<{EXT}::Element>,P {EXT}::Element,P {EXT}::Element,P {EXT}::Element,P Vector<{EXT}::Element>,P Vector<{EXT}::Element>,P {EXT}::Element,P {EXT}::Element);
        local [work] P: let (product,inverse,embedded,scaled,dot,evaluated,round,mv,tmv,bilinear,constant) = Concrete(a,b,k,xs,m,q);
        return (product,inverse,embedded,scaled,dot,evaluated,round,mv,tmv,bilinear,constant);
      }}
      instance concrete: Main {{roles (P=P);}} entry main=concrete;
    }}'''
    (root / 'source.pir').write_text(text)
    authored = json.loads(journal.run([compiler, 'protocol-source', '-'], text))
    plan = json.loads(journal.run([compiler, 'protocol-compile', '-'], text))
    logical = journal.run([compiler, 'protocol-import', '-'], text)
    assert 'algebra.embed' in logical
    journal.run([optimizer, '--verify-each'], logical)
    physical = journal.run([compiler, 'protocol-physical-ir', '-'], text)
    journal.run([optimizer, '--verify-each'], physical)
    assert json.loads(journal.run([compiler, 'protocol-export', '-'], physical)) == plan
    sp, pp = journal.write('source.json', authored), journal.write('plan.json', plan)
    journal.run([lean, '--check-generic', sp, pp])


    def exercise(label, a, b, k, xs, entries, q, failure=False):
        matrix = [2, 2, entries]
        supplied = [('a', 'field', a), ('b', 'field', b), ('xs', 'vector', xs), ('m', 'matrix', matrix), ('q', 'round', q)]
        native = [[name, ['wire', wire(kind, value).hex()]] for name, kind, value in supplied]
        reference = [[name, [kind + ':' + EXT, strings(value)]] for name, kind, value in supplied]
        native.append(['k', ['field', str(k)]])
        reference.append(['k', ['field:koala-bear', str(k)]])
        np = journal.write(label + '-inputs.json', ['zkc.run/2', 'main', 'extension-test', [], [['P', [], native, []]], []])
        rp = journal.write(label + '-reference.json', ['zkc.reference-inputs/1', 'main', 'extension-test', [['P', reference]], [], [], []])
        ref = json.loads(journal.run([lean, '--generic-reference', sp, rp]))
        actual = json.loads(journal.run([runtime, 'run-protocol', sp, pp, np, lean]))
        journal.write(label + '-lean.json', ref)
        journal.write(label + '-native.json', actual)
        if failure:
            assert ref[3][:2] == ['refused', 'inverse-zero'], ref
            assert actual['outcome'][0] == 'stopped' and actual['stop']['detail'] == 'refused:zero-inverse', actual
            return
        scaled = [mul(x, b) for x in xs]
        dot = add(mul(xs[0], scaled[0]), mul(xs[1], scaled[1]))
        evaluated = add(xs[0], mul(a, xs[1]))
        round_eval = add(q[0], mul(a, add(q[1], mul(a, q[2]))))
        mv, tmv = [ZERO[:], ZERO[:]], [ZERO[:], ZERO[:]]
        for r, c, coefficient in entries:
            mv[r] = add(mv[r], mul(coefficient, xs[c]))
            tmv[c] = add(tmv[c], mul(coefficient, xs[r]))
        expected = [('field', mul(a,b)), ('field', power(a,P**8-2)), ('field', [k]+[0]*7),
                    ('vector', scaled), ('field', dot), ('field', evaluated), ('field', round_eval),
                    ('vector', mv), ('vector', tmv), ('field', add(mul(xs[0],mv[0]),mul(xs[1],mv[1]))), ('field',[7]+[0]*7)]
        assert ref[3] == ['returned', [[kind+':'+EXT, strings(value)] for kind, value in expected]], ref[3]
        assert actual['outcome'] == ['returned', {'P': [['wire',kind,wire(kind,value).hex()] for kind,value in expected]}], actual['outcome']
        assert actual['wire']['messages'] == 0 and actual['resources'] == []


    exercise('wrap', X, X7, P-1, [X, X7], [[0,1,X7],[1,0,X]], [X7,ONE,X])
    rng = random.Random(917)
    for i in range(4):
        def value():
            return [rng.randrange(P) for _ in range(8)]
        exercise('random'+str(i), value(), value(), rng.randrange(P), [value(),value()],
                 [[0,0,value()],[0,1,value()],[1,0,value()],[1,1,value()]], [value(),value(),value()])
    exercise('zero-inverse', ZERO, X, 1, [X,X7], [[0,1,X]], [ONE,X,X7], True)

    # Capability distinction and associated-base typing at source formation.
    for label, bad, code in [
        ('prime', text.replace('ExtensionField(E)', 'PrimeField(E), ExtensionField(E)'), 'source-protocol-requirement'),
        ('missing-extension', text.replace('ExtensionField(E)', 'Field(E)'), 'generic-public-requirement'),
        ('implicit-base', text.replace('field::mul::<E>(a,b)', 'field::mul::<E>(a,k)'), 'source-static-conflict'),
        ('wrong-base', text.replace('P k:koala-bear::Element', 'P k:"bls12-381.fr"::Element'), 'source-call-type'),
    ]:
        (root / (label + '.pir')).write_text(bad)
        journal.run([compiler, 'protocol-source', '-'], bad, code)

    # A bound operation must carry a canonical embedded constant below p.
    bad = physical.replace('parameters = ["7"]', f'parameters = ["{P}"]')
    assert bad != physical
    journal.run([optimizer, '--verify-each'], bad, 'interactive-constant')

    # Lean checks capabilities independently of C++ on the retained source document.
    # Add the deliberately unsatisfied promise to common JSON for independent Lean admission.
    prime = json.loads(journal.run([compiler, 'protocol-source', '-'], text))
    prime[1][0][3].insert(0, ['PrimeField', ['E']])
    prime_path = journal.write('prime-source.json', prime)
    journal.run([lean, '--check-generic', prime_path, pp], refuses='binding-requirement')

    # Actual participant transport decodes extension scalars through the same ZKCV envelope.
    transport = f'''module {{
      fn Multiply<F: domain Field>(a:F::Element,b:F::Element) -> (F::Element) requires (Field(F)) {{
        let r = field::mul::<F>(a,b); return (r);
      }}
      fn Check<F: domain Field>(a:F::Element,b:F::Element) -> (bool) requires (Field(F)) {{
        let r = field::equal::<F>(a,b); control::require(r); return (r);
      }}
      configure MultiplyE=Multiply(F={EXT}); configure CheckE=Check(F={EXT});
      protocol Main {{ roles (P,V);
        inputs (P a:{EXT}::Element,P b:{EXT}::Element,V expected:{EXT}::Element);
        outputs (V bool);
        local P: let r = MultiplyE(a,b);
        message product: P(r) -> V(received);
        local V: let accepted = CheckE(received,expected); return (accepted);
      }}
      instance concrete:Main {{roles (P=P,V=V);}} entry main=concrete;
    }}'''
    ts = journal.write('transport-source.json', json.loads(journal.run([compiler, 'protocol-source', '-'], transport)))
    tp = journal.write('transport-plan.json', json.loads(journal.run([compiler, 'protocol-compile', '-'], transport)))
    for label, expected, success in [('good', mul(X7,X7), True), ('wrong', ZERO, False)]:
        np = journal.write('transport-' + label + '.json', ['zkc.run/2', 'main', 'transport', [], [
            ['P', [], [['a',['wire',wire('field',X7).hex()]],['b',['wire',wire('field',X7).hex()]]], []],
            ['V', [], [['expected',['wire',wire('field',expected).hex()]]], []]], []])
        rp = journal.write('transport-' + label + '-reference.json', ['zkc.reference-inputs/1', 'main', 'transport', [
            ['P', [['a',['field:'+EXT,strings(X7)]],['b',['field:'+EXT,strings(X7)]]]],
            ['V', [['expected',['field:'+EXT,strings(expected)]]]]], [], [], []])
        ref = json.loads(journal.run([lean, '--generic-reference', ts, rp]))
        actual = json.loads(journal.run([runtime, 'run-protocol', ts, tp, np, lean]))
        assert actual['wire']['messages'] == 1 and actual['wire']['payload_bytes'] == 38, actual['wire']
        if success:
            assert ref[3] == ['returned', [['bool','true']]], ref[3]
            assert actual['outcome'] == ['returned', {'P': [], 'V': [['bool',True]]}], actual['outcome']
        else:
            assert ref[3][:2] == ['reject','require'], ref[3]
            assert actual['stop']['detail'] == 'rejected:require', actual

    print(f'{journal.save()} octic extension source/MLIR/native/Lean checks passed')



def test_extension_fields():
    main()


if __name__ == "__main__":
    main()
