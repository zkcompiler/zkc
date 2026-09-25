#!/usr/bin/env python3
"""Authored PIR -> MLIR -> native, checked against independent Lean numerics.

Small cosets use Lean's quadratic direct transform, not the native DFT algorithm.
Indices include values above field characteristic and preserve duplicate entries.
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
    journal = Journal(output)

    root = Path(output)
    root.mkdir(parents=True, exist_ok=True)
    base = (Path(__file__).resolve().parents[2] / 'tests/fixtures/coset-kernels.pir').read_text()
    P = 2130706433
    EXT = 'koala-bear.ext8-binomial3'

    def compile_source(label, source):
        logical = journal.run([compiler, 'protocol-import', '-'], source)
        journal.run([optimizer, '--verify-each'], logical)
        physical = journal.run([compiler, 'protocol-physical-ir', '-'], source)
        journal.run([optimizer, '--verify-each'], physical)
        authored = json.loads(journal.run([compiler, 'protocol-source', '-'], source))
        plan = json.loads(journal.run([compiler, 'protocol-compile', '-'], source))
        assert json.loads(journal.run([compiler, 'protocol-export', '-'], physical)) == plan
        sp, pp = journal.write(label+'-source.json', authored), journal.write(label+'-plan.json', plan)
        journal.run([lean, '--check-generic', sp, pp])
        return sp, pp


    def integers(value):
        return [integers(x) for x in value] if isinstance(value, list) else int(value)


    def strings(value):
        return [strings(x) for x in value] if isinstance(value, list) else str(value)


    def wire(kind, value, domain):
        tag = {'index': 31, 'indices': 32}.get(kind)
        if tag is None:
            tag = ({'field': 26, 'vector': 27, 'polynomial': 28} if domain == EXT
                   else {'field': 19, 'vector': 20, 'polynomial': 21})[kind]
        header = b'ZKCV\x01' + bytes([tag])
        if kind in ('index', 'indices'):
            values = [value] if kind == 'index' else value
            width = 8
        else:
            values = [value] if kind == 'field' else value
            if domain == EXT:
                values = [c for x in values for c in x]
            width = 4
        count = len(value).to_bytes(4, 'little') if kind in ('indices', 'vector', 'polynomial') else b''
        return header + count + b''.join(x.to_bytes(width, 'little') for x in values)


    def exercise(label, source, domain, inputs, failure=None, ports=('P',)):
        sp, pp = source
        native, reference = [], []
        for name, kind, value in inputs:
            native.append([name, ['wire', wire(kind, value, domain).hex()]])
            reference.append([name, [kind if kind in ('index', 'indices') else kind+':'+domain, strings(value)]])
        np = journal.write(label+'-inputs.json', ['zkc.run/2', 'main', 'numerical-test', [],
                  [[role, [], native if role == 'P' else [], []] for role in ports], []])
        rp = journal.write(label+'-reference.json', ['zkc.reference-inputs/1', 'main', 'numerical-test',
                  [[role, reference if role == 'P' else []] for role in ports], [], [], []])
        ref = json.loads(journal.run([lean, '--generic-reference', sp, rp]))
        actual = json.loads(journal.run([runtime, 'run-protocol', sp, pp, np, lean]))
        journal.write(label+'-lean.json', ref)
        journal.write(label+'-native.json', actual)
        if failure:
            assert ref[3][:2] == ['refused', failure], ref[3]
            assert actual['outcome'][0] == 'stopped', actual
            return
        assert ref[3][0] == 'returned', ref[3]
        outputs = ref[3][1]
        expected = []
        for spelling, value in outputs:
            kind = spelling.split(':')[0]
            value = integers(value)
            expected.append([kind, value] if kind in ('index', 'indices') else
                            ['wire', kind, wire(kind, value, domain).hex()])
        assert actual['outcome'] == ['returned', {ports[-1]: expected, **({'P': []} if len(ports)>1 else {})}], actual['outcome']
        return outputs


    rng = random.Random(619)
    for domain in ('koala-bear', EXT):
        source = compile_source(domain, base.replace('koala-bear', domain))
        def scalar():
            return [rng.randrange(P) for _ in range(8)] if domain == EXT else rng.randrange(P)
        one = [1]+[0]*7 if domain == EXT else 1
        for n in (2, 4, 8, 16, 32, 64):
            # Non-base extension coefficients, shifts and challenges exercise all coordinates.
            cs = [scalar() for _ in range(n//2)]
            shift, beta = scalar(), scalar()
            args = [('cs','vector',cs),('shift','field',shift),('beta','field',beta),('n','index',n),('query','index',n-1)]
            result = exercise(f'{domain}-{n}', source, domain, args)
            assert integers(result[1][1]) == cs  # normalized nonzero last coefficient
            assert integers(result[4][1]) == [n-1,n-1]  # repeated queries retained
        args = [('cs','vector',[one]),('shift','field',one),('beta','field',one),('n','index',4),('query','index',0)]
        for label, port, value, diagnostic in [
            ('non-power', 'n', 3, 'coset-size'),
            ('zero-shift', 'shift', [0]*8 if domain==EXT else 0, 'coset-zero-shift'),
            ('out-of-range', 'query', 4, 'vector-index'),
            ('max-query', 'query', 2**64-1, 'vector-index'),
            ('singleton', 'n', 1, 'coset-fold-size'),
        ]:
            exercise(domain+'-'+label, source, domain,
                     [(name,kind,value if name==port else old) for name,kind,old in args], diagnostic)

    # A domain-independent collection crosses participant transport with values that
    # cannot be represented injectively in the KoalaBear base field.
    transport = '''module {
 fn Make<>(x:index) -> (Indices) {
   let e = indices::empty(); let a = indices::append(e,x); let b = indices::append(a,x); return (b);
 }
 configure Build = Make();
 protocol Main { roles(P,V); inputs(P x:index); outputs(V Indices);
   local P: let xs = Build(x); message indices: P(xs) -> V(ys); return (ys);
 }
 instance concrete: Main {roles(P=P,V=V);} entry main=concrete;
}'''
    source=compile_source('index-transport',transport)
    exercise('index-transport',source,'koala-bear',[('x','index',2**64-1)],ports=('P','V'))
    journal.run([compiler,'protocol-compile','-'],base.replace('requires (TwoAdicField(F), CharacteristicNotTwo(F))','requires (Field(F))'), 'generic-public-requirement')
    journal.run([compiler,'protocol-compile','-'],base.replace('koala-bear','ristretto255.scalar'), 'source-protocol-requirement')
    print(json.dumps({'checks':journal.save(),'status':'pass','max_reference_coset':64,'domains':['koala-bear',EXT]}))



def test_numerical_kernels():
    main()


if __name__ == "__main__":
    main()
