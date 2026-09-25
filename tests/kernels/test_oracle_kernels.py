#!/usr/bin/env python3
"""Authored oracle operations, native Plonky3 vs independent finite Lean tree."""
import json
from pathlib import Path

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
    base = (Path(__file__).resolve().parents[2] / 'tests/fixtures/oracle-access.pir').read_text()

    def strings(v):
        return [strings(x) for x in v] if isinstance(v,list) else str(v)

    def wire(kind,value,extension):
        header=b'ZKCV\x01'+bytes([31 if kind=='index' else 27 if extension else 20])
        if kind=='index': return header+value.to_bytes(8,'little')
        values=[c for x in value for c in x] if extension else value
        return header+len(value).to_bytes(4,'little')+b''.join(x.to_bytes(4,'little') for x in values)

    for extension in (False, True):
        field='koala-bear.ext8-binomial3' if extension else 'koala-bear'
        source=base.replace('koala-bear',field)
        logical=journal.run([compiler,'protocol-import','-'],source)
        assert 'oracle.commit' in logical and '!oracle.object' in logical
        journal.run([optimizer,'--verify-each'],logical)
        physical=journal.run([compiler,'protocol-physical-ir','-'],source)
        journal.run([optimizer,'--verify-each'],physical)
        original=json.loads(journal.run([compiler,'protocol-source','-'],source))
        plan=json.loads(journal.run([compiler,'protocol-compile','-'],source))
        assert json.loads(journal.run([compiler,'protocol-export','-'],physical))==plan
        sp,pp=journal.write(field+'-source.json',original),journal.write(field+'-plan.json',plan)
        journal.run([lean,'--check-generic',sp,pp])
        for width,height,query,expected_height,expected_query in [
            (1,1,0,1,0),(2,3,2,3,2),(1,4,1,4,1),(3,8,7,8,7),
            (7,7,0,7,0),(9,4,3,4,3),(16,2,1,2,1),
            (2,3,2,4,2),  # Same path depth, wrong expected height.
            (2,3,1,3,2),  # Correct root and row, wrong coordinate.
        ]:
            label=f'{field}-{width}-{height}-{query}-{expected_height}-{expected_query}'
            values=[[i*17+j+1 for j in range(8)] for i in range(width*height)] if extension else [i*17+1 for i in range(width*height)]
            inputs={'P':[('values','vector',values),('width','index',width),('query','index',query)],
                    'V':[('expected_width','index',width),('expected_height','index',expected_height),('selected','index',expected_query)]}
            native=[];reference=[]
            for role,ports in inputs.items():
                native.append([role,[],[[name,['wire',wire(kind,value,extension).hex()]] for name,kind,value in ports],[]])
                reference.append([role,[[name,[kind if kind=='index' else kind+':'+field,strings(value)]] for name,kind,value in ports]])
            np=journal.write(label+'-inputs.json',['zkc.run/2','main','oracle-test',[],native,[]])
            rp=journal.write(label+'-reference.json',['zkc.reference-inputs/1','main','oracle-test',reference,[],[],[]])
            ref=json.loads(journal.run([lean,'--generic-reference',sp,rp]));journal.write(label+'-lean.json',ref)
            actual=json.loads(journal.run([runtime,'run-protocol',sp,pp,np,lean]));journal.write(label+'-native.json',actual)
            if height!=expected_height or query!=expected_query:
                assert ref[3][0]=='reject',ref
                assert actual['outcome'][0]=='stopped',actual
                continue
            assert ref[3][0]=='returned',ref
            expected=[]
            for spelling,value in ref[3][1]:
                kind=spelling.split(':')[0]
                if kind=='bool': expected.append(['bool',value=='true'])
                elif kind=='vector':
                    def integers(v):
                        return [integers(x) for x in v] if isinstance(v,list) else int(v)
                    expected.append(['wire',kind,wire(kind,integers(value),extension).hex()])
                else: expected.append(['wire',kind,value])
            assert actual['outcome']==['returned',{'P':[],'V':expected}],(label,actual['outcome'],expected)

    # Capabilities are not inherited between distinct commitment schemes.
    journal.run([compiler,'protocol-compile','-'],base.replace('requires (VectorCommitment(C))','requires (MultilinearOpening(C))'),'source-protocol-requirement')
    journal.run([compiler,'protocol-compile','-'],base.replace('C = "rows.merkle-keccak256.koala-bear/1"','C = "multilinear.kzg.bls12-381/1"'),'source-call-type')
    # Opening custody and collections cannot cross participant transport.
    journal.run([compiler,'protocol-compile','-'],base.replace('message [__site_1] roots: P(roots) -> V(received_roots);','message private: P(states) -> V(leaked);\n    message [__site_1] roots: P(roots) -> V(received_roots);'),'interactive-message-availability')
    print(json.dumps({'status':'pass','checks':journal.save(),'domains':2,'cases':18}))



def test_oracle_kernels():
    main()


if __name__ == "__main__":
    main()
