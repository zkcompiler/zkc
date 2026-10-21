#!/usr/bin/env python3
"""Compare native SSA interpretation with independently elaborated Lean source.

Uses the explicit Z/97 scalar and additive-group test interpretation. Does not
execute a production field/curve backend. Every selected source is natively
verified before export. Reports include seeds and original-byte identities.
"""
import argparse
import copy
from collections import Counter
import hashlib
import json
from pathlib import Path
import random
import subprocess
import tempfile
import shutil

from native_entry import native_run
from snapshot import render
from contracts import check_contract_forms
from factor_openings import check_factor_forms

ROOT = Path(__file__).resolve().parents[3]
FIELD = 'bls12-381.fr'
GROUP = 'bls12-381.g1'
STOPS = ('reject', 'abort', 'exhausted', 'incomplete', 'refused')
TYPES = {'f': '!F', 'g': '!G', 'b': 'i1', 's': '!S'}


def execute(command, ok=True, diagnostic=None):
    result = subprocess.run(list(map(str, command)), cwd=ROOT, text=True,
                            capture_output=True, timeout=30)
    if result.returncode != (0 if ok else 1):
        raise AssertionError(f'{command}: exit {result.returncode}\n{result.stderr}\n{result.stdout}')
    if diagnostic is not None:
        assert diagnostic in result.stderr.splitlines(), (command, result.stderr, diagnostic)
    return result.stdout


def wrap(body, args, output, scope, helpers=''):
    argtext = ', '.join(f'%{name}: {TYPES[ty]}' for name, ty, _ in args)
    argtypes = ', '.join(TYPES[ty] for _, ty, _ in args)
    scopes = json.dumps([[f'R{r}' for r in roles] for _, _, roles in args])
    outputroles = json.dumps([[f'R{r}' for r in scope]])
    return f'''!F = !algebra.field<"{FIELD}">
!G = !algebra.group<"{GROUP}">
!S = !protocol.service_ref<"random.{FIELD}/0">
module {{ "protocol.module"() ({{
{helpers}
"protocol.func"() ({{
^entry({argtext}):
{chr(10).join(body)}
"protocol.return"(%{output[0]}) : ({TYPES[output[1]]}) -> ()
}}) {{sym_name="main", function_type=({argtypes})->{TYPES[output[1]]}, roles=["R0","R1","R2"], input_roles={scopes}, output_roles={outputroles}}} : () -> ()
}}) {{profile=#protocol.profile<protocol>}} : () -> ()
}}
'''


def generated(rng, count):
    args = [('a','f',[0,1,2]), ('b','f',[0,1]), ('c','f',[1,2]),
            ('g','g',[0,1,2]), ('h','g',[1]), ('flag','b',[0,1,2]),
            ('p','f',[0]), ('svc','s',[1])]
    values = [(n,t,set(s)) for n,t,s in args]
    body = []
    helper = '''func.func private @pair(%a:!F,%b:!F)->(!F,!F) {
%s = algebra.field_add %a, %b : (!F,!F)->!F
%d = algebra.field_subtract %a, %b : (!F,!F)->!F
return %s, %d : !F,!F
}'''
    for i in range(count):
        name = f'v{i}'
        choice = rng.randrange(15)
        if choice == 0:
            sender = rng.randrange(3)
            value = rng.choice([v for v in values if sender in v[2] and v[1] != 's'])
            receiver = (sender + rng.randrange(1,3)) % 3
            body.append(f'%{name} = protocol.exchange %{value[0]} {{site="e{i}",sender="R{sender}",receiver="R{receiver}"}} : {TYPES[value[1]]}')
            values.append((name,value[1],{sender,receiver}))
        elif choice == 1:
            body.append(f'%{name} = "protocol.query"(%svc) {{method="draw",owner="R1",site="q{i}"}} : (!S)->!F')
            values.append((name,'f',{1}))
        elif choice == 2:
            value = rng.choice([v for v in values if v[1] != 's'])
            scope = {rng.choice(sorted(value[2]))}
            body.append(f'%{name} = "protocol.restrict_roles"(%{value[0]}) {{roles=["R{next(iter(scope))}"]}} : ({TYPES[value[1]]})->{TYPES[value[1]]}')
            values.append((name,value[1],scope))
        elif choice == 3:
            value = rng.choice([v for v in values if v[1] == 'b'])
            owner = rng.choice(sorted(value[2]))
            body.append(f'protocol.guard %{value[0]} {{owner="R{owner}",site="guard{i}"}}')
        elif choice == 10:
            first = rng.choice([v for v in values if v[1] == 'g'])
            second = rng.choice([v for v in values if v[1] == 'f' and v[2] & first[2]])
            body.append(f'%{name} = algebra.group_scale %{first[0]}, %{second[0]} : (!G,!F)->!G')
            values.append((name,'g',first[2] & second[2]))
        elif choice == 11:
            first = rng.choice([v for v in values if v[1] != 's'])
            second = rng.choice([v for v in values if v[1] == first[1] and v[2] & first[2]])
            condition = next(v for v in values if v[0]=='flag')
            body.append(f'%{name} = arith.select %flag, %{first[0]}, %{second[0]} : {TYPES[first[1]]}')
            values.append((name,first[1],first[2] & second[2] & condition[2]))
        elif choice == 12:
            number = rng.randrange(1000000)
            body.append(f'%{name} = "algebra.constant"() {{value="{number}"}} : ()->!F')
            values.append((name,'f',{0,1,2}))
        elif choice == 13:
            if i % 2:
                body.append(f'%{name} = algebra.group_identity : !G')
                values.append((name,'g',{0,1,2}))
            else:
                body.append(f'%{name} = arith.constant true')
                values.append((name,'b',{0,1,2}))
        else:
            tag = rng.choice(['f','g','b'])
            first = rng.choice([v for v in values if v[1] == tag])
            second = rng.choice([v for v in values if v[1] == tag and v[2] & first[2]])
            scope = first[2] & second[2]
            if choice == 4 and tag == 'f':
                body.append(f'%{name}:2 = func.call @pair(%{first[0]},%{second[0]}) : (!F,!F)->(!F,!F)')
                values.extend([(name+'#0','f',scope),(name+'#1','f',scope)])
                continue
            operation = {'f': ['field_add','field_subtract','field_multiply','field_equal'],
                         'g': ['group_add','group_equal'],
                         'b': ['andi','ori','xori','cmpi']}[tag]
            operation = rng.choice(operation)
            out = 'b' if operation.endswith('equal') or tag == 'b' else tag
            if tag == 'b':
                prefix = rng.choice(['eq, ', 'ne, ']) if operation == 'cmpi' else ''
                body.append(f'%{name} = arith.{operation} {prefix}%{first[0]}, %{second[0]} : i1')
            else:
                body.append(f'%{name} = algebra.{operation} %{first[0]}, %{second[0]} : ({TYPES[tag]},{TYPES[tag]})->{TYPES[out]}')
            values.append((name,out,scope))
    output = rng.choice([v for v in values if v[1] != 's'])
    return wrap(body,args,output,sorted(output[2]),helper)


class Suite:
    def __init__(self, args, directory):
        self.args, self.directory = args, directory
        self.rng = random.Random(args.seed)
        self.comparisons = 0
        self.sources = []
        self.instructions = Counter()

    def export(self, text, symbol='main'):
        source = self.directory / 'source.mlir'
        source.write_text(text)
        data = json.loads(execute([self.args.compiler,'protocol-lean',source,'--symbol='+symbol]))
        assert data[1] == 'sha256:' + hashlib.sha256(text.encode()).hexdigest()
        exported = self.directory / 'source.json'
        exported.write_text(json.dumps(data))
        execute([self.args.lean,'check',exported])
        return source, exported, data

    def compare(self, source, exported, symbol, request):
        path = self.directory / 'request.json'
        path.write_text(json.dumps(request))
        left = json.loads(execute([self.args.reference,source,symbol,path]))
        right = json.loads(execute([self.args.lean,'run',exported,path]))
        self.comparisons += 1
        if left != right:
            (self.directory / 'mismatch.json').write_text(json.dumps(
                {'request':request,'native':left,'lean':right},indent=2))
            raise AssertionError(f'complete execution mismatch; retained at {self.directory}')
        return left

    def value(self, ty):
        return self.rng.choice([False,True]) if ty[0]=='bool' else self.rng.randrange(97)

    def exercise(self, text, symbol='main', repetitions=2):
        source, exported, data = self.export(text,symbol)
        self.sources.append({'sha256':data[1],'symbol':symbol,'instructions':len(data[8])})
        self.instructions.update(x[1][0] if x[0]=='pure' else x[0] for x in data[8])
        for _ in range(repetitions):
            for role in range(len(data[3])):
                inputs = [self.value(ty) if role in scopes else None for ty,scopes in zip(data[4],data[5],strict=True)]
                request = ['zkc.common-run/0',role,inputs,[]]
                for _ in range(65):
                    result = self.compare(source,exported,symbol,request)
                    events = result[3]
                    if not events or events[-1][1] != ['missing']:
                        break
                    action = events[-1][0]
                    for stop in STOPS:
                        stopped = copy.deepcopy(request)
                        stopped[3].append([action,['stop',stop]])
                        observed = self.compare(source,exported,symbol,stopped)
                        assert observed[1] == ['stopped',stop]
                    altered = copy.deepcopy(request)
                    wrong = copy.deepcopy(action)
                    wrong[1] += '-wrong-site'
                    altered[3].append([wrong,['stop','abort']])
                    assert self.compare(source,exported,symbol,altered)[1] == ['stopped','refused']
                    ty = action[3] if action[0]=='receive' else ['field',FIELD]
                    value = None if action[0]=='send' else self.value(ty)
                    request[3].append([action,['return',value]])
                else:
                    raise AssertionError('unexpected action bound')
        return data

    def sumcheck(self, text, symbol):
        source, exported, data = self.export(text, symbol)
        values = [2,3,5,7,11,13,17,19,23]
        def evaluate(row, x):
            return (row[0] + x*row[1] + x*x*row[2]) % 97
        rows = [values[i:i+3] for i in (0,3,6)]
        message = [(2*a+b+c)%97 for a,b,c in rows]
        claim = (2*message[0]+message[1]+message[2])%97
        first, second = 3,5
        next_message = [evaluate([rows[i][j] for i in range(3)],first) for j in range(3)]
        def label(name):
            return 'label_' + name.encode().hex() + '_0'
        received = {label(f'first{i}'): message[i] for i in range(3)}
        received.update({label(f'second{i}'): next_message[i] for i in range(3)})
        received.update({label('deliver0'): first, label('deliver1'): second})
        outcomes = []
        # Honest execution and two attacks: failed boundary, then a wrong
        # terminal value with a preserved second boundary.
        for attack in ('honest','first-boundary','terminal'):
            for role in (0,1):
                inputs = [*values,claim,41 if role==1 else None]
                request = ['zkc.common-run/0',role,inputs,[]]
                for _ in range(16):
                    result=self.compare(source,exported,symbol,request)
                    if not result[3] or result[3][-1][1] != ['missing']: break
                    action=result[3][-1][0]
                    if action[0]=='send': value=None
                    elif action[0]=='draw': value=first if action[1].endswith('30') else second
                    else:
                        value=received[action[1]]
                        if role==1 and attack=='first-boundary' and action[1]==label('first0'):
                            value=(value+1)%97
                        if role==1 and attack=='terminal':
                            if action[1]==label('second0'): value=(value+1)%97
                            if action[1]==label('second1'): value=(value-2)%97
                    request[3].append([action,['return',value]])
                expected = ['returned',None] if role==0 else {
                    'honest':['returned',True], 'first-boundary':['stopped','reject'],
                    'terminal':['returned',False]}[attack]
                assert result[1]==expected, (attack,role,result)
                if role==1 and attack=='first-boundary': assert result[2]==3
                outcomes.append({'attack':attack,'role':role,'outcome':result[1]})
        return outcomes

    def negatives(self, data):
        mutations = []
        for position,value in [(0,'zkc.common-source/999'),(1,'sha256:bad'),(9,2049),
                               (3,[]),(7,[]),(5,[[99]]*len(data[4]))]:
            changed=copy.deepcopy(data); changed[position]=value; mutations.append(changed)
        changed=copy.deepcopy(data); changed[8].insert(0,['pure',['field.add',FIELD],[2048,2048]]); mutations.append(changed)
        changed=copy.deepcopy(data); changed.append('ignored'); mutations.append(changed)
        for changed in mutations:
            path=self.directory/'negative.json'; path.write_text(json.dumps(changed))
            execute([self.args.lean,'check',path],ok=False)
        return len(mutations)

    def request_formats(self):
        source, exported, _ = self.export(wrap([], [('a', 'f', [0, 1, 2])], ('a', 'f'), [0, 1, 2]))
        assert self.compare(source, exported, 'main', ['zkc.common-run/0', 0, [0], []])[1] == ['returned', 0]
        controls = [
            '["zkc.common-run/0",-0,[0],[]]',
            '["zkc.common-run/0",0,[-0],[]]',
            '["zkc.common-run/0",0,[0],[[-1]]]',
            '["zkc.common-run/0",0,[0],[{"x":0,"x":1}]]',
            '["zkc.common-run/0",0,[0],[{"x":0}]]',
            '["zkc.common-run/0",0,[0],[[1e0]]]',
            '["zkc.common-run/0",0,[0],[[0.0]]]',
        ]
        path = self.directory / 'raw-request.json'
        for text in controls:
            path.write_text(text)
            execute([self.args.reference, source, 'main', path], ok=False, diagnostic='common-run-format')
            refusal = json.loads(execute([self.args.lean, 'run', exported, path], ok=False))
            assert refusal == {'status': 'refused', 'code': 'common-run-json'}, refusal
        # Lexical preflight must leave string contents alone, even in an unused tail.
        self.compare(source, exported, 'main', ['zkc.common-run/0', 0, [0], ['-0{}1e0']])
        return len(controls)

    def mutation_control(self):
        # Deliberately corrupt an exported operation, then shrink native source
        # while rechecking native admission at every candidate.
        args=[('a','f',[0,1,2]),('b','f',[0,1,2])]
        body=['%dead = algebra.field_multiply %a, %b : (!F,!F)->!F',
              '%answer = algebra.field_add %a, %b : (!F,!F)->!F']
        def mismatch(candidate, inputs):
            source, exported, data = self.export(wrap(candidate,args,('answer','f'),[0,1,2]))
            index=next(i for i,x in enumerate(data[8]) if x[0]=='pure' and x[1][0]=='field.add')
            data[8][index][1][0]='field.subtract'; exported.write_text(json.dumps(data))
            path=self.directory/'request.json'; path.write_text(json.dumps(['zkc.common-run/0',0,inputs,[]]))
            return json.loads(execute([self.args.reference,source,'main',path])) != json.loads(execute([self.args.lean,'run',exported,path]))
        assert mismatch(body,[29,17])
        # Greedy definition deletion; candidates with dangling references are
        # rejected by native admission, never treated as counterexamples.
        for line in list(body):
            candidate=[x for x in body if x!=line]
            try:
                remains=mismatch(candidate,[29,17])
            except AssertionError:
                remains=False
            if remains: body=candidate
        inputs=[29,17]
        for i in range(len(inputs)):
            for value in (0,1):
                candidate=inputs.copy(); candidate[i]=value
                if mismatch(body,candidate): inputs=candidate; break
        assert len(body)==1 and inputs==[0,1] and mismatch(body,inputs)
        return {'kind':'field.add-to-subtract','definitions':len(body),'inputs':inputs}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler',type=Path,default=ROOT/'build/compiler/zkc-compile')
    parser.add_argument('--reference',type=Path,default=ROOT/'build/compiler/test/zkc-common_reference-test')
    parser.add_argument('--lean',type=Path,default=ROOT/'lean/.lake/build/bin/common-source')
    parser.add_argument('--seed',type=int,default=20261012)
    parser.add_argument('--cases',type=int,default=40)
    parser.add_argument('--report',type=Path,required=True)
    args=parser.parse_args()
    args.report.parent.mkdir(parents=True,exist_ok=True)
    # Retain failing artifacts next to the report instead of deleting temp data.
    temporary=Path(tempfile.mkdtemp(prefix='common-',dir=args.report.parent))
    try:
        binaries = {}
        for name in ('compiler', 'reference', 'lean'):
            original = getattr(args, name).resolve()
            target = temporary / name
            shutil.copy2(original, target)
            binaries[name] = {'path': str(original), 'sha256': hashlib.sha256(target.read_bytes()).hexdigest()}
            setattr(args, name, target)
        suite=Suite(args,temporary)
        flags=['--source-format=zkc','--module=example=examples/projects/schnorr/main.zkc',
               '--module=schnorr=libraries/protocols/sigma/schnorr/lib.zkc','--entry=example::Interactive']
        text, interface = native_run(execute, args.compiler, flags)
        assert interface['original']==hashlib.sha256(text.encode()).hexdigest()
        symbol=interface['protocol']
        data=suite.exercise(text,symbol)
        fixture=ROOT/'lean/ZkcExamples/NativePrograms/fixtures/schnorr.json'
        assert data==json.loads(fixture.read_text()), 'Schnorr source drift: review correspondence before refreshing'
        expected=render(data,'ZkcExamples.NativePrograms.SchnorrData')
        assert expected==(fixture.parent.parent/'SchnorrData.lean').read_text()
        fixture_text=(ROOT/'compiler/test/fixtures/mathematical/schnorr-services.mlir').read_text()
        suite.exercise(fixture_text)
        sumcheck_flags=['--source-format=zkc',
                        '--module=scalar_sumcheck=lean/bridges/common/fixtures/sumcheck.zkc',
                        '--entry=scalar_sumcheck::Interactive']
        sumcheck_text, sumcheck_interface = native_run(execute, args.compiler, sumcheck_flags)
        assert sumcheck_interface['original']==hashlib.sha256(sumcheck_text.encode()).hexdigest()
        sumcheck_symbol=sumcheck_interface['protocol']
        sumcheck_data=suite.exercise(sumcheck_text,sumcheck_symbol)
        sumcheck_fixture=fixture.with_name('sumcheck.json')
        assert sumcheck_data==json.loads(sumcheck_fixture.read_text())
        assert render(sumcheck_data,'ZkcExamples.NativePrograms.SumcheckData')==(fixture.parent.parent/'SumcheckData.lean').read_text()
        sumcheck_controls=suite.sumcheck(sumcheck_text,sumcheck_symbol)
        contract_controls=check_contract_forms(suite,ROOT,execute,
            {'Schnorr':(text,symbol),'Sumcheck':(sumcheck_text,sumcheck_symbol)})
        factor_controls=check_factor_forms(suite,ROOT,execute)
        algebra_sources=[]
        for entry in ('Helpers','Expanded','AirResidual'):
            flags=['--source-format=zkc',
                   '--module=scalar_algebra=lean/bridges/common/fixtures/algebra.zkc',
                   '--entry=scalar_algebra::'+entry]
            algebra_text, algebra_interface = native_run(execute, args.compiler, flags)
            algebra_symbol = algebra_interface['protocol']
            suite.exercise(algebra_text,algebra_symbol)
            algebra_sources.append((algebra_text,algebra_symbol))
        variation_checks=0
        for _ in range(24):
            inputs=[suite.rng.randrange(97) for _ in range(5)]
            outcomes=[]
            for text,symbol in algebra_sources[:2]:
                source,exported,_=suite.export(text,symbol)
                outcomes.append(suite.compare(source,exported,symbol,['zkc.common-run/0',1,inputs,[]]))
            assert outcomes[0]==outcomes[1], 'helper/expanded fold mismatch'
            variation_checks+=1
        for _ in range(args.cases):
            suite.exercise(generated(suite.rng,suite.rng.randrange(4,30)))
        negatives=suite.negatives(data)
        request_formats=suite.request_formats()
        control=suite.mutation_control()
        report={'binaries':binaries,'seed':args.seed,'generated_cases':args.cases,'comparisons':suite.comparisons,
                'negative_formats':negatives,'request_format_refusals':request_formats,
                'mutation_control':control,'sources':suite.sources,
                'sumcheck_controls':sumcheck_controls,'source_variation_checks':variation_checks,
                'contract_controls':contract_controls,'factor_opening_controls':factor_controls,
                'instruction_coverage':dict(sorted(suite.instructions.items())),
                'interpretation':'Z/97 field and additive group; production backend not covered'}
        args.report.write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps({k:v for k,v in report.items() if k!='sources'}))
    except Exception:
        print(f'Failing inputs retained at {temporary}')
        raise
    else:
        shutil.rmtree(temporary)


if __name__=='__main__':
    main()
