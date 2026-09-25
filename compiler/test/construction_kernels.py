#!/usr/bin/env python3
"""Independent typed MLIR contracts for the installed kernels and domains."""
import json
from bls_fixture import declaration, PCS
from pathlib import Path
from commands import Commands
from tools import compiler, optimizer, records
from journal import names

# Group sequences now use the builtin dynamic tensor carrier; contracts and
# all existing signature/effect/refusal assertions below are unchanged.
T={'bool':'i1','field':'!algebra.field<"bls12-381.fr">',
   'group':'!algebra.group<"bls12-381.g1">','groups':'tensor<?x!algebra.group<"bls12-381.g1">>',
   'table':'!poly.multilinear<"bls12-381.fr">','round':'!poly.quadratic<"bls12-381.fr">',
   'point':'!poly.point<"bls12-381.fr">','nonce':'!pir.capability<"nonce:bls12-381.fr">',
   'transcript':'!pir.capability<"transcript:merlin3.bls12-381.fr64be/1">',
   **{k:f'!pcs.object<"{PCS}", "{k}">' for k in ['commitment','proof']}}
contracts=[
 ('pcs.equal','pcs.equal',['commitment','commitment'],['bool'],[]),
 ('curve.generator','algebra.curve_generator',[],['group'],[]),
 ('curve.add','algebra.curve_add',['group','group'],['group'],[]),
 ('curve.scale','algebra.curve_scale',['group','field'],['group'],[]),
 ('curve.equal','algebra.curve_equal',['group','group'],['bool'],[]),
 ('curve.empty','algebra.curve_empty',[],['groups'],[]),
 ('curve.append','algebra.curve_append',['groups','group'],['groups'],[]),
 ('curve.at','algebra.curve_at',['groups'],['group'],['0']),
 ('curve.commit','algebra.curve_commit',['groups','nonce'],['groups','nonce'],[]),
 ('curve.response','algebra.curve_response',['field','field','nonce'],['field'],[]),
 ('transcript.challenge','pir.transcript_challenge',['transcript'],['field','transcript'],['Protocol','call','Function','draw','V'])]
for t in ['bool','field','table','point','round','commitment','proof','group','groups']:
 contracts.append(('transcript.observe.'+t,'pir.transcript_observe',['transcript',t],['transcript'],['Protocol','message','schema','P','V']))
checks=[]
commands=Commands(records())


def run(tool,*args,text=None,ok=True,code=None):
 printed=commands.run([tool,*args],stdin=text,refuses=None if ok else (code or True))
 if ok and code:assert names(commands.last.stderr, code),(code,commands.last.stderr)
 return printed

def ir(spelling,inputs,outputs,params,extra=''):
 key = next((k for k, op, ins, outs, _ in contracts
             if op == spelling and (op != 'pir.transcript_observe' or [T[t] for t in ins] == inputs)), 'curve.commit')
 binding = declaration(key, key)
 args=', '.join(f'%a{i}: {t}' for i,t in enumerate(inputs))
 vals=', '.join(f'%a{i}' for i in range(len(inputs)))
 results=f'%r:{len(outputs)} = ' if outputs else ''
 return f'''module {{ "pir.module"() <{{stage = "common"}}> ({{
 {binding}
 func.func @f({args}) attributes {{logical_origin = ["f", []]}} {{
 {results}"{spelling}"({vals}) <{{site = "site", binding = @"{key}", parameters = {json.dumps(params)}}}> : ({', '.join(inputs)}) -> ({', '.join(outputs)})
 {extra}
 return
 }}
 }}) : () -> () }}'''

tmp = records()
tmp=Path(tmp)
for key,spelling,ins,outs,params in contracts:
 text=ir(spelling,[T[t] for t in ins],[T[t] for t in outs],params)
 path=tmp/'subject.mlir';path.write_text(text)
 exported=json.loads(run(compiler,'protocol-export',path))
 assert exported[2][0][4][0][2]==key,(key,exported)
 checks.append(key+'-signature-and-export')
 # Removing dead operations is forbidden: kernel effects/failures are explicit.
 after=run(optimizer,'--canonicalize','--cse',text=text)
 assert f'"{spelling}"' in after,after
 checks.append(key+'-effects-retained')
 # Too many, too few, and the wrong type. A contract that takes no parameters
 # has no too-few and no wrong-type case: both spell the same one extra string.
 malformed=[('too-many',params+['extra'],'interactive-kernel-parameters')]
 if params:malformed+=[('too-few',params[:-1],'interactive-kernel-parameters'),
                       ('wrong-type',[True]*len(params),'binding-parameters')]
 for how,bad,code in malformed:
  run(optimizer,text=ir(spelling,[T[t] for t in ins],[T[t] for t in outs],bad),ok=False,code=code)
  checks.append(key+'-parameters-'+how)
 run(optimizer,text=ir(spelling,[T[t] for t in ins],['i1']*(len(outs)+1),params),ok=False,code='binding-operation-signature')
 checks.append(key+'-wrong-signature')
for bad,code in [('00','noncanonical-natural'),('-1','expected-natural'),
                 ('1048577','interactive-index'),('18446744073709551616','interactive-index'),
                 ('1.0','expected-natural'),('','expected-natural')]:
 run(optimizer,text=ir('algebra.curve_at',[T['groups']],[T['group']],[bad]),ok=False,code=code)
 checks.append('curve-at-refuses-'+bad)
run(optimizer,text=ir('algebra.curve_add',['!algebra.group<"reference.group">']*2,[T['group']],[]),ok=False,code='binding-operation-signature')
checks.append('reference-group-is-not-g1')
run(optimizer,text=ir('algebra.curve_commit',[T['groups'],'!pir.capability<"nonce">'],[T['groups'],'!pir.capability<"nonce">'],[]),ok=False,code='binding-operation-signature')
checks.append('reference-nonce-is-not-fr-nonce')
# The same affine transcript cannot be consumed twice. This subject is directly
# authored MLIR, so it exercises admission of actual mutated SSA.
second='''%second = "pir.transcript_observe"(%a0, %a1) <{site = "other", binding = @"transcript.observe.bool", parameters = ["Protocol","m2","schema","P","V"]}> : (!pir.capability<"transcript:merlin3.bls12-381.fr64be/1">, i1) -> !pir.capability<"transcript:merlin3.bls12-381.fr64be/1">'''
run(optimizer,text=ir('pir.transcript_observe',[T['transcript'],'i1'],[T['transcript']],['Protocol','message','schema','P','V'],extra=second),ok=False,code='interactive-resource-reuse')
checks.append('transcript-affine-reuse')
print(f'construction kernels: {commands.save()} checks over {len(checks)} named assertions')
