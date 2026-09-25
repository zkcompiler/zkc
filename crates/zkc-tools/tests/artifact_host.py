#!/usr/bin/env python3
"""Actual compiler + Lean admission + Ark Runner, separate process controls.
No primitive reference service is implemented here. Test exporter creates only
explicit development fixtures. Required executable paths have no machine defaults.
"""
import argparse
import copy
import hashlib
import json
import pathlib

import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "tests/support"))
from bls_fixture import module, nominal
from journal import Journal, TIMEOUT, positive_timeout

p = argparse.ArgumentParser()
for arg in ['zkc', 'fixture-exporter', 'compiler', 'lean', 'output-dir']:
    p.add_argument('--' + arg, required=True)
p.add_argument('--timeout', type=positive_timeout, default=TIMEOUT)
a = p.parse_args()
out = pathlib.Path(a.output_dir).resolve()
out.mkdir(parents=True, exist_ok=False)
fixtures = pathlib.Path(__file__).parent / 'fixtures' / 'artifact'
checks = []
commands = []
journal = Journal(out / 'commands', timeout=a.timeout)

def command(args):
    r = journal.attempt(args, text=False)
    commands.append({'argv': [str(x) for x in args], 'returncode': r.returncode})
    return r

def save(name, value):
    path = out / name
    path.write_text(json.dumps(value))
    return path

def read(path):
    return json.loads(pathlib.Path(path).read_bytes())

assert command([a.fixture_exporter, out]).returncode == 0
assert command([a.fixture_exporter, out / 'other-setup']).returncode == 0

def compile_case(name, source=None, descriptor=None):
    source = source if source is not None else read(fixtures / (name + '.json'))
    descriptor = descriptor if descriptor is not None else read(fixtures / (name + '.construction.json'))
    s = save(name + '.source.json', source)
    d = save(name + '.descriptor.json', descriptor)
    r = command([a.compiler, 'protocol-construct', s, d])
    assert r.returncode == 0, r.stderr.decode()
    result = json.loads(r.stdout)
    assert len(result) == 6
    c = save(name + '.construction.json', result)
    common = save(name + '.common.json', result[2])
    r = command([a.compiler, 'protocol-compile', common])
    assert r.returncode == 0, r.stderr.decode()
    physical = save(name + '.physical.json', json.loads(r.stdout))
    return [s, d, c, physical]

cases = {name: compile_case(name) for name in ['dleq', 'committed-two-factor']}

def run(name, producer=False, inputs=None, proof=None, budget='10000', paths=None, code=None, label=None):
    paths = paths or cases[name]
    role = 'producer' if producer else 'validator'
    inp = save('current-input.json', inputs) if inputs is not None else out / (name + '.' + role + '.json')
    current = read(inp)
    if current[4][1]:
        def receives(body):
            for op in body:
                if op[0] == 'receive' and op[5].split(':')[0] in ('commitment', 'proof'):
                    yield op[1]
                if op[0] == 'loop':
                    yield from receives(op[5])
        current[4][3] = [[part[2], part[3], site, 'vk']
                         for part in read(paths[3])[4] for site in receives(part[7])]
    inp = save('bound-current-input.json', current)
    proof = proof or out / (name + '.proof')
    r = command([a.zkc, 'produce-artifact' if producer else 'validate-artifact', *paths, inp, a.compiler, a.lean, proof, budget])
    result = json.loads(r.stdout)
    if code is None:
        assert r.returncode == 0 and result['status'] == ('produced' if producer else 'accepted'), (result['status'],result['code'])
    else:
        assert r.returncode == 1 and result['status'] == 'refused', (result['status'],result['code'])
        if isinstance(code, str):
            assert result['code'] == code, (code, result['code'])
    label = label or (name + '-' + role)
    checks.append({'case': label, 'status': result['status'], 'code': result['code'],
                   'messages': result['messages'], 'events': len(result['events'])})
    save('report-%03d.json' % len(checks), result)
    return result

for name, messages, events, transitions in [('dleq',6,60,10), ('committed-two-factor',9,73,15)]:
    produced = run(name, True, budget=str(transitions))
    accepted = run(name, budget=str(transitions))
    assert produced['messages'] == accepted['messages'] == messages
    assert len(accepted['events']) == events
    assert accepted['runtime']['active_frames'] == 0
    assert all(r['transitions'] == 0 for r in accepted['resources'] if r['port'].startswith('rng:'))
    assert [r['transitions'] for r in accepted['resources'] if r['port'].startswith('transcript:')] == [transitions]
    assert produced['events'] == []  # no witness/nonce operand observer on P
    proof = (out / (name + '.proof')).read_bytes()
    run(name, True, budget='0', code='exhausted:resource-budget', label=name+'-producer-budget')
    assert (out / (name + '.proof')).read_bytes() == proof
    run(name, budget='0', code='exhausted:resource-budget', label=name+'-validator-budget')
    for label, data, code in [
        ('trailing',proof+b'x','proof-trailing'),
        ('truncated',proof[:-1],'proof-truncated'),
        ('header-short',proof[:39],'proof-truncated'),
        ('header-binding',proof[:8]+bytes([proof[8]^1])+proof[9:],'proof-header'),
        ('length-limit',proof[:40]+b'\xff'*8+proof[48:],'proof-limit')]:
        bad = out / 'bad.proof'; bad.write_bytes(data)
        run(name, proof=bad, code=code, label=name+'-'+label)

v = read(out / 'dleq.validator.json')
pv = read(out / 'dleq.producer.json')
# Public root changes are valid application inputs but cannot validate this proof.
w = copy.deepcopy(v); w[1] = '01'
run('dleq', inputs=w, code='proof-header', label='context-binding')
for label, mutate, code, producer in [
    ('duplicate-source',lambda x:x[3].append(copy.deepcopy(x[3][0])),'artifact-duplicate-input',True),
    ('unknown-source',lambda x:x[3].append(['unknown','field:bls12-381.fr','00']),'artifact-unknown-input',False),
    ('injected-rng',lambda x:x[3].append(['coins','rng','2']),'artifact-injected-selected-rng',False),
    ('injected-transcript',lambda x:x[3].append(['transcript','transcript','2']),'artifact-unknown-input',False),
    ('validator-private-pk',lambda x:x[3].append(['x','prover_key_file','missing','00','vk']),'artifact-unknown-input',False),
    ('missing-witness',lambda x:x[3].pop(0),'artifact-missing-input',True),
    ('input-kind',lambda x:x[3][0].__setitem__(1,'scalar'),'artifact-input-type',True),
    ('private-nonce-material',lambda x:x[3][1].append('secret'),'artifact-record',True),
    ('duplicate-public',lambda x:x[2].append(x[2][0]),'artifact-duplicate-public',False),
    ('public-kind',lambda x:x[2][0].__setitem__(1,'scalar'),'artifact-public-type',False),
    ('uppercase-hex',lambda x:x[2][0].__setitem__(2,x[2][0][2].upper()),'artifact-hex',False),
    ('odd-hex',lambda x:x[2][0].__setitem__(2,'0'),'artifact-hex',False),
]:
    w=copy.deepcopy(pv if producer else v);mutate(w)
    run('dleq', producer, inputs=w, code=code, label=label)
w=copy.deepcopy(v);w[1]='0x00'
run('dleq',inputs=w,code='artifact-hex',label='prefixed-hex')
w=copy.deepcopy(v);w[2].reverse()
ordered=run('dleq',label='public-order-original')
reordered=run('dleq',inputs=w,label='public-order-normalized')
assert ordered['binding_sha256']==reordered['binding_sha256']
w=copy.deepcopy(v);w[2][0][0]='unknown'
run('dleq',inputs=w,code='artifact-unknown-public',label='unknown-public')
w=copy.deepcopy(v);w[2].pop()
run('dleq',inputs=w,code='artifact-public-coverage',label='missing-public')
# Explicit public duplicates agree, otherwise fail before running.
w=copy.deepcopy(pv);w[3].append(['p_base_0','group:bls12-381.g1',w[2][0][2]])
run('dleq',True,inputs=w,label='explicit-public-equal')
w[3][-1][2]=w[2][1][2]
run('dleq',True,inputs=w,code='artifact-public-equality',label='explicit-public-disagrees')
# Restore matching candidate, then change a canonical scalar response to zero.
run('dleq', True)
proof=(out/'dleq.proof').read_bytes();cursor=40;last=None
while cursor<len(proof):
    size=int.from_bytes(proof[cursor:cursor+8],'little');last=(cursor+8,size);cursor+=8+size
assert last[1]==38
bad=bytearray(proof);bad[last[0]+6:last[0]+38]=bytes(32)
(out/'bad.proof').write_bytes(bad)
r=run('dleq',proof=out/'bad.proof',code='rejected:require',label='canonical-invalid-response')
assert r['events'][-1][0]=='request' and r['events'][-1][1][4][6]=='control.require'
assert r['runtime']['active_frames']==0
# Compiler / manifest and independent physical admission are separate boundaries.
for label,index,change in [
    ('five-element-result',2,lambda x:x.pop()),
    ('changed-output-map',2,lambda x:x[5][0].__setitem__(1,'999')),
    ('changed-origin',2,lambda x:x[4][0].__setitem__(2,'other')),
    ('wrong-descriptor',1,lambda x:x.__setitem__(6,'1')),
    ('changed-physical',3,lambda x:x.__setitem__(0,'wrong'))]:
    paths=list(cases['dleq']);val=read(paths[index]);change(val);paths[index]=save('mutation.json',val)
    run('dleq',paths=paths,code=True,label=label)
# PK association and material pins use only application configuration.
pk=read(out/'committed-two-factor.producer.json');vk=read(out/'committed-two-factor.validator.json')
for label,mutate,code in [
    ('pk-fingerprint',lambda x:x[3][0].__setitem__(3,'00'*32),'key-mismatch'),
    ('pk-fingerprint-width',lambda x:x[3][0].__setitem__(3,'00'),'artifact-material-fingerprint'),
    ('pk-association',lambda x:x[3][0].__setitem__(4,'other'),'artifact-prover-key-association'),
    ('config-missing',lambda x:x[4][1].clear(),'artifact-configuration-ports'),
    ('config-wrong-port',lambda x:x[4][1][0].__setitem__(0,'pk'),'artifact-configuration-order'),
    ('config-extra',lambda x:x[4][1].append(x[4][1][0]),'artifact-configuration-ports'),
    ('vk-truncated',lambda x:x[4][1][0].__setitem__(2,'00'),'artifact-verifier-key'),
]:
    w=copy.deepcopy(pk);mutate(w)
    run('committed-two-factor',True,inputs=w,code=code,label=label)
w=copy.deepcopy(vk);w[3].append(copy.deepcopy(vk[4][1][0]));run('committed-two-factor',inputs=w,label='explicit-vk-equal')
w[3][-1][2]=read(out/'other-setup/committed-two-factor.validator.json')[4][1][0][2]
run('committed-two-factor',inputs=w,code='artifact-configuration-equality',label='explicit-vk-disagrees')
# Reorder original V result positions: host selects the checked OUTPUT MAP.
s=read(fixtures/'dleq.json');d=read(fixtures/'dleq.construction.json')
entry=s[3][-1];entry[5].reverse();entry[7][-1][1].reverse();d[6]='1'
paths=compile_case('rng-before-acceptance',s,d)
run('dleq',True,paths=paths,label='rng-before-acceptance-producer')
run('dleq',paths=paths,label='rng-before-acceptance-validator')
# Formal role names survive nonidentity actual custody roles.
s=read(fixtures/'dleq.json');d=read(fixtures/'dleq.construction.json')
for instance in s[4]:
    for role in instance[5]: role[1]={'P':'Alice','V':'Bob'}[role[1]]
d[2:4]=['Alice','Bob']
for pub in d[4]:
    for port in pub[1]:port[0]={'P':'Alice','V':'Bob'}[port[0]]
paths=compile_case('renamed-roles',s,d)
run('dleq',True,paths=paths,label='renamed-roles-producer')
r=run('dleq',paths=paths,label='renamed-roles-validator')
assert all(e[1][4][5]=='V' for e in r['events'] if e[0] in ['request','response'])
# Repeated VK ports share material; selecting another authorized setup changes the proof binding.
s=read(fixtures/'committed-two-factor.json');d=read(fixtures/'committed-two-factor.construction.json')
s[3][-1][4].append(['vk_second','V','verifier_key:multilinear.kzg.bls12-381/1'])
paths=compile_case('two-vk-ports',s,d)
pp=copy.deepcopy(pk);vv=copy.deepcopy(vk)
for x in [pp,vv]:x[4][1].append(['vk_second','verifier_key:multilinear.kzg.bls12-381/1',x[4][1][0][2]])
run('committed-two-factor',True,paths=paths,inputs=pp,label='homogeneous-vk-producer')
run('committed-two-factor',paths=paths,inputs=vv,label='homogeneous-vk-validator')
wrong_order=copy.deepcopy(vv);wrong_order[4][1].reverse()
run('committed-two-factor',paths=paths,inputs=wrong_order,code='artifact-configuration-order',label='vk-config-order')
vv[4][1][-1][2]=read(out/'other-setup/committed-two-factor.validator.json')[4][1][0][2]
run('committed-two-factor',paths=paths,inputs=vv,code='proof-header',label='changed-vk-configuration')
# Exact UTF-8 application labels and same-role equality groups.
s=read(fixtures/'dleq.json');d=read(fixtures/'dleq.construction.json')
d[4][0][0]='e\u0301 public label'
paths=compile_case('unicode-label',s,d)
pp=copy.deepcopy(pv);vv=copy.deepcopy(v)
for x in [pp,vv]:x[2][0][0]=d[4][0][0]
run('dleq',True,inputs=pp,paths=paths,label='unicode-label-producer')
run('dleq',inputs=vv,paths=paths,label='unicode-label-validator')
vv[2][0][0]='é public label'
run('dleq',inputs=vv,paths=paths,code='artifact-unknown-public',label='unicode-no-normalization')
s=read(fixtures/'dleq.json');d=read(fixtures/'dleq.construction.json')
d[4][0][1].extend(d[4][1][1]);d[4].pop(1)
paths=compile_case('same-role-public',s,d)
pp=copy.deepcopy(pv);vv=copy.deepcopy(v)
for x in [pp,vv]:
    x[2][3][2]=x[2][2][2]  # both bases now equal, so both images equal
    x[2].pop(1)
run('dleq',True,inputs=pp,paths=paths,label='same-role-public-producer')
run('dleq',inputs=vv,paths=paths,label='same-role-public-validator')
# Unrelated affine resources remain in their actual roles and traverse the
# entry without synthetic draws or discarded returned resource custody.
s=read(fixtures/'dleq.json');d=read(fixtures/'dleq.construction.json')
for role,kind in [('P','rng'),('P','nonce')]:
    name='unrelated_'+kind
    s[3][-1][4].append([name,role,nominal(kind)]);s[3][-1][5].append([role,nominal(kind)]);s[3][-1][7][-1][1].append(name)
paths=compile_case('unrelated-resources',s,d)
pp=copy.deepcopy(pv);vv=copy.deepcopy(v)
pp[3].extend([['unrelated_rng','rng','0'],['unrelated_nonce','nonce','0']])
pr=run('dleq',True,inputs=pp,paths=paths,label='unrelated-resource-producer')
vr=run('dleq',inputs=vv,paths=paths,label='unrelated-resource-validator')
assert all(r['transitions']==0 for r in pr['resources'] if r['port'].startswith('rng:'))
assert sorted(r['transitions'] for r in pr['resources'] if r['port'].startswith('nonce:')) == [0,2,2]
# Large canonical public values use logical-tree limits, not source-string limits.
s=read(fixtures/'dleq.json');d=read(fixtures/'dleq.construction.json')
s[3][-1][4].extend([['p_table','P','table:bls12-381.fr'],['v_table','V','table:bls12-381.fr']])
d[4].append(['large_table',[['P','p_table'],['V','v_table']]])
paths=compile_case('large-public',s,d)
wire=(b'ZKCV\x01\x02'+(8).to_bytes(4,'little')+(1).to_bytes(32,'little')*256).hex()
assert len(wire)>4096
pp=copy.deepcopy(pv);vv=copy.deepcopy(v)
for x in [pp,vv]:x[2].append(['large_table','table:bls12-381.fr',wire])
run('dleq',True,paths=paths,inputs=pp,label='large-public-producer')
run('dleq',paths=paths,inputs=vv,label='large-public-validator')
# An entry may have no selected draw, with an explicit empty allowlist/budget.
s=module(
   [['function','Accept',[['ok','bool']],['bool'],[['return',['ok']]]]],
   [['protocol','NoDraw',['P','V'],[],[['ok','V','bool'],['coins','V','rng']],
     [['V','bool'],['V','rng']],[],[['local','accept','V','Accept',['ok'],['accepted']],['return',['accepted','coins']]]]],
   [['instance','root','NoDraw',[],[],[['P','P'],['V','V']]]],[['entry','main','root']])
d=['zkc.construction/1','main','P','V',[['ok',[['V','ok']]]],['coins',[]],'0','merlin3.bls12-381.fr64be/1','exact']
paths=compile_case('no-selected-draw',s,d)
x=['zkc.artifact-inputs/1','',[['ok','bool','5a4b4356010501']],[],['zkc.public-configuration/1',[],[],[]]]
r=run('dleq',True,paths=paths,inputs=x,budget='0',label='no-draw-producer');assert r['messages']==0
r=run('dleq',paths=paths,inputs=x,budget='0',label='no-draw-validator');assert r['events']==[]
# Proving-material substitution and truncation are separate from VK configuration.
paths=cases['committed-two-factor']
w=copy.deepcopy(pk);w[3][0][2]=str(out/'other-setup/development.pk')
run('committed-two-factor',True,inputs=w,code='key-mismatch',label='pk-file-substitution')
badpk=out/'truncated.pk';badpk.write_bytes((out/'development.pk').read_bytes()[:-1])
w=copy.deepcopy(pk);w[3][0][2]=str(badpk)
run('committed-two-factor',True,inputs=w,code=True,label='pk-file-truncated')
# The observer's explicit finite byte policy must refuse, not truncate events
# and return success. This compact source stays within runtime instruction limits.
s=module(
   [['function','Keep',[['a','bool']],['bool'],[['op','both','bool.and',[],['a','a'],['b']],['return',['b']]]]],
   [['protocol','ObserveLimit',['P','V'],[],[['ok','V','bool'],['coins','V','rng']],
     [['V','bool'],['V','rng']],[],[
       ['loop','repetitions',['constant','50000'],[['a','ok']],[],[['local','keep','V','Keep',['a'],['b']],['yield',['b']]],['result']],
       ['return',['result','coins']]]]],
   [['instance','root','ObserveLimit',[],[],[['P','P'],['V','V']]]],[['entry','main','root']])
d=['zkc.construction/1','main','P','V',[['ok',[['V','ok']]]],['coins',[]],'0','merlin3.bls12-381.fr64be/1','exact']
paths=compile_case('observer-byte-budget',s,d)
x=['zkc.artifact-inputs/1','',[['ok','bool','5a4b4356010501']],[],['zkc.public-configuration/1',[],[],[]]]
run('dleq',True,paths=paths,inputs=x,budget='0',label='observer-limit-producer')
r=run('dleq',paths=paths,inputs=x,budget='0',code='exhausted:observer-bytes',label='observer-byte-limit')
assert r['events'] and r['runtime']['active_frames']==0
assert len(r['events']) % 2 == 0
assert all(e[0] == ('request' if i % 2 == 0 else 'response')
           for i,e in enumerate(r['events']))
# Pre-parse resource controls.
for label,data,code in [('depth',b'['*66,'artifact-json-depth'),('object-duplicate',b'{"x":0,"x":1}','artifact-json-kind'),('source-byte-limit',b' '*((1<<20)+1),'artifact-byte-limit'),
                        ('array-items',b'['+b'[],'*32768+b'[]]','tree-limit'),
                        ('aggregate-nodes',b'['+b','.join([b'['+b','.join([b'[]']*30000)+b']']*7)+b']','tree-limit')]:
    paths=list(cases['dleq']);path=out/'hostile-source.json';path.write_bytes(data);paths[0]=path
    run('dleq',paths=paths,code=code,label=label)
run('dleq',budget='01',code='natural-index',label='canonical-budget')
# All reports contain public V operands only. Private nonce/material values are
# never encoded; source P field input x is not included in producer stdout.
assert all(c['returncode'] in [0,1] for c in commands)
summary={'status':'passed','checks':len(checks),'cases':checks,
         'executables':{k:{'path':getattr(a,k),'sha256':hashlib.sha256(pathlib.Path(getattr(a,k)).read_bytes()).hexdigest()} for k in ['zkc','compiler','lean']}}
save('summary.json',summary);save('commands.json',commands)
print(json.dumps({'status':'passed','checks':len(checks)}))
