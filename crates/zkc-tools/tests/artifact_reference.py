#!/usr/bin/env python3
"""Compare native V events with Main's separate original-source Lean reference.
The reference driver and primitive executable are dependencies, never implemented
or modified by this test. All inputs/outputs stay under --output-dir.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "tests/support"))
from journal import Journal, TIMEOUT, positive_timeout  # noqa: E402

p=argparse.ArgumentParser(description=__doc__)
for k in ['zkc','compiler','lean','fixture-exporter','reference-driver','reference','primitive','output-dir']:
    p.add_argument('--'+k,required=True,type=Path)
p.add_argument('--timeout',type=positive_timeout,default=TIMEOUT)
p.add_argument('--reference-timeout',type=positive_timeout,default=900)
a=p.parse_args()
a.output_dir.mkdir(parents=True,exist_ok=False)
fixtures=Path(__file__).parent/'fixtures/artifact'
records=[]
configuration_checks=[]
commands=[]
journal=Journal(a.output_dir/'commands',timeout=a.timeout)
def call(args):
    r=journal.attempt(args,text=False,
                      timeout=a.reference_timeout if str(args[0])==sys.executable else a.timeout,
                      cleanup_grace=3 if str(args[0])==sys.executable else 1)
    commands.append({'argv':[str(x) for x in args],'returncode':r.returncode})
    return r

def save(path,v):
    path.write_text(json.dumps(v));return path

def load(path):return json.loads(path.read_bytes())

assert call([a.fixture_exporter,a.output_dir]).returncode==0
assert call([a.fixture_exporter,a.output_dir/'other-setup']).returncode==0
for name in ['dleq','committed-two-factor','renamed-dleq','unicode-label','same-role-public','shifted-output','homogeneous-vk']:
    case=a.output_dir/name;case.mkdir(exist_ok=True)
    base='committed-two-factor' if name in ['committed-two-factor','homogeneous-vk'] else 'dleq'
    source=load(fixtures/(base+'.json'));descriptor=load(fixtures/(base+'.construction.json'))
    if name=='renamed-dleq':
        for instance in source[4]:
            for role in instance[5]:role[1]={'P':'Alice','V':'Bob'}[role[1]]
        descriptor[2:4]=['Alice','Bob']
        for binding in descriptor[4]:
            for port in binding[1]:port[0]={'P':'Alice','V':'Bob'}[port[0]]
    if name=='unicode-label':descriptor[4][0][0]='e\u0301 public label'
    if name=='same-role-public':
        descriptor[4][0][1].extend(descriptor[4][1][1]);descriptor[4].pop(1)
    if name=='shifted-output':
        source[3][-1][5].reverse();source[3][-1][7][-1][1].reverse();descriptor[6]='1'
    # A second verifier key of the same setup as the first. Every other port
    # names its domain, and a key that did not was refused `binding-type`.
    if name=='homogeneous-vk':source[3][-1][4].append(['vk_second','V','verifier_key:multilinear.kzg.bls12-381/1'])
    s=save(case/'source.json',source);d=save(case/'descriptor.json',descriptor)
    r=call([a.compiler,'protocol-construct',s,d]);assert r.returncode==0,r.stderr
    result=json.loads(r.stdout);c=save(case/'construction.json',result);common=save(case/'common.json',result[2])
    r=call([a.compiler,'protocol-compile',common]);assert r.returncode==0,r.stderr
    physical=save(case/'physical.json',json.loads(r.stdout))
    proof=case/'proof.bin'
    pi=load(a.output_dir/(base+'.producer.json'));vi=load(a.output_dir/(base+'.validator.json'))
    if name=='homogeneous-vk':
        # Homogeneous means the same setup as the first key: same type
        # spelling and same material. The configuration's key records are
        # checked against the artifact's key ports name for name and type
        # for type, so a record that spelled its type differently was
        # refused `artifact-configuration-order`.
        for x in [pi,vi]:x[4][1].append(['vk_second',x[4][1][0][1],x[4][1][0][2]])
    if name=='unicode-label':
        for x in [pi,vi]:x[2][0][0]=descriptor[4][0][0]
    if name=='same-role-public':
        for x in [pi,vi]:
            x[2][3][2]=x[2][2][2];x[2].pop(1)
    vi[2].reverse()  # named public INPUTS normalize to descriptor root order
    pin=save(case/'producer.json',pi);vin=save(case/'validator.json',vi)
    def native(mode,input_path,proof_path):
        r=call([a.zkc,mode,s,d,c,physical,input_path,a.compiler,a.lean,proof_path,'10000'])
        return json.loads(r.stdout)
    produced=native('produce-artifact',pin,proof);assert produced['status']=='produced',produced
    original=proof.read_bytes()
    candidates=[('honest',original),('trailing',original+b'\0'),('truncated',original[:-1]),('wrong-root',original[:8]+bytes([original[8]^1])+original[9:])]
    if base=='dleq':
        cursor=40;last=None
        while cursor<len(original):
            n=int.from_bytes(original[cursor:cursor+8],'little');last=(cursor+8,n);cursor+=8+n
        bad=bytearray(original);assert last[1]==38
        bad[last[0]+6:last[0]+38]=bytes(32)
        candidates.append(('bad-equation',bytes(bad)))
    else:
        # Root comparison fails before the first challenge, even with a valid
        # canonical commitment payload taken from the other original factor.
        n=int.from_bytes(original[40:48],'little');second=48+n
        n2=int.from_bytes(original[second:second+8],'little');assert n==n2
        bad=bytearray(original);bad[48:48+n]=original[second+8:second+8+n]
        candidates.append(('bad-commitment',bytes(bad)))
    for label,bytes_ in candidates:
        run_dir=case/label;run_dir.mkdir(exist_ok=True)
        candidate=run_dir/'proof.bin';candidate.write_bytes(bytes_)
        native_report=native('validate-artifact',vin,candidate)
        save(run_dir/'native.json',native_report)
        r=call([sys.executable,a.reference_driver,'--lean',a.reference,'--primitive',a.primitive,
                '--source',s,'--descriptor',d,'--inputs',vin,'--proof',candidate,'--output',run_dir/'reference'])
        assert r.returncode==0,r.stderr
        ref=load(run_dir/'reference/observation.json')
        assert ref[0] == 'zkc.artifact-observation/1',ref
        assert (ref[1][0]=='accepted')==(native_report['status']=='accepted'),(name,label,ref[1],native_report['code'])
        assert ref[2]==native_report['events'],(name,label,'event mismatch')
        assert int(ref[4])==native_report['proof_bytes'],(name,label,ref[4],native_report['proof_bytes'])
        assert int(ref[5])==sum(e[0]=='challenge' for e in native_report['events'])
        assert int(ref[6])==sum(e[0] in ['challenge','message'] for e in native_report['events'])
        records.append({'protocol':name,'case':label,'outcome':ref[1][0],'native_code':native_report['code'],
                        'events':len(ref[2]),'proof_bytes':int(ref[4]),'draws':int(ref[5]),'transcript_actions':int(ref[6])})
    if name=='homogeneous-vk':
        # The second key becomes one from an independently generated setup. That
        # is not a conflicting key — a conflict is two records that carry the
        # same metadata and different material, and these two carry different
        # metadata — it is a configuration the proof was not made under. Both
        # implementations refuse it the same way and observe nothing.
        wrong=copy.deepcopy(vi)
        wrong[4][1][1][2]=load(a.output_dir/'other-setup/committed-two-factor.validator.json')[4][1][0][2]
        wrong_path=save(case/'conflicting-keys.json',wrong)
        report=native('validate-artifact',wrong_path,proof)
        save(case/'conflicting-native.json',report)
        assert report['code']=='proof-header' and report['events']==[],report
        r=call([sys.executable,a.reference_driver,'--lean',a.reference,'--primitive',a.primitive,
                '--source',s,'--descriptor',d,'--inputs',wrong_path,'--proof',proof,'--output',case/'conflicting-reference'])
        assert r.returncode==0,r.stderr
        ref=load(case/'conflicting-reference/observation.json')
        assert ref[1][:2]==['refused','proof-header'] and ref[2]==[],ref
        configuration_checks.append({'case':'conflicting-keys','native':report['code'],'reference':ref})
summary={'status':'passed','comparisons':len(records),'cases':records,'configuration_checks':configuration_checks,'dependencies':{
    key:{'path':str(getattr(a,key)),'sha256':hashlib.sha256(getattr(a,key).read_bytes()).hexdigest()}
    for key in ['zkc','compiler','lean','reference_driver','reference','primitive']}}
save(a.output_dir/'summary.json',summary);save(a.output_dir/'commands.json',commands)
print(json.dumps({'status':'passed','comparisons':len(records)}))
