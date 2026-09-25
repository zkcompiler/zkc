#!/usr/bin/env python3
"""Whole-host resource-boundary regressions, with real construction and backend.

Preserve completed observations at exhaustion and reject allocation-amplifying
JSON before constructing its tree. Memory figures are measurements, not caps.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil

import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "tests/support"))
from bls_fixture import module
from journal import Journal, positive_timeout

p = argparse.ArgumentParser(description=__doc__)
for name in ['zkc', 'compiler', 'lean', 'primitive', 'output']:
    p.add_argument('--' + name, type=Path, required=True)
p.add_argument('--timeout', type=positive_timeout, default=180)
a = p.parse_args()
gnu_time = shutil.which('time')
if gnu_time is None:
    p.error('GNU time is required on PATH to record peak memory')
a.output.mkdir(parents=True, exist_ok=False)
commands, checks = [], []
journal = Journal(a.output / 'commands', timeout=a.timeout)

def save(name, value):
    path = a.output / name
    path.write_text(json.dumps(value, separators=(',', ':')))
    return path

def run(argv, name, stdin=None):
    rss = a.output / (name + '.rss')
    argv = list(map(str, argv))
    r = journal.attempt([gnu_time, '-f', '%M', '-o', str(rss), *argv],
                        stdin=stdin, text=False)
    commands.append({'argv': argv, 'returncode': r.returncode})
    assert r.returncode in [0, 1], r.stderr[-1000:]
    result = json.loads(r.stdout)
    save(name + '.json', result)
    # time emits a status line on failure; its final line is maximum RSS.
    checks.append({'case': name, 'max_rss_kib': int(rss.read_text().splitlines()[-1]),
                   'code': result.get('code') if isinstance(result, dict) else None})
    return result

def compile_case(name, functions, ports, body, selections):
    s = module( functions,
         [['protocol',name,['P','V'],[],ports,[['V','bool'],['V','rng']],[],body]],
         [['instance','root',name,[],[],[['P','P'],['V','V']]]],[['entry','main','root']])
    d = ['zkc.construction/1','main','P','V',[['ok',[['V','ok']]]],
         ['coins',selections],'0','merlin3.bls12-381.fr64be/1','exact']
    sp, dp = save(name+'-source.json',s), save(name+'-descriptor.json',d)
    construction = run([a.compiler,'protocol-construct',sp,dp],name+'-construct')
    cp = save(name+'-construction.json',construction)
    common = save(name+'-common.json',construction[2])
    physical = run([a.compiler,'protocol-compile',common],name+'-compile')
    return [sp,dp,cp,save(name+'-physical.json',physical)]

base_ports = [['ok','V','bool'],['coins','V','rng']]
inputs = ['zkc.artifact-inputs/1','',[['ok','bool','5a4b4356010501']],[],['zkc.public-configuration/1',[],[],[]]]
vi = save('validator-inputs.json',inputs)
messages = compile_case('Messages',[],[['table','P','table']]+base_ports,
    [['message',f'm{i}','payload','P','V','table',f'r{i}'] for i in range(4)]+
    [['return',['ok','coins']]],[])
wire = (b'ZKCV\x01\x02'+(16).to_bytes(4,'little')+bytes(32*65536)).hex()
producer_inputs = json.loads(json.dumps(inputs))
producer_inputs[3] = [['table','table:bls12-381.fr',wire]]
pi = save('producer-inputs.json',producer_inputs)
proof = a.output / 'messages.proof'
produced = run([a.zkc,'produce-artifact',*messages,pi,a.compiler,a.lean,proof,'4'],'messages-produce')
assert produced['status'] == 'produced' and produced['messages'] == 4
validated = run([a.zkc,'validate-artifact',*messages,vi,a.compiler,a.lean,proof,'4'],'messages-validate')
assert validated['code'] == 'exhausted:observer-bytes'
assert len(validated['events']) == 3 and all(e[0]=='message' for e in validated['events'])
assert [r['transitions'] for r in validated['resources'] if r['port'].startswith('transcript:')] == [3]
assert validated['runtime']['active_frames'] == 0

draws = compile_case('Draws',[
    ['function','Draw',[['r','rng']],['field','rng'],[
        ['op','draw','random.draw',[],['r'],['c','next']],['return',['c','next']]]]],base_ports,
    [['loop','repetitions',['constant','20000'],[['r','coins']],[],[
        ['local','draw','V','Draw',['r'],['c','next']],['yield',['next']]],['last']],
     ['return',['ok','last']]], [['Draw','draw']])
proof = a.output / 'draws.proof'
produced = run([a.zkc,'produce-artifact',*draws,vi,a.compiler,a.lean,proof,'20000'],'draws-produce')
assert produced['status'] == 'produced'
validated = run([a.zkc,'validate-artifact',*draws,vi,a.compiler,a.lean,proof,'20000'],'draws-validate')
assert validated['code'] == 'exhausted:observer-bytes', validated['code']
events = validated['events']
assert events and len(events)%3 == 0
assert all(e[0]==['request','challenge','response'][i%3] for i,e in enumerate(events))
assert [r['transitions'] for r in validated['resources'] if r['port'].startswith('transcript:')] == [len(events)//3]
assert validated['runtime']['active_frames'] == 0

# Same 16.5 MB shape as the review countermodel, and an independent primitive
# ingress with a still larger declared byte bound. Neither can allocate the
# 5.5 million-node serde tree. Do not equate measured RSS with a formal bound.
candidate = a.output/'oversized-tree.json'
payload = b'[['+b'[],'*5499999+b'[]]]'
candidate.write_bytes(payload)
paths = list(messages); paths[2] = candidate
r = run([a.zkc,'validate-artifact',*paths,vi,a.compiler,a.lean,proof,'0'],'json-host')
assert r['code']=='tree-limit'
r = run([a.primitive,candidate],'json-primitive')
assert r == ['error','primitive-json-limit'], r
save('summary.json',{'status':'pass','checks':checks,'commands':commands,
     'tools':{n:{'path':str(getattr(a,n)), 'sha256':hashlib.sha256(getattr(a,n).read_bytes()).hexdigest()}
              for n in ['zkc','compiler','lean','primitive']}})
print(json.dumps({'status':'pass','checks':len(checks)}))
