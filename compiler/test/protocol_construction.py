#!/usr/bin/env python3
"""Actual C++ construction, independent structural observations, hostile subjects.

No research oracle is imported. Small counts are expanded only by this test
observer; the production input/output loops remain compact.
"""
import copy
from bls_fixture import module
import json
from pathlib import Path
from commands import Commands
from tools import compiler, corpus, examples, optimizer, records
from journal import names

root = Path(__file__).resolve().parents[2]
ARK = 'arkworks.multilinear.bls12-381/1'
commands = Commands(records())


def check(name, condition, **detail):
    commands.check(name, condition, detail or None)
    assert condition, (name, detail)


def run(tool, *args, ok=True, code=None, text=None):
    return commands.run([tool, *args], stdin=text,
                        refuses=None if ok else (code or True))


def walk(body):
    for op in body:
        yield op
        if op[0] == 'loop':
            yield from walk(op[5])


def program(source, entry='main'):
    instances = {i[1]: i for i in source[4]}
    defs = {p[1]: p for p in source[3]}
    selected = next(e[2] for e in source[5] if e[1] == entry)
    return instances, defs, selected


def semantic_operations(source):
    source = copy.deepcopy(source)
    contracts = {b[0]: b[1] for b in source[1]}
    for function in source[2]:
        for op in function[4]:
            if op[0] == 'op':
                op[2] = contracts[op[2]]
    return source


def observed(source, mappings=None):
    source = semantic_operations(source)
    """Independent finite source-order observer, never compiler dependency sets."""
    instances, defs, selected = program(source)
    functions = {f[1]: f for f in source[2]}
    origins = {(m[0], m[1]): m for m in mappings or []}
    events = {'P': [], 'V': []}

    def block(inst, body, path):
        roles = dict(inst[5])
        for op in body:
            if op[0] == 'local':
                role = roles[op[2]]
                for k in functions[op[3]][4]:
                    if k[0] != 'op':
                        continue
                    origin = origins.get((op[3], k[1]))
                    if mappings is not None:
                        if origin is None:
                            raise AssertionError(('missing origin', op, k))
                        # Compare original operations; selected V draws map to
                        # transcript.challenge at exactly their source position.
                        if origin[7] == 'recipe' or (origin[7] == 'construction' and
                              (k[2] != 'transcript.challenge' or role == 'P')):
                            continue
                        fn, site, call = origin[4], origin[5], origin[3]
                        key = 'random.draw' if k[2] == 'transcript.challenge' else k[2]
                    else:
                        fn, site, call, key = op[3], k[1], op[1], k[2]
                    events[role].append([inst[1], path, call, fn, site, key])
            elif op[0] == 'call':
                child = instances[dict(inst[4])[op[2]]]
                block(child, defs[child[2]][7], path + [['call', op[1], child[1]]])
            elif op[0] == 'loop':
                n = int(dict(inst[3])[op[2][1]] if op[2][0] == 'parameter' else op[2][1])
                assert n < 10, 'bounded test observer only'
                for iteration in range(n):
                    block(inst, op[5], path + [['loop', op[1], str(iteration)]])
    inst = instances[selected]
    block(inst, defs[inst[2]][7], [])
    return events


def frames(source, constructed=False):
    source = semantic_operations(source)
    instances, defs, selected = program(source)
    functions = {f[1]: f for f in source[2]}
    result = {'P': [], 'V': []}
    def visit(inst, body, path):
        roles = dict(inst[5])
        for op in body:
            if op[0]=='message' and not constructed:
                origin=[defs[inst[2]][1],op[1],op[2],op[3],op[4]]
                for role in result: result[role].append([inst[1],path,'message',origin])
            elif op[0]=='local':
                for k in functions[op[3]][4]:
                    if k[0]!='op':continue
                    if constructed and k[2].startswith('transcript.'):
                        kind='challenge' if k[2]=='transcript.challenge' else 'message'
                        result[roles[op[2]]].append([inst[1],path,kind,k[3]])
                    elif not constructed and roles[op[2]]=='V' and k[2]=='random.draw':
                        origin=[defs[inst[2]][1],op[1],op[3],k[1],op[2]]
                        for role in result: result[role].append([inst[1],path,'challenge',origin])
            elif op[0]=='call':
                child=instances[dict(inst[4])[op[2]]]
                visit(child,defs[child[2]][7],path+[['call',op[1],child[1]]])
            elif op[0]=='loop':
                n=int(dict(inst[3])[op[2][1]] if op[2][0]=='parameter' else op[2][1])
                assert n<10
                for iteration in range(n):visit(inst,op[5],path+[['loop',op[1],str(iteration)]])
    inst=instances[selected];visit(inst,defs[inst[2]][7],[])
    return result


def descriptor(public=(), draw=(), rng='coins'):
    return ['zkc.construction/1', 'main', 'P', 'V',
            [[p, [['V', p]]] for p in public], [rng, [list(d) for d in draw]],
            '0', 'merlin3.bls12-381.fr64be/1', 'exact']


OK_FN = ['function', 'Accept', [], ['bool'], [
    ['op', 'zero', 'field.constant', ['0'], [], ['z']],
    ['op', 'eq', 'field.equal', [], ['z', 'z'], ['ok']], ['return', ['ok']]]]
DRAW_FN = ['function', 'Draw', [['rng', 'rng']], ['field', 'rng'], [
    ['op', 'draw', 'random.draw', [], ['rng'], ['r', 'after']], ['return', ['r', 'after']]]]


def small(ports, body, functions=(), returns=()):
    # Every descriptor designates a real V RNG and a real Boolean acceptance.
    ports = copy.deepcopy(ports)
    if not any(p[0] == 'coins' for p in ports):
        ports.append(['coins', 'V', 'rng'])
    body = copy.deepcopy(body) + [['local', 'accept', 'V', 'Accept', [], ['accepted']],
                                  ['return', ['accepted', *returns]]]
    output_types = [['V', 'bool']] + [['V', 'rng'] for _ in returns]
    return module([copy.deepcopy(OK_FN), *copy.deepcopy(functions)],
            [['protocol', 'Subject', ['P', 'V'], [], ports, output_types, [], body]],
            [['instance', 'subject', 'Subject', [], [], [['P', 'P'], ['V', 'V']]]],
            [['entry', 'main', 'subject']])


tmp = records()
tmp = Path(tmp)

save = commands.write

def construct(source, desc, name, ok=True, code=None, stages=True):
    src, des = save('source.json', source), save('descriptor.json', desc)
    output = run(compiler, 'protocol-construct', src, des, ok=ok, code=code)
    if not ok:
        # run() has already required the refusal; this names which one it was,
        # read back from what the compiler said rather than assumed from
        # having got here.
        check(name, names(commands.last.stderr, code), refusal=code)
        return None
    result = json.loads(output)
    check(name, len(result)==6 and result[0] == 'zkc.construction-result/1' and result[1] == desc)
    candidate = save('candidate.json', result)
    run(compiler, 'protocol-check-construction', src, des, candidate)
    common = save('constructed.json', result[2])
    if stages:
        ir = run(compiler, 'protocol-construct-ir', src, des)
        ir_path = tmp / 'constructed.mlir'; ir_path.write_text(ir)
        exported = json.loads(run(compiler, 'protocol-export', ir_path))
        projected_ir = run(optimizer, '--zkc-project-participants', ir_path)
        pi = tmp / 'projected.mlir'; pi.write_text(projected_ir)
        physical_ir = run(optimizer, '--zkc-plan-participants', pi)
        phy = tmp / 'physical.mlir'; phy.write_text(physical_ir)
        physical = json.loads(run(compiler, 'protocol-export', phy))
        check(name+'-separate-stages', physical == json.loads(run(compiler, 'protocol-compile', common)))
        check(name+'-inspectable', 'pir.transcript_' in ir or not result[4])
        run(compiler, 'protocol-project', save('reexported.json', exported))
    return result

for name in ['two-factor', 'committed-two-factor', 'dleq']:
    source = json.loads((examples / f'{name}.json').read_text())
    desc = json.loads((examples / f'{name}.construction.json').read_text())
    # These checks read the author's site labels back from the origins, which
    # exact identity keeps; normalized identity replaces them with positions.
    desc[8] = 'exact'
    result = construct(source, desc, name)
    check(name+'-preserves-every-source-operation-in-order', observed(source) == observed(result[2], result[4]))
    check(name+'-exact-frame-history-both-roles', frames(source) == frames(result[2], True))
    instances, defs, selected = program(result[2])
    reachable = set()
    def visit(i):
        if i in reachable: return
        reachable.add(i)
        for _, child in instances[i][4]: visit(child)
    visit(selected)
    instructions = [op for i in reachable for op in walk(defs[instances[i][2]][7])]
    check(name+'-erases-live-validator-delivery', all(op[0] != 'message' or op[3] == 'P' for op in instructions))
    check(name+'-threads-two-transcripts', all(sum(p[2].startswith('transcript:') for p in defs[instances[i][2]][4]) == 2 for i in reachable))
    fn = {f[1]: f for f in result[2][2]}
    recipes = [fn[m[0]][4][0][2] for m in result[4] if m[7] == 'recipe']
    check(name+'-producer-does-not-replay-checks', not {'control.require', 'pcs.check'}.intersection(recipes))
    params = [f[4][0][3] for f in result[2][2] if f[4][0][0] == 'op' and dict((b[0], b[1]) for b in result[2][1])[f[4][0][2]] == 'transcript.challenge']
    check(name+'-source-challenge-identity', all(len(p) == 5 and not any(x.startswith('constructed_') for x in p) for p in params))
    check(name+'-checked-acceptance-result-mapping',
          ['V','0',['source','0']] in result[5] and
          ['V','1',['transcript']] in result[5])
    if name == 'committed-two-factor':
        events = observed(source)['V']; keys = [v[-1] for v in events]
        check('commitment-guards-before-challenges', keys[:4] == ['pcs.equal', 'control.require', 'pcs.equal', 'control.require'] and keys.index('random.draw') > 3)
        check('claim-and-roots-public-bindings', [x[0] for x in result[1][4]] == ['claim', 'expected_f', 'expected_g'])
        check('keys-remain-source-configuration-inputs', all(x[2][0] == 'source' for x in result[3] if x[1] in ['pk', 'vk']))
    if name == 'dleq':
        check('repeated-child-instance-retained', [o[1] for o in defs[instances[selected][2]][7] if o[0] == 'call'] == ['first', 'second'])
        check('dleq-vector-nonce-commitment', sum(v[-1] == 'curve.commit' for v in observed(source)['P']) == 2)
        check('dleq-four-actual-group-equations', sum(v[-1] == 'curve.equal' for v in observed(source)['V']) == 4)
    # Independently authored corruption: still-typed removal of a V guard,
    # origin substitutions, and reordered effects must fail correspondence.
    for mutation in ['drop-guard', 'drop-observation', 'origin', 'entry-map', 'result-map', 'descriptor']:
        bad = copy.deepcopy(result)
        if mutation == 'drop-guard':
            chosen = next(m for m in bad[4] if m[7] == 'original' and any(
                op[0] == 'op' and op[1] == m[1] and dict((b[0], b[1]) for b in bad[2][1])[op[2]] == 'control.require'
                for op in fn[m[0]][4]))
            f = next(f for f in bad[2][2] if f[1] == chosen[0])
            f[4] = [op for op in f[4] if not (op[0] == 'op' and op[1] == chosen[1])]
            run(compiler, 'protocol-project', save('typed-corruption.json', bad[2]))
        elif mutation == 'drop-observation':
            f=next(f for f in bad[2][2] if f[4][0][0]=='op' and dict((b[0], b[1]) for b in bad[2][1])[f[4][0][2]].startswith('transcript.observe.'))
            f[4]=[['return',[f[2][0][0]]]]
            run(compiler,'protocol-project',save('typed-corruption.json',bad[2]))
            check(name+'-independent-observer-sees-missing-frame',frames(source)!=frames(bad[2],True))
        elif mutation == 'origin': bad[4][0][5] = 'substituted'
        elif mutation == 'entry-map': bad[3][0][2] = ['public', 'unbound']
        elif mutation == 'result-map': bad[5][0][1]='999'
        else: bad[1][7] = 'different-suite'
        run(compiler, 'protocol-check-construction', save('source.json', source), save('descriptor.json', desc), save('bad-result.json', bad), ok=False, code='construction-candidate-mismatch')
        check(name+'-rejects-'+mutation, names(commands.last.stderr, 'construction-candidate-mismatch'))

base = json.loads((examples/'two-factor.json').read_text())
base_desc = json.loads((examples/'two-factor.construction.json').read_text())
base_desc[8] = 'exact'  # The order checks read the author's site labels.
sizes = []
for n in [0, 1, 2, 4, 1000000]:
    source = copy.deepcopy(base)
    for i in source[4]:
        for b in i[3]: b[1] = str(n)
    result = construct(source, base_desc, f'compact-two-factor-{n}', stages=n in [0, 1, 1000000])
    sizes.append(len(json.dumps(result)))
    if n < 10: check(f'count-{n}-operation-order', observed(source) == observed(result[2], result[4]))
check('million-count-output-compact', max(sizes[1:])-min(sizes[1:]) < 100 and max(sizes) < 60000, bytes=sizes)

for n in [0, 1, 2, 1000000]:
    body = [['loop','repeat',['constant',str(n)],[['x','public']],['secret'],[
        ['message','query','field','V','P','x','seen'],['yield',['secret']]],['last']]]
    source = small([['public','V','field'],['secret','V','field']], body)
    construct(source, descriptor(['public']), f'private-backedge-{n}', ok=n<2, code=None if n<2 else 'construction-private-demand', stages=False)
for n in [0, 1, 2, 1000000]:
    body = [['loop','repeat',['constant',str(n)],[['a','coins'],['b','private']],[],[
        ['local','sample','V','Draw',['a'],['r','after']],
        ['message','challenge','field','V','P','r','p_r'],['yield',['b','after']]],['last_a','last_b']]]
    source = small([['coins','V','rng'],['private','V','rng']], body, [DRAW_FN], ['last_a','last_b'])
    construct(source, descriptor(draw=[('Draw','draw')]), f'actual-resource-swap-{n}', ok=n<2, code=None if n<2 else 'construction-private-rng', stages=False)
body = [['loop','repeat',['constant','1000000'],[['a','first'],['b','second']],[],[['yield',['b','a']]],['last_a','last_b']]]
source = small([['first','V','rng'],['second','V','rng']],body,returns=['last_a','last_b'])
construct(source,descriptor(),'unrelated-affine-permutation',stages=False)

guard = ['function','Guarded',[['x','field']],['field'],[
    ['op','eq','field.equal',[],['x','x'],['ok']],['op','guard','control.require',[],['ok'],[]],['return',['x']]]]
source = small([['public','V','field']], [['local','guarded','V','Guarded',['public'],['out']],['message','echo','field','V','P','out','received']], [guard])
result = construct(source,descriptor(['public']),'guarded-raw-operand',stages=False)
check('guard-not-in-raw-recipe', not any(m[7]=='recipe' and m[5]=='guard' for m in result[4]))
construct(source,descriptor(),'missing-public-binding',ok=False,code='construction-private-demand',stages=False)
source[2][1][4][-1] = ['return',['ok']]; source[2][1][3] = ['bool']
# field.equal is an admitted executable recipe even after an unrelated guard.
construct(source,descriptor(['public']),'guarded-public-equality',stages=False)

source = copy.deepcopy(base)
fn = next(f for f in source[2] if f[1]=='CheckOpening')
fn[3]=['bool'];fn[4][-1]=['return',['valid']]
source[3][1][5]=[['V','bool']]
source[3][1][7].insert(-1,['message','checked','boolean','V','P','checked_value','p_checked'])
# Adapt the caller's terminal to bool inputs without changing PCS semantics.
terminal=next(f for f in source[2] if f[1]=='CheckTerminal')
terminal[2]=[['a','bool'],['b','bool'],['claim','field:bls12-381.fr']]
source[1].append(['bool.and', 'bool.and', [], ''])
terminal[4]=[['op','and','bool.and',[],['a','b'],['ok']],['return',['ok']]]
construct(source,base_desc,'demanded-pcs-check-result',ok=False,code='construction-unavailable-recipe:pcs.check',stages=False)

# Explicit public immutable P/V port equality, independent of name spelling.
source = small([['p','P','field'],['v','V','field']], [['message','echo','field','V','P','v','seen']])
d=descriptor();d[4]=[['statement',[['P','p'],['V','v']]]]
result=construct(source,d,'public-equality-port-pair',stages=False)
check('equality-reuses-existing-producer-port', not any(m[2][0]=='public' for m in result[3]))

# Source identity includes unused instance parameter bindings, rather than
# only the executable entry projection.
unused=copy.deepcopy(base); extra=copy.deepcopy(unused[4][0]);extra[1]='unused';unused[4].append(extra)
before=construct(unused,base_desc,'whole-source-identity',stages=False)
unused[4][-1][3][0][1]='2'
run(compiler,'protocol-check-construction',save('changed-source.json',unused),save('descriptor.json',base_desc),save('old-result.json',before),ok=False,code='construction-candidate-mismatch')
check('unused-instance-change-is-bound',names(commands.last.stderr, 'construction-candidate-mismatch'))

for kind in ['derived', 'nested']:
    specimen = corpus / ('construction-'+kind+'.json')
    source = json.loads(specimen.read_text())
    result = construct(source, base_desc, kind+'-source-specimen', stages=True)
    check(kind+'-preserves-original-operation-order', observed(source) == observed(result[2], result[4]))
    if kind == 'nested':
        for n in [0, 1, 1000000]:
            case = copy.deepcopy(source); case[3][-1][7][0][2] = ['constant', str(n)]
            construct(case,base_desc,f'nested-wrapper-{n}',stages=True)

source = copy.deepcopy(base);d=copy.deepcopy(base_desc)
for i in source[4]: i[5] = [[formal, {'P':'Alice','V':'Bob'}[actual]] for formal,actual in i[5]]
d[2:4]=['Alice','Bob'];d[4][0][1][0][0]='Bob'
result=construct(source,d,'resolved-nonidentity-roles',stages=True)
params=[f[4][0][3] for f in result[2][2] if f[4][0][0]=='op' and dict((b[0], b[1]) for b in result[2][1])[f[4][0][2]].startswith('transcript.')]
check('nonidentity-roles-preserve-formal-origin-names',all(p[-1] in ['P','V'] for p in params) and all('Alice' not in p and 'Bob' not in p for p in params))

# Exact one: a private initial field/bool is overwritten by a public local
# result before it is demanded. No arbitrary invariant is imposed.
for typ in ['field','bool']:
    local = ['local','make','V','Accept',[],['new']] if typ=='bool' else ['local','make','V','Zero',[],['new']]
    fns=[] if typ=='bool' else [['function','Zero',[],['field'],[['op','zero','field.constant',['0'],[],['z']],['return',['z']]]]]
    source=small([['private','V',typ]],[['loop','once',['constant','1'],[['x','private']],[],[local,['yield',['new']]],['last']],['message','result',typ,'V','P','last','received']],fns)
    construct(source,descriptor(),f'exact-once-new-{typ}-result',stages=False)

# An output proof whose seed is not representable is refused as such, rather
# than being given a fabricated initial proof value or reported as a
# private-dependency finding.
openfn=['function','Open',[['state','opening_state'],['point','point']],['field','proof'],[
  ['op','open','pcs.open',[],['state','point'],['value','proof']],['return',['value','proof']]]]
source=small([['private_proof','V','proof'],['state','P','opening_state'],['point','P','point']],
  [['loop','once',['constant','1'],[['x','private_proof']],['state','point'],[
   ['local','open','P','Open',['state','point'],['value','new_proof']],
   ['message','proof','proof','P','V','new_proof','received'],['yield',['received']]],['last']],
   ['message','echo','proof','V','P','last','p_last']],[openfn])
construct(source,descriptor(),'exact-once-output-proof-without-seed',ok=False,code='construction-single-loop-seed',stages=False)

source=copy.deepcopy(base)
mixed=next(f for f in source[2] if f[1]=='CheckRoundAndDraw')
draw=next(op for op in mixed[4] if op[0]=='op' and op[2]=='random.draw')
mixed[4].remove(draw);mixed[4].insert(0,draw)
result=construct(source,base_desc,'source-draw-before-guard',stages=False)
check('source-draw-before-guard-keeps-failure-prefix',observed(source)==observed(result[2],result[4]))
source=small([['secret_rng','V','rng']],[['local','private','V','Draw',['secret_rng'],['r','after']]],[DRAW_FN])
construct(source,descriptor(draw=[('Draw','draw')]),'selected-site-with-private-root',ok=False,code='construction-private-rng',stages=False)
source=small([['p_rng','P','rng']],[['local','private','P','Draw',['p_rng'],['r','after']]], [DRAW_FN])
result=construct(source,descriptor(draw=[('Draw','draw')]),'producer-private-draw-retained',stages=False)
check('producer-draw-does-not-become-transcript',not any(m[7]=='construction' for m in result[4]))

source=copy.deepcopy(base);d=copy.deepcopy(base_desc)
source[3][-1][5].reverse();source[3][-1][7][-1][1].reverse();d[6]='1'
result=construct(source,d,'acceptance-after-rng-result',stages=False)
check('acceptance-after-rng-explicit-map',['V','0',['source','1']] in result[5])

source=json.loads((corpus / "construction-nested.json").read_text())
source[3][-1][7][0][2]=['constant','0']
d=copy.deepcopy(base_desc)
for i in source[4]:i[5]=[[formal,{'P':'Alice','V':'Bob'}[actual]] for formal,actual in i[5]]
d[2:4]=['Alice','Bob'];d[4][0][1][0][0]='Bob'
construct(source,d,'zero-loop-nested-remapped-roles',stages=False)

source=small([],[])
unused=small([['private','V','rng']],[['local','sample','V','Draw',['private'],['r','after']]],[DRAW_FN])
source[2].append(copy.deepcopy(next(f for f in unused[2] if f[1] == "Draw")))
source[1].extend(copy.deepcopy(b) for b in unused[1] if b[0] not in {old[0] for old in source[1]})
unused[3][0][1]='Unused';source[3].append(unused[3][0])
source[3][0][6]=[['unused','Unused',[]]]
source[4][0][4]=[['unused','unused']]
source[4].append(['instance','unused','Unused',[],[],[['P','P'],['V','V']]])
construct(source,descriptor(),'unused-private-dependency-is-not-rewritten',stages=False)

# Independent bounded availability oracle for two mutable slots. This
# enumerates actual transfers; it does not import the research analysis or
# share the production union/fixed-point algorithm.
choices=['a','b','public','secret']
for left in choices:
  for right in choices:
    for count in [0,1,2,3]:
      source=small([['public','V','field'],['secret','V','field']],
        [['loop','repeat',['constant',str(count)],[['a','public'],['b','secret']],['public','secret'],[
         ['message','query','field','V','P','a','received'],['yield',[left,right]]],['last_a','last_b']]])
      available={'a':True,'b':False,'public':True,'secret':False};safe=True
      for _ in range(count):
        safe &= available['a']
        available={**available,'a':available[left],'b':available[right]}
      src=save('oracle-source.json',source);des=save('descriptor.json',descriptor(['public']))
      proc=commands.attempt([compiler,'protocol-construct',src,des])
      assert proc.returncode in [0,1],proc.stderr
      if proc.returncode:assert names(proc.stderr, 'construction-private-demand'),proc.stderr
      check(f'bounded-availability-{left}-{right}-{count}',
            (safe or proc.returncode > 0) and (count>=2 or (proc.returncode==0)==safe),
            bounded_available=bool(safe),constructed=proc.returncode==0)

# Renaming a generated helper changes the prescribed candidate spelling but
# does not change either role's logical transcript frame history.
result=construct(base,base_desc,'helper-identity-subject',stages=False)
renamed=copy.deepcopy(result[2]);old=result[4][0][0];new='renamed_generated_helper'
next(f for f in renamed[2] if f[1]==old)[1]=new
for protocol in renamed[3]:
  for op in walk(protocol[7]):
    if op[0]=='local' and op[3]==old:op[3]=new
run(compiler,'protocol-project',save('renamed-helper.json',renamed))
check('generated-helper-name-not-in-transcript-identity',frames(result[2],True)==frames(renamed,True))


# Exact resource results use the real trip count, independently of the
# conservative availability invariant. No selected carrier escapes as an
# ordinary private RNG output, even through a cyclic slot permutation.
for n in [0,1,2,3,1000000,1000001]:
  source=small([['coins','V','rng'],['private','V','rng']],
    [['loop','swap',['constant',str(n)],[['a','coins'],['b','private']],[],[['yield',['b','a']]],['out_a','out_b']]],returns=['out_a','out_b'])
  result=construct(source,descriptor(),f'exact-resource-result-{n}',stages=False)
  retained='1' if n%2 else '2'
  removed='2' if n%2 else '1'
  check(f'exact-resource-result-map-{n}',
    ['V','1',['source',retained]] in result[5] and
    all(m[2]!=['source',removed] for m in result[5]))

source=json.loads((examples/'dleq.json').read_text());d=json.loads((examples/'dleq.construction.json').read_text())
source[3][-1][7][1][3][3]='nonce_first'
construct(source,d,'repeated-dleq-nonce-reuse',ok=False,code='interactive-resource-reuse',stages=False)

messages=[];previous='public';sender='V'
for k in range(3000):
  receiver='P' if sender=='V' else 'V';current=f'value{k}'
  messages.append(['message',f'message{k}','field',sender,receiver,previous,current])
  previous=current;sender=receiver
source=small([['public','V','field']],messages)
construct(source,descriptor(['public']),'message-output-module-limit',ok=False,code='construction-output:source-limit:module',stages=False)

source=small([['p','P','field'],['q','P','field'],['a','V','field'],['b','V','field']],
  [['message','echo_a','field','V','P','a','received_a'],['message','echo_b','field','V','P','b','received_b']])
d=descriptor();d[4]=[['statement / café',[['P','p'],['P','q'],['V','a'],['V','b']]]]
construct(source,d,'utf8-label-and-multiple-same-role-ports',stages=False)
d[4][0][0]='é';result=construct(source,d,'composed-unicode-label',stages=False)
different=copy.deepcopy(d);different[4][0][0]='e\u0301'
run(compiler,'protocol-check-construction',save('source.json',source),save('descriptor.json',different),save('result.json',result),ok=False,code='construction-candidate-mismatch')
check('unicode-labels-are-not-normalized',names(commands.last.stderr, 'construction-candidate-mismatch'))

# Descriptor and source malformations reach refusals, never a process signal.
# Each names the identifier it must refuse with: a shared prefix was matching
# the working directory's name rather than anything the compiler said.
malformed=[(None,'source-syntax'),([],'interactive-shape'),
  (['zkc.construction/1'],'construction-descriptor'),
  (copy.deepcopy(base_desc),'construction-public-binding')]
malformed[-1][0][4]=[['claim',[]]]
for n,(d,code) in enumerate(malformed):construct(base,d,f'malformed-descriptor-{n}',ok=False,code=code,stages=False)
for field,value,code in [(6,'00','construction-acceptance-index'),(6,'1','construction-acceptance-index'),(7,'other','construction-suite-or-roles'),(8,'other','construction-descriptor'),(8,'/2','construction-descriptor'),(5,['claim',[]],'construction-rng-port'),(5,['coins',[['CheckRoundAndDraw','missing']]],'construction-draw-selector')]:
    d=copy.deepcopy(base_desc);d[field]=value
    construct(base,d,f'descriptor-{field}-{value}',ok=False,code=code,stages=False)
d=copy.deepcopy(base_desc);d[4].append(copy.deepcopy(d[4][0]))
construct(base,d,'duplicate-public-label',ok=False,code='construction-public-binding',stages=False)
d=copy.deepcopy(base_desc);d[4]=[['coins',[['V','coins']]]]
construct(base,d,'private-capability-public-binding',ok=False,code='construction-public-binding',stages=False)
d=copy.deepcopy(base_desc);d[5][1]=[]
construct(base,d,'unselected-draw-site',ok=False,code='construction-unselected-draw',stages=False)
source=copy.deepcopy(base);source[2][3][4]='external'
construct(source,base_desc,'external-source',ok=False,code='interactive-external-body',stages=False)
source=copy.deepcopy(base);source[3][-1][7][-1]=['stop','unfinished','V','incomplete']
construct(source,base_desc,'incomplete-source',ok=False,code='construction-incomplete-control',stages=False)

print(f'protocol construction: {commands.save()} checks over {len(commands.checks)} named assertions')
