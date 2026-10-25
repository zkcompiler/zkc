"""Whole-original protocol repeats and independent contextual SSA execution."""
import hashlib
import json
from pathlib import Path

from cases import case, counted
from commands import Commands
from entry_artifacts import compile_run_package
from project import project_arguments
from tools import compiler, records

commands = Commands(records())
root = Path(__file__).resolve().parents[2]
reference = Path(compiler).parent / 'test/zkc-structured_reference-test'
field = ['field', 'bls12-381.fr']
service = 'random.bls12-381.fr/0'
P, V, W = (f'role{i:08x}' for i in range(3))
serial = 0
export_serial = 0


def export(source, symbol='main', refusal=None, keep=None):
    global export_serial
    export_serial += 1
    (commands.directory / f'export-{export_serial}.mlir').write_text(source)
    text = commands.source('protocol-structured', source, '--symbol=' + symbol,
                           refuses=refusal, keep=keep)
    if refusal:
        return None
    snapshot = json.loads(text)
    assert len(snapshot) == 10
    assert snapshot[2] == 'sha256:' + hashlib.sha256(source.encode()).hexdigest()
    assert all(len(row) == 10 for row in snapshot[7] if row[0] == 'function')
    return snapshot


def run(source, inputs, role='P', replies=(), symbol='main', refusal=None, capacity=1000000):
    global serial
    serial += 1
    path = commands.directory / f'repeat-{serial}.mlir'
    path.write_text(source)
    request = commands.write(f'repeat-{serial}.json',
                             ['zkc.structured-open-request/0', role, inputs, list(replies), capacity])
    text = commands.run([reference, 'open', path, symbol, request], refuses=refusal,
                        keep=f'repeat-{serial}-result.json')
    return None if refusal else json.loads(text)


def reply(action, value=None, stop=None):
    return ['reply', action, ['stop', stop] if stop else
            ['unit'] if action[0] == 'send' else ['value', value]]


def trace(replies):
    return [event for i, row in enumerate(replies)
            for event in [['request', i, row[1]], ['reply', i, row[2]]]]


def returned(values, replies=()):
    return ['zkc.structured-open-result/0', ['returned', values], trace(replies), len(replies)]


def stopped(reason, site, replies=(), extra=()):
    return ['zkc.structured-open-result/0', ['stopped', reason, site],
            trace(replies) + list(extra) + [['stop', reason, site, len(replies)]], len(replies)]


def frontend(path, entry='Demo', flags=None, label=None):
    flags = flags or [f'--module=sample={path}']
    label = label or path.stem + '-' + entry
    flags = ['--source-format=zkc', '--entry=' + ('example::' if path.name == 'main.zkc' else 'sample::') + entry, *flags]
    before = path.read_bytes()
    child = compile_run_package(commands, *flags)
    source = child['original']
    interface = json.loads(child['interface'])
    (commands.directory / (label + '.mlir')).write_text(source)
    (commands.directory / (label + '-interface.json')).write_text(child['interface'])
    assert path.read_bytes() == before
    snapshot = export(source, interface['protocol'], keep=label + '.snapshot.json')
    assert 'sha256:' + interface['original'] == snapshot[2]
    (commands.directory / (label + '.zkc')).write_bytes(before)
    return source, interface['protocol'], snapshot


def instructions(block):
    for instruction in block[1]:
        yield instruction
        for region in instruction[3]:
            yield from instructions(region[2])


def native(source, label):
    prepared = commands.verified(source, None, '--zkc-prepare-protocol')
    projected = commands.verified(prepared, None, '--zkc-project-protocol', '--zkc-lower-math')
    physical = commands.verified(projected, None, '--zkc-select-physical')
    for suffix, text in [('prepared', prepared), ('projected', projected), ('physical', physical)]:
        (commands.directory / f'{label}.{suffix}.mlir').write_text(text)
    return json.loads(commands.source('protocol-export', physical, keep=label + '.participants.json'))


repeat_source, repeat_symbol, repeat_snapshot = frontend(root / 'compiler/test/fixtures/language/repeat.zkc')
repeats = [i for d in repeat_snapshot[7] for i in instructions(d[9]) if i[0][0] == 'protocol_repeat']
[loop] = repeats
header = loop[4]
with case('unchanged-repeat-full-original-callback-and-independent-received-values'):
    assert loop[0] == ['protocol_repeat', 2, 4, [P, V], [[P], [V]]]
    assert len(loop[3]) == 1 and loop[3][0][2][2][0] == 'yield'
    assert loop[3][0][0] == [['index'], field, field, ['bool'], ['service', service]]
    calls = [i for i in instructions(loop[3][0][2]) if i[0][0] == 'protocol_apply']
    [call] = calls
    round_body = next(d[9] for d in repeat_snapshot[7] if d[1] == call[0][1])
    draw_site = next(i[4] for i in round_body[1] if i[0][0] == 'draw')
    send_site = next(i[4] for i in round_body[1] if i[0][0] == 'exchange')
    prefix = 'apply_' + str(len(call[4].encode())) + '_' + call[4] + '_'
    receive = ['receive', prefix + send_site, V, P, field]
    replies = [reply(receive, value) for value in ('5', '7')]
    assert run(repeat_source, ['2', '10', None, None, None], P, replies, repeat_symbol) == returned(['22', None], replies)
    replies = []
    for value in ('2', '3'):
        replies += [reply(['draw', prefix + draw_site, V, service, '9', 'bls12-381.fr'], value),
                    reply(['send', prefix + send_site, V, P, field, value])]
    assert run(repeat_source, ['2', None, '100', True, '9'], V, replies, repeat_symbol) == returned([None, '105'], replies)
    assert run(repeat_source, ['1', None, '100', True, '9'], V, replies, repeat_symbol) == returned([None, '102'], replies[:2])
    native(repeat_source, 'repeat')

with case('repeat-zero-missing-count-bound-and-late-provider-stop'):
    assert run(repeat_source, ['0', None, '100', None, None], V, symbol=repeat_symbol) == returned([None, '100'])
    assert run(repeat_source, [None, None, None, None, None], V, symbol=repeat_symbol) == stopped('incomplete', header)
    assert run(repeat_source, ['5', None, None, None, None], V, symbol=repeat_symbol) == stopped('refused', header)
    run(repeat_source, [str(1 << 64), None, None, None, None], V, symbol=repeat_symbol, refusal='structured-reference-input')
    guard_site = next(i[4] for i in loop[3][0][2][1] if i[0][0] == 'guard')
    assert run(repeat_source, ['1', None, '100', False, None], V, symbol=repeat_symbol) == stopped('reject', guard_site)
    first = [reply(['draw', prefix + draw_site, V, service, '9', 'bls12-381.fr'], '2'),
             reply(['send', prefix + send_site, V, P, field, '2'])]
    stop = reply(['draw', prefix + draw_site, V, service, '9', 'bls12-381.fr'], stop='abort')
    assert run(repeat_source, ['2', None, '100', True, '9'], V, [*first, stop, *first], repeat_symbol) == stopped('abort', prefix + draw_site, [*first, stop])

nested_source, nested_symbol, _ = frontend(root / 'compiler/test/fixtures/language/repeat_nested.zkc')
with case('unchanged-nested-repeat-count-capture-state-and-zero'):
    for n, m, x in [(2, 2, 3), (3, 1, 7), (0, None, 11), (1, 0, 5)]:
        expected = x * (1 + n * (m or 0))
        assert run(nested_source, [str(n), None if m is None else str(m), str(x)], P, symbol=nested_symbol) == returned([str(expected)])
    native(nested_source, 'repeat-nested')


# Handwritten original SSA controls keep the callback ABI visible and mutate
# one contract at a time. Native formation runs before both independent paths.
def protocol(name, body='', roles=('P', 'Q'), inputs=(('n', 'ui64', ('P',)), ('x', '!F', ('P',)), ('c', '!F', ('P',))),
             outputs=(('!F', ('P',)),), returns=('%r',)):
    ins = ','.join(t for _, t, _ in inputs)
    outs = ','.join(t for t, _ in outputs)
    args = ','.join(f'%{n}:{t}' for n, t, _ in inputs)
    return f'''"protocol.func"() ({{ ^entry({args}):
      {body}
      "protocol.return"({','.join(returns)}) : ({outs})->()
    }}) {{sym_name="{name}",origin=["{name}",[]],function_type=({ins})->({outs}),roles={json.dumps(roles)},
      input_roles={json.dumps([s for _, _, s in inputs])},
      output_roles={json.dumps([s for _, s in outputs])}}} : ()->()'''


def module(*definitions):
    return '''!F = !algebra.field<"bls12-381.fr">
!S = !protocol.service_ref<"random.bls12-381.fr/0">
module { "protocol.module"() ({
''' + '\n'.join(definitions) + '\n}) {profile=#protocol.profile<protocol>} : ()->() }'


def repeat(body='', yielded='%s', maximum=4):
    return f'''%r = "protocol.repeat"(%n,%x,%c) ({{
      ^body(%i:ui64,%s:!F,%capture:!F):
      {body}
      "protocol.yield"({yielded}) : (!F)->()
    }}) {{site="loop",carried=1:i64,maximum={maximum}:i64,roles=["P"],carried_roles=[["P"]]}} : (ui64,!F,!F)->!F'''


identity = module(protocol('main', repeat()))
with case('unused-absent-capture-zero-optional-state-and-outside-roster'):
    export(identity)
    assert run(identity, ['3', '7', None]) == returned(['7'])
    assert run(identity, ['0', None, None]) == returned([None])
    assert run(identity, [None, None, None], 'Q', capacity=4) == returned([None])
    replacement = module(protocol('main', repeat(yielded='%capture')))
    assert run(replacement, ['2', '7', '19']) == returned(['19'])
    native(identity, 'outside-repeat')

with case('outside-roster-skips-present-excess-count-inside-role-refuses'):
    source = module(protocol('main', repeat(), inputs=(
        ('n', 'ui64', ('P', 'Q')), ('x', '!F', ('P',)), ('c', '!F', ('P',)))))
    commands.verified(source)
    export(source)
    assert run(source, ['99', None, None], 'Q', capacity=4) == returned([None])
    assert run(source, ['99', '7', None], 'P') == stopped('refused', 'loop')

with case('zero-state-positive-effects-and-original-count-versus-index'):
    body = '''"protocol.repeat"(%n,%n) ({ ^body(%i:ui64,%original:ui64):
      %same = "data.index_equal"(%i,%original) : (ui64,ui64)->i1
      "protocol.guard"(%same) {owner="P",site="different"} : (i1)->()
      "protocol.yield"() : ()->()
    }) {site="loop",carried=0:i64,maximum=4:i64,roles=["P"],carried_roles=[]} : (ui64,ui64)->()'''
    source = module(protocol('main', body, inputs=(('n', 'ui64', ('P',)),), outputs=(), returns=()))
    export(source)
    assert run(source, ['0']) == returned([])
    assert run(source, ['2']) == stopped('reject', 'different')


def refuse(source, diagnostic='mathematical-formation', observed='structured-reference-source', invariant=None):
    export(source, refusal=diagnostic)
    exported = commands.last.stderr
    run(source, [], refusal=observed)
    if invariant:
        for tool, stderr in [('exporter', exported), ('reference', commands.last.stderr)]:
            assert invariant in stderr, (tool, invariant, stderr)


for label, old, new, diagnostic in [
    ('negative-carried', 'carried=1', 'carried=-1', 'mathematical-formation'),
    ('oversized-carried', 'carried=1', 'carried=3', 'mathematical-formation'),
    ('negative-maximum', 'maximum=4', 'maximum=-1', 'mathematical-formation'),
    ('oversized-maximum', 'maximum=4', 'maximum=1048577', 'mathematical-formation'),
    ('count-type', 'ui64', 'i1', 'mathematical-formation'),
    ('callback-type', '%i:ui64', '%i:i1', 'mathematical-formation'),
    ('yield-arity', '"protocol.yield"(%s) : (!F)', '"protocol.yield"() : ()', 'mathematical-formation'),
    ('yield-type', '"protocol.yield"(%s) : (!F)', '"protocol.yield"(%i) : (ui64)', 'mathematical-formation'),
    ('callback-return', '"protocol.yield"', '"protocol.return"', 'structured-source-original'),
    ('duplicate-roster', 'roles=["P"],carried', 'roles=["P","P"],carried', 'mathematical-formation'),
    ('empty-roster', 'roles=["P"],carried', 'roles=[],carried', 'mathematical-formation'),
    ('unknown-roster', 'roles=["P"],carried', 'roles=["R"],carried', 'mathematical-formation'),
    ('empty-state-scope', 'carried_roles=[["P"]]', 'carried_roles=[[]]', 'mathematical-formation'),
    ('unavailable-state-scope', 'carried_roles=[["P"]]', 'carried_roles=[["Q"]]', 'mathematical-formation'),
    ('unavailable-count', 'roles=["P"],carried', 'roles=["P","Q"],carried', 'mathematical-formation'),
]:
    with case(label + '-including-zero-maximum'):
        source = identity.replace(old, new)
        invariant = "'protocol.return' op expects parent op 'protocol.func'" if label == 'callback-return' else None
        refuse(source, diagnostic, invariant=invariant)
        if 'maximum' not in label:
            refuse(source.replace('maximum=4', 'maximum=0'), diagnostic, invariant=invariant)

with case('extra-repeat-attribute-refused-in-export-and-independent-admission'):
    source = identity.replace('site="loop"', 'foreign=true,site="loop"')
    refuse(source)

with case('free-ssa-capture-refused-even-at-zero'):
    refuse(identity.replace('"protocol.yield"(%s)', '"protocol.yield"(%x)').replace('maximum=4', 'maximum=0'),
           'structured-source-original', invariant="'protocol.yield' op using value defined outside the region")

with case('full-dormant-callback-and-stopped-suffix-remain-checked'):
    bad = repeat('%bad = "data.index"() {value="1",foreign=true} : ()->ui64', maximum=0)
    source = module(protocol('main', repeat()), protocol('dormant', bad))
    refuse(source)
    source = module(protocol('main', repeat('''%no = "arith.constant"() {value=false} : ()->i1
      "protocol.guard"(%no) {owner="P",site="stop"} : (i1)->()
      %bad = "data.index"() {value="1",foreign=true} : ()->ui64''')))
    refuse(source)

with case('native-valid-dormant-zero-callback-has-structured-unsupported-operation'):
    body = repeat('''%yes = "arith.constant"() {value=true} : ()->i1
      "protocol.finish_if"(%yes,%s) {owner="P",site="finish"} : (i1,!F)->()''', maximum=0)
    source = module(protocol('main', inputs=(), outputs=(), returns=()), protocol('dormant', body))
    commands.verified(source)
    refuse(source, 'structured-source-operation', 'structured-reference-unsupported', invariant='protocol.finish_if')

with case('repeat-header-body-and-sibling-site-collisions-at-zero'):
    source = module(protocol('main', repeat('''%yes = "arith.constant"() {value=true} : ()->i1
      "protocol.guard"(%yes) {owner="P",site="loop"} : (i1)->()''', maximum=0)))
    refuse(source)

with case('nested-application-roster-and-action-owner-cannot-widen'):
    source = module(protocol('main', repeat('''%yes = "arith.constant"() {value=true} : ()->i1
      "protocol.guard"(%yes) {owner="Q",site="escape"} : (i1)->()''', maximum=0)))
    refuse(source)
    child = protocol('child', '', inputs=(), outputs=(), returns=())
    source = module(child, protocol('main', repeat('''"protocol.apply"() {callee=@child,roles=["P","Q"],site="escape"} : ()->()''', maximum=0)))
    refuse(source)

with case('maximum-endpoints-visit-stored-body-once'):
    small = export(identity.replace('maximum=4', 'maximum=0'))
    large = export(identity.replace('maximum=4', 'maximum=1048576'))
    small[2], large[2] = '', ''
    small[7][0][9][1][0][0][2] = 1048576
    assert small == large


service_path = root / 'compiler/test/fixtures/structured-source/repeat-service-order.zkc'
service_source, service_symbol, service_snapshot = frontend(service_path)
service_body = next(d[9] for d in service_snapshot[7] if d[1] == service_symbol)
[service_loop] = [i for i in service_body[1] if i[0][0] == 'protocol_repeat']
pre, post = [i[4] for i in service_body[1] if i[0][0] == 'draw']
[service_call] = [i for i in service_loop[3][0][2][1] if i[0][0] == 'protocol_apply']
draw_body = next(d[9] for d in service_snapshot[7] if d[1] == service_call[0][1])
left, right = [i[4] for i in draw_body[1] if i[0][0] == 'draw']
[delivery] = [i[4] for i in draw_body[1] if i[0][0] == 'exchange']


def qualified(prefix, site):
    return f'apply_{len(prefix.encode())}_{prefix}_{site}'


for alias in (True, False):
    with case(f'whole-service-wrapper-shared-provider-state-and-alias-{alias}'):
        counts = [0, 0]
        replies, draws = [], []
        handles = [0, 0 if alias else 1]

        def draw(site, handle):
            counts[handle] += 1
            value = str(counts[handle])
            replies.append(reply(['draw', site, V, service, str(handle), 'bls12-381.fr'], value))
            draws.append(int(value))
            return int(value)

        total = draw(pre, 0)
        sent = []
        for _ in range(2):
            value = draw(qualified(service_call[4], left), handles[0])
            value += draw(qualified(service_call[4], right), handles[1])
            replies.append(reply(['send', qualified(service_call[4], delivery), V, P, field, str(value)]))
            sent.append(str(value))
            total += value
        total += draw(post, 0)
        assert counts == ([6, 0] if alias else [4, 2])
        assert run(service_source, ['2', '0', str(handles[1])], V, replies, service_symbol) == returned([None, str(total)], replies)
        received = [reply(['receive', qualified(service_call[4], delivery), V, P, field], v) for v in ('17', '23')]
        assert run(service_source, ['2', None, None], P, received, service_symbol) == returned(['40', None], received)
        # The unused scripted suffix makes both residual position and retained
        # prefix observable after stopping at the second callback query.
        stop = reply(replies[2][1], stop='abort')
        assert run(service_source, ['2', '0', str(handles[1])], V, [*replies[:2], stop, *replies[3:]], service_symbol) == stopped('abort', replies[2][1][1], [*replies[:2], stop])

with case('zero-count-keeps-prelude-and-suffix-queries'):
    replies = [reply(['draw', site, V, service, '0', 'bls12-381.fr'], value)
               for site, value in [(pre, '2'), (post, '7')]]
    assert run(service_source, ['0', '0', None], V, replies, service_symbol) == returned([None, '9'], replies)

with case('repeat-in-application-noninvolutive-three-role-map-and-top-down-label'):
    source, symbol, snapshot = frontend(service_path, 'Nested')
    body = next(d[9] for d in snapshot[7] if d[1] == symbol)
    [outer] = [i for i in body[1] if i[0][0] == 'protocol_apply']
    assert outer[0][2] == [W, P]
    action = ['receive', qualified(qualified(outer[4], service_call[4]), delivery), P, W, field]
    replies = [reply(action, '31'), reply(action, '37')]
    assert run(source, ['2', None, None, None], W, replies, symbol) == returned([None, None, '68'], replies)
    assert run(source, [None, '41', None, None], V, symbol=symbol) == returned([None, '41', None])
    native(source, 'repeat-service-nested')

with case('nested-statement-is-refused-in-zero-callback'):
    relation = 'relation.declare @R {kind="external",key="r",revision="0",signature=(!F)->i1,purposes=["statement"]}'
    statement = '"protocol.statement"(%capture) {relation=@R,selectors=["P"],acceptance=0:i64} : (!F)->()'
    source = module(relation, protocol('main', repeat(statement, maximum=0) + '\n%ok = "arith.constant"() {value=true} : ()->i1',
                      outputs=(('i1', ('P',)),), returns=('%ok',)))
    refuse(source, 'structured-source-original',
           invariant="'protocol.statement' op expects parent op 'protocol.func'")

with case('generated-collision-in-repeat-is-checked-even-at-zero'):
    child = protocol('child', '%yes = "arith.constant"() {value=true} : ()->i1\n"protocol.guard"(%yes) {owner="P",site="C"} : (i1)->()',
                     roles=('P',), inputs=(), outputs=(), returns=())
    body = '\n'.join(['"protocol.apply"() {callee=@child,roles=["P"],site="A"} : ()->()',
                      '%yes = "arith.constant"() {value=true} : ()->i1',
                      '"protocol.guard"(%yes) {owner="P",site="apply_1_A_C"} : (i1)->()'])
    source = module(child, protocol('main', repeat(body, maximum=0)))
    commands.verified(source)
    commands.verified(source, 'mathematical-formation', '--zkc-prepare-protocol')
    refuse(source, 'structured-source-site', 'structured-reference-site')
    # A surviving repeat header also claims its effective label. The erased
    # application header does not hide the collision with the child's body.
    header = module(child, protocol('main', repeat(
        '"protocol.apply"() {callee=@child,roles=["P"],site="A"} : ()->()', maximum=0)))
    header = header.replace('site="loop"', 'site="apply_1_A_C"')
    commands.verified(header)
    commands.verified(header, 'mathematical-formation', '--zkc-prepare-protocol')
    refuse(header, 'structured-source-site', 'structured-reference-site')

for label, path, entry, maximum in [
    ('reduction', root / 'examples/projects/sumcheck/composed/main.zkc', 'Reduction', 4),
    ('sumcheck', root / 'examples/projects/sumcheck/main.zkc', 'Interactive', 2),
]:
    with case('whole-original-' + label + '-capture-and-independent-admission'):
        source, symbol, snapshot = frontend(path, entry, project_arguments(path.with_name('zkc.toml')), label)
        loops = [(d, i) for d in snapshot[7] if d[0] == 'function' and d[2] == 'protocol'
                 for i in instructions(d[9]) if i[0][0] == 'protocol_repeat']
        [(reduction, loop)] = loops
        assert loop[0] == ['protocol_repeat', 6, maximum, [P, V], [[P], [P], [P], [P], [V], [V]]]
        assert len(loop[3][0][0]) == 8 and loop[3][0][0][-1] == ['service', service]
        assert reduction[9][2] == ['return', [3, 0, 1, 2, 4, 5]]
        # Admission validates every dormant declaration before optional zero
        # execution. Full symbolic Sumcheck equations are a subsequent package.
        inputs = [None, None, '9', '0', None] if label == 'reduction' else [['7'], '7', '0', None]
        expected = [None, None, [], '9'] if label == 'reduction' else [True]
        assert run(source, inputs, V, symbol=symbol) == returned(expected)



def empty_repeat(body, site, count='%n', capture='%n'):
    body = body.replace('%n', f'%count_{site}')
    return f'''"protocol.repeat"({count},{capture}) ({{ ^body(%i_{site}:ui64,%count_{site}:ui64):
      {body}
      "protocol.yield"() : ()->()
    }}) {{site="{site}",carried=0:i64,maximum=0:i64,roles=["P"],carried_roles=[]}} : (ui64,ui64)->()'''


def depth_source(depth, per_function):
    definitions = []
    parts = (depth + per_function - 1) // per_function
    for i in reversed(range(parts)):
        body = '' if i == parts - 1 else f'"protocol.apply"(%n) {{callee=@f{i+1},roles=["P"],site="A"}} : (ui64)->()'
        for j in range(min(per_function, depth - i * per_function)):
            body = empty_repeat(body, f'r{j}')
        definitions.append(protocol('main' if i == 0 else f'f{i}', body, roles=('P',),
                                    inputs=(('n', 'ui64', ('P',)),), outputs=(), returns=()))
    return module(*definitions)


for depth in (64, 65):
    with case(f'effective-repeat-depth-through-applications-{depth}'):
        source = depth_source(depth, 2)
        commands.verified(source)
        if depth == 64:
            export(source)
            assert run(source, ['0']) == returned([])
            # Repeat formation admits 64; the independent native preparation
            # correspondence checker has its own region/application budget.
            commands.verified(source, 'mathematical-correspondence', '--zkc-prepare-protocol')
        else:
            commands.verified(source, 'mathematical-formation', '--zkc-prepare-protocol')
            refuse(source, 'structured-source-limit', 'structured-reference-capacity')

with case('lexical-wire-nesting-is-separate-from-native-repeat-depth'):
    def array_depth(value):
        return 1 + max((array_depth(v) for v in value), default=0) if isinstance(value, list) else 0

    boundary = None
    previous = None
    for depth in range(1, 16):
        source = depth_source(depth, depth)
        commands.verified(source)
        # Actual native verification remains valid past the wire boundary.
        path = commands.directory / f'depth-{depth}.mlir'
        path.write_text(source)
        result = commands.attempted(compiler, 'protocol-structured', path, '--symbol=main')
        if result.returncode:
            assert 'structured-source-limit' in result.stderr
            boundary = depth
            assert depth > 1 and array_depth(previous) <= 64
            break
        previous = json.loads(result.stdout)
    assert boundary is not None
    commands.write('wire-depth-boundary.json', {'first_refused_repeat_depth': boundary,
                                              'last_admitted_array_depth': array_depth(previous),
                                              'native_repeat_limit': 64})


with case('nested-immutable-service-captures-preserve-entry-origin'):
    body = '''%r = "protocol.repeat"(%n,%x,%first,%second) ({
      ^outer(%i:ui64,%state:!F,%a:!S,%b:!S):
      %one = "data.index"() {value="1"} : ()->ui64
      %y = "protocol.repeat"(%one,%state,%b,%a) ({
        ^inner(%j:ui64,%s:!F,%right:!S,%left:!S):
        %q = "protocol.query"(%left) {owner="P",method="draw",site="q"} : (!S)->!F
        %v = "protocol.query"(%right) {owner="P",method="draw",site="v"} : (!S)->!F
        %sum = "algebra.field_add"(%q,%v) : (!F,!F)->!F
        "protocol.yield"(%sum) : (!F)->()
      }) {site="inner",carried=1:i64,maximum=1:i64,roles=["P"],carried_roles=[["P"]]} : (ui64,!F,!S,!S)->!F
      "protocol.yield"(%y) : (!F)->()
    }) {site="outer",carried=1:i64,maximum=2:i64,roles=["P"],carried_roles=[["P"]]} : (ui64,!F,!S,!S)->!F'''
    ports = (('n', 'ui64', ('P',)), ('x', '!F', ('P',)), ('first', '!S', ('P',)), ('second', '!S', ('P',)))
    source = module(protocol('main', body, inputs=ports))
    export(source)
    replies = [reply(['draw', site, 'P', service, handle, 'bls12-381.fr'], value)
               for site, handle, value in [('q', '11', '2'), ('v', '17', '3'), ('q', '11', '5'), ('v', '17', '7')]]
    assert run(source, ['2', '0', '11', '17'], replies=replies) == returned(['12'], replies)
    # Swapping two typed captures changes routing, without changing lexical
    # owner facts or creating fresh service state at the callback boundary.
    changed = source.replace('%state,%b,%a', '%state,%a,%b')
    export(changed)
    assert run(changed, ['2', '0', '11', '17'], replies=replies) == stopped('refused', 'q', extra=[['request', 0, ['draw', 'q', 'P', service, '17', 'bls12-381.fr']]])
    forged = source.replace('owner="P",method="draw",site="q"', 'owner="Q",method="draw",site="q"')
    refuse(forged)

with case('service-cannot-be-carried-even-at-maximum-zero'):
    source = module(protocol('main', '''%r = "protocol.repeat"(%n,%x) ({ ^body(%i:ui64,%s:!S):
      "protocol.yield"(%s) : (!S)->()
    }) {site="loop",carried=1:i64,maximum=0:i64,roles=["P"],carried_roles=[["P"]]} : (ui64,!S)->!S''',
        inputs=(('n', 'ui64', ('P',)), ('x', '!S', ('P',))), outputs=(), returns=()))
    refuse(source)

with case('helper-stops-inside-repeat-keep-raw-helper-label'):
    helper = 'local.func @stop() attributes {logical_origin=["stop",[]]} { "local.stop"() {reason="abort",site="raw"} : ()->() }'
    body = repeat('"protocol.local_call"() {callee=@stop,role="P",site="call"} : ()->()')
    child = protocol('child', body)
    caller = protocol('main', '%r = "protocol.apply"(%n,%x,%c) {callee=@child,roles=["P","Q"],site="A"} : (ui64,!F,!F)->!F')
    source = module(helper, child, caller)
    export(source)
    assert run(source, ['1', '7', None]) == stopped('abort', 'raw')

for label, replacement in [('unresolved', 'missing'), ('cyclic', 'main')]:
    with case(label + '-call-in-zero-repeat'):
        source = module(protocol('main', repeat(f'%ignored = "protocol.apply"(%i,%s,%capture) {{callee=@{replacement},roles=["P"],site="A"}} : (ui64,!F,!F)->!F', maximum=0), roles=('P',)))
        refuse(source, 'protocol-application')


for label, old, new, diagnostic, invariant in [
    ('missing-maximum', ',maximum=4:i64', '', 'structured-source-original', "'protocol.repeat' op requires attribute 'maximum'"),
    ('missing-scope', ',carried_roles=[["P"]]', '', 'structured-source-original', "'protocol.repeat' op requires attribute 'carried_roles'"),
    ('callback-extra-argument', '%capture:!F', '%capture:!F,%extra:!F', 'mathematical-formation', None),
    ('callback-condition', '"protocol.yield"(%s) : (!F)', '"local.condition"(%s) : (!F)', 'structured-source-original', "'local.condition' op expects parent op 'local.for'"),
    ('callback-stop', '"protocol.yield"(%s) : (!F)->()', '"local.stop"() {reason="abort",site="stopped"} : ()->()', 'mathematical-formation', 'repeat must yield its carried interface'),
    ('disjoint-capture', '["P"], ["P"], ["P"]', '["P"], ["P"], ["Q"]', 'mathematical-formation', None),
]:
    with case(label + '-zero-maximum'):
        assert old in identity
        refuse(identity.replace(old, new).replace('maximum=4', 'maximum=0'), diagnostic, invariant=invariant)

source = identity.replace('maximum=4', 'maximum=0')
begin = source.index(' ({', source.index('"protocol.repeat"'))
end = source.index('}) {site="loop"', begin) + 2
second = ',{ ^other(%j:ui64,%t:!F,%d:!F): "protocol.yield"(%t) : (!F)->() }'
extra = '^extra(%j:ui64,%t:!F,%d:!F): "protocol.yield"(%t) : (!F)->()'
for label, malformed, invariant in [
    ('zero-region', source[:begin] + source[end:], "'protocol.repeat' op requires one region"),
    ('two-regions', source[:end-1] + second + source[end-1:], "'protocol.repeat' op requires one region"),
    ('multiblock', source[:end-2] + extra + source[end-2:], "'protocol.repeat' op expects region #0 to have 0 or 1 blocks"),
]:
    with case(label + '-callback-refused-at-zero-maximum'):
        refuse(malformed, 'structured-source-original', invariant=invariant)

with case('yield-cannot-widen-carried-role-scope'):
    body = repeat('%v = "protocol.restrict_roles"(%s) {roles=["Q"]} : (!F)->!F', yielded='%v')
    source = module(protocol('main', body))
    refuse(source)

with case('nested-repeat-roster-cannot-widen-even-for-constant-count'):
    body = '''%n0 = "data.index"() {value="0"} : ()->ui64
      "protocol.repeat"(%n0) ({ ^inner(%j:ui64): "protocol.yield"() : ()->() })
      {site="inner",carried=0:i64,maximum=0:i64,roles=["P","Q"],carried_roles=[]} : (ui64)->()'''
    refuse(module(protocol('main', repeat(body, maximum=0))))

with case('native-multirole-finite-math-profile-reaches-repeat-body'):
    original = (root / 'compiler/test/fixtures/finite/total-state.mlir').read_text()
    start = original.index('"protocol.func"')
    definitions = original[:start]
    tail = original[original.rindex('}) {profile='):]
    body = '''%r:2 = "protocol.repeat"(%n,%a,%b,%xs) ({
      ^body(%i:ui64,%x:!algebra.field<"bls12-381.fr">,%y:!algebra.field<"bls12-381.fr">,%captured:!algebra.field_vector<"bls12-381.fr">):
      %v:2 = "algebra.finite_fold"(%captured,%x,%y) {domain=@items,step=@step} : (!algebra.field_vector<"bls12-381.fr">,!algebra.field<"bls12-381.fr">,!algebra.field<"bls12-381.fr">)->(!algebra.field<"bls12-381.fr">,!algebra.field<"bls12-381.fr">)
      "protocol.yield"(%v#0,%v#1) : (!algebra.field<"bls12-381.fr">,!algebra.field<"bls12-381.fr">)->()
    }) {site="loop",carried=2:i64,maximum=0:i64,roles=["P"],carried_roles=[["P"],["P"]]} : (ui64,!algebra.field<"bls12-381.fr">,!algebra.field<"bls12-381.fr">,!algebra.field_vector<"bls12-381.fr">)->(!algebra.field<"bls12-381.fr">,!algebra.field<"bls12-381.fr">)'''
    ports = (('n', 'ui64', ('P',)), ('a', '!algebra.field<"bls12-381.fr">', ('P',)),
             ('b', '!algebra.field<"bls12-381.fr">', ('P',)), ('xs', '!algebra.field_vector<"bls12-381.fr">', ('P',)))
    source = definitions + protocol('main', body, inputs=ports, outputs=(), returns=()) + tail
    commands.verified(source)
    refuse(source, 'structured-source-multirole-math', 'structured-reference-unsupported')


with case('zero-state-application-effects-repeat-with-static-label'):
    child = protocol('child', '"protocol.query"(%coins) {owner="P",method="draw",site="q"} : (!S)->!F',
                     roles=('P',), inputs=(('coins', '!S', ('P',)),), outputs=(), returns=())
    body = '''"protocol.repeat"(%n,%coins) ({ ^body(%i:ui64,%capture:!S):
      "protocol.apply"(%capture) {callee=@child,roles=["P"],site="A"} : (!S)->()
      "protocol.yield"() : ()->()
    }) {site="loop",carried=0:i64,maximum=2:i64,roles=["P"],carried_roles=[]} : (ui64,!S)->()'''
    source = module(child, protocol('main', body, roles=('P',),
        inputs=(('n', 'ui64', ('P',)), ('coins', '!S', ('P',))), outputs=(), returns=()))
    export(source)
    replies = [reply(['draw', 'apply_1_A_q', 'P', service, '11', 'bls12-381.fr'], value) for value in ('2', '5')]
    assert run(source, ['2', '11'], replies=replies) == returned([], replies)
    stop = reply(replies[1][1], stop='exhausted')
    assert run(source, ['2', '11'], replies=[replies[0], stop]) == stopped('exhausted', 'apply_1_A_q', [replies[0], stop])

with case('induction-advances-and-original-count-capture-remains-fixed'):
    body = '''%r:2 = "protocol.repeat"(%n,%n,%n,%n) ({ ^body(%i:ui64,%last:ui64,%old:ui64,%count:ui64):
      "protocol.yield"(%i,%count) : (ui64,ui64)->()
    }) {site="loop",carried=2:i64,maximum=4:i64,roles=["P"],carried_roles=[["P"],["P"]]} : (ui64,ui64,ui64,ui64)->(ui64,ui64)'''
    source = module(protocol('main', body, roles=('P',), inputs=(('n', 'ui64', ('P',)),),
        outputs=(('ui64', ('P',)), ('ui64', ('P',))), returns=('%r#0', '%r#1')))
    export(source)
    for n in (0, 1, 2, 4):
        assert run(source, [str(n)]) == returned([str(max(0,n-1)), str(n)])

with case('dormant-supported-repeat-is-admitted-with-repeat-free-selected-root'):
    body = '''%n = "data.index"() {value="0"} : ()->ui64
      "protocol.repeat"(%n) ({ ^round(%i:ui64): "protocol.yield"() : ()->()
      }) {site="loop",roles=["P","Q"],carried=0:i64,maximum=3:i64,carried_roles=[]} : (ui64)->()'''
    source = module(protocol('main', inputs=(), outputs=(), returns=()),
                    protocol('dormant', body, inputs=(), outputs=(), returns=()))
    export(source)
    assert run(source, []) == returned([])

with case('same-labelled-component-at-two-repeat-sites'):
    source, symbol, snapshot = frontend(root / 'compiler/test/fixtures/structured-source/repeated-draw.zkc')
    definitions = {row[1]: row for row in snapshot[7] if row[0] == 'function'}
    owner = definitions[symbol]
    loop, = [i for i in owner[9][1] if i[0][0] == 'protocol_repeat']
    calls = [i for i in loop[3][0][2][1] if i[0][0] == 'protocol_apply']
    assert len(calls) == 2 and calls[0][0][1] == calls[1][0][1]
    assert calls[0][4] != calls[1][4]
    component = definitions[calls[0][0][1]]
    assert component[8] == ['sample::Draw', []]
    draw, = [i for i in component[9][1] if i[0][0] == 'draw']
    assert draw[4].startswith('label_')
    role = owner[6][1][0]
    actions = [['draw', qualified(call[4], draw[4]),
                role, service, '0', 'bls12-381.fr'] for call in calls]
    assert actions[0] != actions[1]
    replies = [reply(action, str(value)) for action, value in
               zip(actions * 2, [1, 2, 3, 4])]
    assert run(source, ['2', '0'], role, replies, symbol) == returned(['10'], replies)
    assert run(source, ['0', '0'], role, replies, symbol) == returned(['0'])
    stop = reply(actions[1], stop='abort')
    assert run(source, ['2', '0'], role, [replies[0], stop, *replies[2:]], symbol) == stopped(
        'abort', actions[1][1], [replies[0], stop])
    native(source, 'same-labelled-component')

commands.save()
print(f'{counted()} structured repeat cases; evidence: {commands.directory}')
