"""Exact affine origins across structured control and static applications."""
import json
from pathlib import Path
from cases import case, counted
from commands import Commands
from affine_sources import source, unit_source, outside
from tools import records

OUT = records()
commands = Commands(OUT)
FIXTURES = Path(__file__).parent / 'fixtures/resource-origins'


def edit(text, old, new):
    assert text.count(old) == 1, f'expected exactly one fixture edit: {old}'
    return text.replace(old, new)


def refuse_root(text):
    commands.source('protocol-bundle', text, refuses='mathematical-formation')
    assert 'exact carried resource root' in commands.last.stderr


def tags(tree):
    if isinstance(tree, list):
        if tree and isinstance(tree[0], str):
            yield tree[0]
        for child in tree:
            yield from tags(child)


for name in ['if', 'for', 'match', 'apply', 'swap-inside', 'swap-outside',
             'role-stop-direct', 'role-stop-apply']:
    with case(name):
        text = (FIXTURES / (name + '.mlir')).read_text()
        refusal = 'mathematical-formation' if name in [
            'swap-inside', 'role-stop-direct', 'role-stop-apply'] else None
        if refusal:
            refuse_root(text)
        else:
            commands.source('protocol-bundle', text)
        if name in ['if', 'for', 'match']:
            commands.source('protocol-bundle', outside(text))

with case('local stop joins the continuing identity arm'):
    text = edit((FIXTURES / 'if.mlir').read_text(),
        '"local.yield"(%a) : (!s)->()',
        '"local.stop"() {site="abort",reason="abort"} : ()->()')
    commands.source('protocol-bundle', text)
    # Both terminal arms with outputs are invalid under ordinary formation.
    commands.source('protocol-bundle', text.replace(
        '"local.yield"(%b) : (!s)->()',
        '"local.stop"() {site="abort_other",reason="abort"} : ()->()'),
        refuses='local-terminal-outputs')

with case('stop through a call prunes only its local arm'):
    text = unit_source('''%out = "local.if"(%go,%s) ({ ^yes(%a:!s):
      local.apply @never() {site="never"} : ()->()
      %new = "local.exec.resource_unit_create"() {binding=@create,parameters=[],site="new"} : ()->!s
      "local.yield"(%new) : (!s)->()
    }, { ^no(%b:!s):
      "local.yield"(%b) : (!s)->()
    }) {site="choice"} : (i1,!s)->!s
    local.return %out : !s''')
    text = edit(text, ' local.func @step', '''local.func @never() attributes {logical_origin=["never",[]]} {
      "local.stop"() {site="abort",reason="abort"} : ()->()
    }
    local.func @step''')
    commands.source('protocol-bundle', text)
    # Without the stopping call, the replacing arm continues and must be refused.
    refuse_root(edit(text, 'local.apply @never() {site="never"} : ()->()\n', ''))

with case('stopping loop body retains the zero-trip root'):
    text = edit((FIXTURES / 'for.mlir').read_text(),
        '"local.yield"(%a) : (!s)->()',
        '"local.stop"() {site="abort",reason="abort"} : ()->()')
    commands.source('protocol-bundle', text)

with case('match stop joins the continuing capture'):
    text = edit((FIXTURES / 'match.mlir').read_text(),
        '"local.yield"(%a) : (!s)->()',
        '"local.stop"() {site="abort",reason="abort"} : ()->()')
    commands.source('protocol-bundle', text)

with case('local application uses the resolved callee'):
    text = source('%out = local.apply @identity(%s) {site="call"} : (!s)->!s\n local.return %out : !s')
    text = text.replace(' local.func @step', '''local.func @identity(%x:!s)->!s attributes {logical_origin=["identity",[]]} {
      local.return %x : !s
    }
    local.func @step''')
    commands.source('protocol-bundle', text)
    commands.source('protocol-bundle', text.replace('@identity(%s)', '@missing(%s)'), refuses='interactive-symbol-kind')

with case('different actual resources share only formal-relative summaries'):
    text = (FIXTURES / 'swap-inside.mlir').read_text()
    begin = text.index('  %next:2 = "local.for"')
    end = text.index('  local.return', begin)
    text = text[:begin] + '''  %left = local.apply @identity(%a) {site="left"} : (!s)->!s
  %right = local.apply @identity(%b) {site="right"} : (!s)->!s
''' + text[end:]
    text = text.replace('%next#0,%next#1 : !s,!s', '%left,%right : !s,!s')
    text = text.replace(' local.func @swap', '''local.func @identity(%x:!s)->!s attributes {logical_origin=["identity",[]]} {
       local.return %x : !s
    }
    local.func @swap''')
    commands.source('protocol-bundle', text)
    refuse_root(text.replace('local.return %left,%right', 'local.return %right,%left'))

with case('sequential calls consume work without consuming nesting depth'):
    body = []
    previous = '%s'
    for i in range(80):
        body.append(f'%v{i} = local.apply @identity({previous}) {{site="call{i}"}} : (!s)->!s')
        previous = f'%v{i}'
    text = source('\n'.join(body) + f'\nlocal.return {previous} : !s')
    text = text.replace(' local.func @step', '''local.func @identity(%x:!s)->!s attributes {logical_origin=["identity",[]]} {
       local.return %x : !s
    }
    local.func @step''')
    commands.source('protocol-bundle', text)
    start = text.index('    %next = "protocol.local_call"')
    end = text.index('    "protocol.yield"', start)
    calls=[]
    previous='%state'
    for i in range(80):
        calls.append(f'%v{i} = "protocol.local_call"({previous}) {{callee=@identity,role="P",site="call{i}"}} : (!s)->!s')
        previous=f'%v{i}'
    text = text[:start] + '\n'.join(calls) + '\n' + text[end:]
    commands.source('protocol-bundle', text.replace('"protocol.yield"(%next)', f'"protocol.yield"({previous})'))

with case('generated resource transitions in all lowering modes'):
    text = (FIXTURES / 'execution.mlir').read_text()
    stop = edit(text,'%once:2 = local.apply @draw(%a,%b,%g) {site="once"} : (!r,!t,i1)->(!r,!t)\n   "local.yield"(%once#0,%once#1) : (!r,!t)->()',
                        '"local.stop"() {site="abort",reason="abort"} : ()->()')
    nested_stop = edit(text,
        '"local.yield"(%out#0,%out#1,%flag) : (!r,!t,i1)->()',
        '"local.stop"() {site="after_draw",reason="abort"} : ()->()')
    for name, authored in [('execution', text), ('stop', stop), ('nested_stop', nested_stop)]:
        for suffix, options in [('', ()), ('_plain', ('--no-simplify',)), ('_release', ('--release-storage',))]:
            bundle = commands.source('protocol-bundle', authored, *options)
            if name == 'execution':
                emitted = set(tags(json.loads(json.loads(bundle)['candidate'])))
                assert {'if', 'match', 'for', 'loop'} <= emitted, emitted
                if suffix == '_release':
                    assert 'release' in emitted, emitted
            (OUT / (name + suffix + '.bundle')).write_text(bundle)
with case('fresh roots remain unknown; standalone replacement is legal'):
    fresh = '%new = "local.exec.resource_unit_create"() {binding=@create,parameters=[],site="new"} : ()->!s'
    text = unit_source(fresh+'\nlocal.return %new : !s')
    refuse_root(text)
    commands.source('protocol-bundle', outside(text))
    # One unknown carried slot does not erase another slot's identity invariant.
    text = unit_source(fresh+'''
     %loop:2 = "local.for"(%lo,%hi,%s,%new) ({ ^body(%i:ui64,%a:!s,%b:!s):
       %replacement = "local.exec.resource_unit_create"() {binding=@create,parameters=[],site="replace"} : ()->!s
       "local.yield"(%a,%replacement) : (!s,!s)->()
     }) {site="loop"} : (ui64,ui64,!s,!s)->(!s,!s)
     local.return %loop#0 : !s''')
    commands.source('protocol-bundle', text)
    refuse_root(text.replace('local.return %loop#0', 'local.return %loop#1'))
    # A replacing branch prevents a joint exact-root result.
    text = unit_source('''%out = "local.if"(%go,%s) ({ ^yes(%a:!s):
      "local.yield"(%a) : (!s)->()
    }, { ^no(%b:!s):
      '''+fresh+'''
      "local.yield"(%new) : (!s)->()
    }) {site="choice"} : (i1,!s)->!s
    local.return %out : !s''')
    refuse_root(text)
    commands.source('protocol-bundle', outside(text))
    # A stopping arm cannot turn the other arm's fresh root into an identity.
    text = edit(text, '"local.yield"(%a) : (!s)->()',
        '"local.stop"() {site="abort",reason="abort"} : ()->()')
    refuse_root(text)
    commands.source('protocol-bundle', outside(text))

with case('match payload roots are not inferred from aggregate construction'):
    from variant_codec import descriptor
    tag = descriptor('Box', [('box', ['rng:bls12-381.fr'])])
    text = source('''%box = "local.variant_inject"(%s) {alternative="box",site="box"} : (!s)->!box
      %out = "local.match"(%box) ({ ^arm(%payload:!s):
        "local.yield"(%payload) : (!s)->()
      }) {alternatives=["box"],site="match"} : (!box)->!s
      local.return %out : !s''').replace('module {', f'!box = !local.variant<"{tag}">\nmodule {{', 1)
    commands.source('protocol-bundle', outside(text))
    refuse_root(text)

with case('private match still refuses hidden history through a call'):
    text = edit((FIXTURES / 'execution.mlir').read_text(),
        '"local.yield"(%a,%b) : (!r,!t)->()',
        '%drawn:2 = local.apply @draw(%a,%b,%yes) {site="hidden"} : (!r,!t,i1)->(!r,!t)\n "local.yield"(%drawn#0,%drawn#1) : (!r,!t)->()')
    text = text.replace('"local.match"(%tag,%r,%t)', '"local.match"(%tag,%r,%t,%go)').replace('^left(%a:!r,%b:!t)', '^left(%a:!r,%b:!t,%yes:i1)').replace('^right(%c:!r,%d:!t)', '^right(%c:!r,%d:!t,%no:i1)').replace('(!tag,!r,!t)->', '(!tag,!r,!t,i1)->')
    commands.source('protocol-bundle', text, refuses='local-match-challenge')

with case('successor chains are work, not nesting'):
    draw = '%v{0}:2 = "crypto.exec.random_draw"({1}) {{binding=@draw,parameters=[],site="draw{0}"}} : (!s)->(!algebra.field<"bls12-381.fr">,!s)'
    body=[]
    previous='%s'
    for i in range(80):
        body.append(draw.format(i,previous))
        previous=f'%v{i}#1'
    text=source('\n'.join(body)+f'\nlocal.return {previous} : !s').replace(' local.func @step', '"local.binding"() {sym_name="draw",contract="random.draw",arguments=["bls12-381.fr"],implementation=""} : ()->()\n local.func @step')
    commands.source('protocol-bundle', text)
    commands.source('protocol-bundle', text.replace('local.return %v79#1', 'local.return %s'), refuses='interactive-resource-reuse')

with case('local.call retains endpoint-only placement'):
    text=source('local.call @identity(%s) {site="call"} : (!s)->!s\nlocal.return %s : !s')
    text=text.replace(' local.func @step', 'local.func @identity(%x:!s)->!s attributes {logical_origin=["identity",[]]} { local.return %x : !s }\n local.func @step')
    commands.source('protocol-bundle', text, refuses='interactive-role-attribute')

with case('one role stopping does not erase another role identity'):
    for name in ['role-stop-direct', 'role-stop-apply']:
        text = (FIXTURES / (name + '.mlir')).read_text().replace('local.return %b,%a', 'local.return %a,%b')
        commands.source('protocol-bundle', text)
        if name.endswith('apply'):
            begin = text.index(' "protocol.func"() ({ ^entry(%a:!s,%b:!s):')
            end = text.index(' "protocol.func"() ({ ^entry(%n:', begin)
            child = text[begin:end]
            reordered = text[:begin] + text[end:]
            end = reordered.index('}) {profile=')
            commands.source('protocol-bundle', reordered[:end]+child+reordered[end:])

with case('a locally terminal branch cannot manufacture a returned root'):
    text = source('''"local.if"(%go) ({
      "local.stop"() {site="left",reason="abort"} : ()->()
    }, {
      "local.stop"() {site="right",reason="abort"} : ()->()
    }) {site="both"} : (i1)->()
    local.return %s : !s''')
    refuse_root(text)
    commands.source('protocol-bundle', outside(text))

with case('callee repeat invariant is checked in both declaration orders'):
    text = (FIXTURES / 'swap-inside.mlir').read_text()
    begin = text.index(' "protocol.func"')
    end = text.index('}) {profile=')
    child = edit(text[begin:end], 'sym_name="main"', 'sym_name="child"')
    child = edit(child, 'site="outer"', 'site="child_rounds"')
    parent = edit(text[begin:end], '"protocol.local_call"(%x,%y,%l,%h) {callee=@swap,role="P",site="swap"} : (!s,!s,ui64,ui64)->(!s,!s)',
        '"protocol.apply"(%i,%x,%y,%l,%h) {callee=@child,roles=["P"],site="child"} : (ui64,!s,!s,ui64,ui64)->(!s,!s)')
    for definitions in [child+parent, parent+child]:
        authored = text[:begin]+definitions+text[end:]
        assert '"protocol.apply"' in authored
        refuse_root(authored)
        # Removing only the actual swap makes the complete composition legal.
        commands.source('protocol-bundle', authored.replace('"local.yield"(%y,%x)', '"local.yield"(%x,%y)'))

with case('cyclic local applications keep their formation diagnostic'):
    text = source('%out = local.apply @step(%s,%go,%lo,%hi) {site="again"} : (!s,i1,ui64,ui64)->!s\nlocal.return %out : !s')
    commands.source('protocol-bundle', text, refuses='interactive-call-cycle')

with case('acyclic application expansion retains its own limit'):
    definitions=[]
    for i in range(20):
        body='local.return %s : !s'
        if i:
            body=f'''%a = local.apply @f{i-1}(%s) {{site="a"}} : (!s)->!s
              %b = local.apply @f{i-1}(%a) {{site="b"}} : (!s)->!s
              local.return %b : !s'''
        definitions.append(f'local.func @f{i}(%s:!s)->!s attributes {{logical_origin=["f{i}",[]]}} {{ {body} }}')
    text=source('%out = local.apply @f19(%s) {site="dag"} : (!s)->!s\nlocal.return %out : !s').replace(' local.func @step', '\n'.join(definitions)+'\n local.func @step')
    commands.source('protocol-bundle', text, refuses='algorithm-expansion-limit')

counted()
