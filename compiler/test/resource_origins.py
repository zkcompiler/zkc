"""Exact affine roots through scoped control, source calls and protocol repeats."""
import json
from functools import cache

from cases import case, counted
from commands import Commands
from tools import records, resource_origin_sources

OUT = records()
commands = Commands(OUT)


@cache
def source(name, outside=False):
    """Author native scoped source directly, independently of frontend syntax."""
    text = commands.run([resource_origin_sources, name,
                         *(['--outside'] if outside else [])])
    (OUT / (name + ('-outside' if outside else '') + '.mlir')).write_text(text)
    return text


def accept(name, outside=False):
    return commands.source('protocol-bundle', source(name, outside))


def refuse_root(name, outside=False):
    commands.source('protocol-bundle', source(name, outside),
                    refuses='mathematical-formation')
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
        if name == 'swap-inside':
            refuse_root('swap')
        elif name == 'swap-outside':
            accept('swap', outside=True)
        elif name == 'role-stop-direct':
            refuse_root('role-stop')
        elif name == 'role-stop-apply':
            refuse_root('role-apply-stop')
        else:
            accept(name)
            if name in ['if', 'for', 'match']:
                accept(name, outside=True)

with case('scoped stop joins the continuing identity arm'):
    accept('if-stop')
    commands.source('protocol-bundle', source('if-terminal'),
                    refuses='execution-cfg')
    assert 'stopped arms cannot produce data' in commands.last.stderr

with case('stop through an ordinary call prunes only its local arm'):
    accept('stop-call')
    refuse_root('continuing-call')

with case('stopping loop body retains the zero-trip root'):
    accept('for-stop')

with case('match stop joins the continuing capture'):
    accept('match-stop')

with case('ordinary scoped application uses the resolved callee'):
    accept('apply')
    # Standard Func owns unresolved ordinary-call symbol diagnostics.
    commands.source('protocol-bundle', source('missing'),
                    refuses="'missing' does not reference a valid function")

with case('different actual resources share only formal-relative summaries'):
    accept('formal')
    refuse_root('formal-swap')

with case('sequential calls consume work without consuming nesting depth'):
    accept('calls80')
    accept('protocol-calls80')

with case('generated resource transitions in all lowering modes'):
    for name in ['execution', 'stop', 'nested_stop']:
        for suffix, options in [('', ()), ('_plain', ('--no-simplify',)),
                                ('_release', ('--release-storage',))]:
            bundle = commands.source('protocol-bundle', source(name), *options)
            if name == 'execution':
                emitted = set(tags(json.loads(json.loads(bundle)['candidate'])))
                assert {'if', 'match', 'for', 'loop'} <= emitted, emitted
                if suffix == '_release':
                    assert 'release' in emitted, emitted
            (OUT / (name + suffix + '.bundle')).write_text(bundle)

with case('fresh roots remain unknown; standalone replacement is legal'):
    refuse_root('fresh')
    accept('fresh', outside=True)
    accept('unknown-slot')
    refuse_root('unknown-wrong')
    for name in ['fresh-branch', 'fresh-stop-branch']:
        refuse_root(name)
        accept(name, outside=True)

with case('match payload roots are not inferred from aggregate construction'):
    accept('box', outside=True)
    refuse_root('box')

with case('private match still refuses hidden history through a call'):
    commands.source('protocol-bundle', source('private-history'),
                    refuses='execution-match-history')

with case('successor chains are work, not nesting'):
    accept('draw80')
    commands.source('protocol-bundle', source('draw-reuse'),
                    refuses='execution-resource-reuse')

with case('protocol endpoint invocation cannot appear inside a scoped helper'):
    commands.source('protocol-bundle', source('endpoint-call'),
                    refuses="'protocol.local_call' op expects parent op")

with case('one role stopping does not erase another role identity'):
    for name in ['role-identity', 'role-apply-identity',
                 'role-apply-identity-reverse']:
        accept(name)
    refuse_root('role-apply-stop-reverse')

with case('a locally terminal branch cannot manufacture a returned root'):
    refuse_root('terminal-then-return')
    accept('terminal-then-return', outside=True)

with case('callee repeat invariant is checked in both declaration orders'):
    for suffix in ['', '-reverse']:
        refuse_root('callee-repeat' + suffix)
        accept('callee-repeat-good' + suffix)

with case('cyclic scoped applications keep their formation diagnostic'):
    commands.source('protocol-bundle', source('cycle'),
                    refuses='execution-call-cycle')

with case('acyclic application expansion retains its own limit'):
    commands.source('protocol-bundle', source('dag'),
                    refuses='algorithm-expansion-limit')

commands.save()
counted()
