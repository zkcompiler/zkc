"""A Math selection that one role demands compiles through role projection.

Projection places the selection only at the role that consumes its result, and
the projected comparison reads it as a value where that role sends it.
"""
import json
from pathlib import Path

from cases import case
from commands import Commands
from tools import records

OUT = records()
commands = Commands(OUT)
FIXTURES = Path(__file__).parent / 'fixtures'
FIELD = '!algebra.field<"bls12-381.fr">'
GROUP = '!algebra.group<"bls12-381.g1">'
HELPER = f'''func.func private @choose(%c: i1, %a: {FIELD}, %b: {FIELD}) -> {FIELD} {{
  %r = "data.branch"(%c, %a, %b) ({{
  ^then(%x: {FIELD}, %y: {FIELD}):
    "data.yield"(%x) : ({FIELD}) -> ()
  }}, {{
  ^else(%x: {FIELD}, %y: {FIELD}):
    "data.yield"(%y) : ({FIELD}) -> ()
  }}) {{alternatives=["then","else"]}} : (i1, {FIELD}, {FIELD}) -> {FIELD}
  return %r : {FIELD}
}}
'''
RESPONSE = f'%z = algebra.field_add %k, %cx : ({FIELD}, {FIELD}) -> {FIELD}'
SELECTED = (f'%t = algebra.group_equal %g, %y : ({GROUP}, {GROUP}) -> i1\n'
            f'%z = func.call @choose(%t, %k, %cx) : (i1, {FIELD}, {FIELD}) -> {FIELD}')
OPTIONS = [(), ('--no-simplify',), ('--release-storage',)]


def selecting(bundle):
    """Whether each role executes a selection, directly or in a local call."""
    document = json.loads(bundle)
    assert document['format'] == 'zkc.run/0'
    program = json.loads(document['candidate'])
    calls = [json.dumps(function[1]) for function in program[2]
             if '"if"' in json.dumps(function)]
    return {function[3]: any(text in json.dumps(function) for text in ['"if"', *calls])
            for function in program[3] if function[0] == 'participant'}


with case('a Math selection only the prover demands compiles to a bundle'):
    schnorr = (FIXTURES / 'mathematical/schnorr-services.mlir').read_text()
    assert schnorr.count('relation.declare') == 1 and schnorr.count(RESPONSE) == 1
    text = schnorr.replace('relation.declare', HELPER + 'relation.declare').replace(
        RESPONSE, SELECTED)
    for options in OPTIONS:
        bundle = commands.source('protocol-bundle', text, *options)
        assert selecting(bundle) == {'Alice': True, 'Bob': False}

with case('a source helper selection that one role sends compiles to a bundle'):
    flags = ['--source-format=zkc-layout', '--subject=selected::Run',
             f'--module=selected={FIXTURES / "selected-control/math-one-role.zkc"}']
    original = commands.source('language-emit', None, *flags)
    interface = json.loads(commands.source('language-interface', None, *flags))
    for options in OPTIONS:
        bundle = commands.source('protocol-bundle', original,
                                 f'--entry={interface["protocol"]}', *options)
        # The sender alone selects; the receiver only receives the value.
        roles = selecting(bundle)
        assert sorted(roles.values()) == [False, True]
        sender = next(role for role, selects in roles.items() if selects)
        program = json.loads(json.loads(bundle)['candidate'])
        assert all(('"send"' in json.dumps(function)) == (function[3] == sender)
                   for function in program[3] if function[0] == 'participant')
