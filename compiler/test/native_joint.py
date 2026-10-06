"""Native bundles: source-order schedules and fresh inputs for joint execution."""
import json
from pathlib import Path

from cases import case, counted
from commands import Commands
from tools import records

OUT = records()
commands = Commands(OUT)
FIXTURES = Path(__file__).parent / 'fixtures/mathematical'


def compile_bundle(name, text, expected, *options):
    output = commands.source('protocol-bundle', text, *options)
    bundle = json.loads(output)
    (OUT / f'{name}.bundle').write_text(output)
    (OUT / f'{name}.mlir').write_text(text)
    assert bundle['format'] == 'zkc.run/1'
    candidate = json.loads(bundle['candidate'])
    assert candidate[0] == 'zkc.program/1'
    programs = {p[3]: p[7] for p in candidate[4]}
    authored_local = {(r, s) for r, k, s, _ in expected if k == 'local'}
    actual = []
    for step in bundle['steps']:
        role = bundle['roles'][step['role']]
        instruction = programs[role][step['instruction']]
        # Exclude demand calculations by exact independently listed source sites,
        # never by a generated-looking symbol prefix.
        if instruction[0] in ('query', 'send', 'receive') or (
                instruction[0] == 'local' and (role, instruction[1]) in authored_local):
            actual.append((role, instruction[0], instruction[1], step['anchor']))
    assert actual == expected, (name, actual, expected)
    for role in bundle['roles']:
        indices = [s['instruction'] for s in bundle['steps'] if bundle['roles'][s['role']] == role]
        assert indices == list(range(len(programs[role])))
    return bundle


schnorr = (FIXTURES / 'schnorr-services.mlir').read_text()
foreign = (FIXTURES / 'foreign-guard.mlir').read_text()
services = (FIXTURES / 'services.mlir').read_text()
inverse = (FIXTURES / 'mixed-inverse.mlir').read_text()
# Expected action lists are authored directly from the protocols. Demand
# calculations are checked separately below, including deliberate name collisions.
expected_schnorr = [('Alice', 'query', 'nonce', 0), ('Alice', 'send', 'commitment', 1),
                    ('Bob', 'receive', 'commitment', 1), ('Bob', 'query', 'draw_challenge', 2),
                    ('Bob', 'send', 'challenge', 3), ('Alice', 'receive', 'challenge', 3),
                    ('Alice', 'send', 'response', 4), ('Bob', 'receive', 'response', 4)]
expected_foreign = [('Alice', 'query', 'first_draw', 0), ('Bob', 'local', 'foreign_guard', 1),
                    ('Alice', 'query', 'second_draw', 2), ('Alice', 'send', 'result', 3),
                    ('Bob', 'receive', 'result', 3)]
expected_services = [('Alice', 'local', 'before_query', 0), ('Alice', 'query', 'first_draw', 1),
                     ('Alice', 'query', 'second_draw', 2), ('Alice', 'query', 'unused_draw', 3),
                     ('Alice', 'send', 'result', 4), ('Bob', 'receive', 'result', 4)]
expected_inverse = [('P', 'send', 'send', 0), ('V', 'receive', 'send', 0),
                    ('V', 'send', 'reply', 1), ('P', 'receive', 'reply', 1),
                    ('P', 'local', 'after_receive', 2), ('P', 'local', 'inverse', 3)]
for name, text, expected in [('schnorr', schnorr, expected_schnorr), ('foreign', foreign, expected_foreign),
                             ('services', services, expected_services), ('inverse', inverse, expected_inverse)]:
    for suffix, flags in [('', ()), ('_plain', ('--no-simplify',)), ('_release', ('--release-storage',)),
                          ('_plain_release', ('--no-simplify', '--release-storage'))]:
        with case(f'{name}{suffix} source order'):
            compile_bundle(name + suffix, text, expected, *flags)

with case('deferred false permits later query'):
    deferred = '\n'.join(line for line in foreign.splitlines() if 'protocol.guard' not in line)
    expected = [(r, k, s, a - (a > 1)) for r, k, s, a in expected_foreign if s != 'foreign_guard']
    compile_bundle('deferred', deferred, expected)

with case('authored generated-looking callee and site are not a demand prefix'):
    collision = inverse.replace('@inverse', '@_calculation_0').replace('site="inverse"', 'site="calculation_0"')
    expected = [(r, k, 'calculation_0' if s == 'inverse' else s, a) for r, k, s, a in expected_inverse]
    compile_bundle('collision', collision, expected)

single = '''module { "protocol.module"() ({
  "protocol.func"() ({
  ^entry(%value: i1):
    "protocol.return"(%value) : (i1) -> ()
  }) {sym_name="main", function_type=(i1) -> i1, roles=["Solo"],
      input_roles=[["Solo"]], output_roles=[["Solo"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () }'''
with case('single role no messages'):
    bundle = compile_bundle('single', single, [])
    assert bundle['steps'] == [{'role': 0, 'instruction': 0, 'anchor': None}]
with case('single role zero inputs and outputs'):
    empty = single.replace('^entry(%value: i1):', '^entry:').replace('"protocol.return"(%value) : (i1)', '"protocol.return"() : ()')
    empty = empty.replace('function_type=(i1) -> i1', 'function_type=() -> ()').replace('input_roles=[["Solo"]], output_roles=[["Solo"]]', 'input_roles=[], output_roles=[]')
    compile_bundle('empty', empty, [])
with case('roster and selected entry survive renaming'):
    renamed = foreign.replace('Alice', 'Zulu').replace('Bob', 'Alpha').replace('sym_name="main"', 'sym_name="selected"')
    expected = [(dict(Alice='Zulu', Bob='Alpha').get(r, r), k, s, a) for r, k, s, a in expected_foreign]
    bundle = compile_bundle('renamed', renamed, expected, '--entry=selected')
    assert bundle['roles'] == ['Zulu', 'Alpha', 'Observer']
with case('reject physical input and invalid invocation without partial output'):
    physical = commands.verified(single, None, '--zkc-project-protocol', '--zkc-lower-math', '--zkc-select-physical')
    commands.source('protocol-bundle', physical, refuses='run-source-profile')
    commands.source('protocol-bundle', single, '--entry=missing', refuses='run-entry')
    commands.source('protocol-bundle', single, '--entry=main', '--entry=main', refuses='run-duplicate-option')
    commands.source('protocol-bundle', single, '--no-simplify=yes', refuses='run-option')
    commands.source('protocol-bundle', 'module {', refuses='error')

counted()
