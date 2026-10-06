"""Profiles and executable feature selectors are independently checked."""
import json
from commands import Commands
from tools import records

commands = Commands(records())

def module(profile, contract=None):
    attrs = f'profile = #protocol.profile<{profile}>'
    if contract:
        attrs += f', execution_contract = #protocol.execution_contract<{contract}>'
    body = '^entry:'
    if profile in ('exec', 'physical'):
        body += '\n"protocol.participant"() <{sym_name="p", function_type=() -> (), instance="example", role="P", parameters=[]}> ({"protocol.finish"() : () -> ()}) : () -> ()'
        body += '\n"protocol.entry"() <{sym_name="main", targets=[["P", @p]]}> : () -> ()'
    return f'module {{ "protocol.module"() <{{{attrs}}}> ({{{body}}}) : () -> () }}'

# Empty symbol-table blocks are explicitly present in generic assembly.
common = module('protocol_exec').replace('({})', '({^entry:})')
normalized = commands.verified(common)
assert 'stage' not in normalized
assert 'protocol_exec' in normalized
for profile in ('exec', 'physical'):
    source = module(profile, 'legacy_participants_v1').replace('({})', '({^entry:})')
    normalized = commands.verified(source)
    carrier = json.loads(commands.source('protocol-export', normalized))
    assert carrier[0] == 'zkc.participants/1'
    imported = commands.source('protocol-import', json.dumps(carrier))
    assert f'#protocol.profile<{profile}>' in imported
    assert '#protocol.execution_contract<legacy_participants_v1>' in imported

for profile in ('protocol_exec', 'protocol', 'participant'):
    for contract in ('legacy_participants_v1', 'program'):
        commands.verified(module(profile, contract), 'protocol-execution-contract')
for profile in ('exec', 'physical'):
    commands.verified(module(profile), 'protocol-execution-contract')
commands.verified('module { "protocol.module"() ({}) {profile=#protocol.profile<participant>} : () -> () }', 'must have exactly one block')
commands.verified(module('participant'), 'mathematical-projection')
commands.verified(module('unknown'), 'to be one of')
commands.verified(module('protocol_exec', 'unknown'), 'to be one of')
commands.verified(common.replace('profile = #protocol.profile<protocol_exec>', 'stage = "common"'),
                  'mlir-unknown-property')
# Changing a profile alone never reinterprets a program. This protocol_exec
# module lacks the declarations required by protocol admission.
commands.verified(common.replace('protocol_exec', 'protocol'), 'mathematical-module')
native = commands.verified(module('exec', 'program'))
commands.source('protocol-export', native, refuses='native-physical-required')
native = commands.verified(native, None, '--zkc-select-physical')
carrier = json.loads(commands.source('protocol-export', native))
assert carrier[0] == 'zkc.program/1'
assert len(carrier[4][0]) == 9
commands.verified(commands.source('protocol-import', json.dumps(carrier)))
for retired in ('zkc.service-participants/1', 'zkc.native-participants/1', 'zkc.native-participants/2',
                'zkc.native-participants/3', 'zkc.program/99'):
    mutant = list(carrier)
    mutant[0] = retired
    commands.source('protocol-import', json.dumps(mutant), refuses='interactive-format')
for retired in ('service_participants_v1', 'native_participants_v1', 'native_participants_v2', 'native_participants_v3'):
    commands.verified(module('physical', retired), 'to be one of')
carrier[2] = 'logical'
commands.source('protocol-import', json.dumps(carrier), refuses='native-physical-required')
print(f'protocol profile checks: {commands.save()}')

for terminal in ['"protocol.incomplete"() {site="end"} : () -> ()', '"local.stop"() {site="end", reason="reject"} : () -> ()']:
    candidate = module('physical', 'program').replace('"protocol.finish"() : () -> ()', terminal)
    commands.verified(candidate, 'native-participant-terminal')
