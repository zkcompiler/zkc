"""The four profiles select formation and export; unknown properties refuse."""
import json
from commands import Commands
from tools import records, canonical_program

commands = Commands(records())


def module(profile):
    attrs = f'profile = #protocol.profile<{profile}>'
    if profile in ('protocol', 'participant'):
        mathematical = 'module { "protocol.module"() <{profile=#protocol.profile<protocol>}> ({"protocol.func"() <{sym_name="main", function_type=() -> (), roles=["P"], input_roles=[], output_roles=[]}> ({"protocol.return"() : () -> ()}) : () -> ()}) : () -> () }'
        return commands.verified(mathematical, None, '--zkc-project-protocol') if profile == 'participant' else mathematical
    body = '^entry:'
    if profile in ('exec', 'physical'):
        body += '\n"protocol.participant"() <{sym_name="p", function_type=() -> (), instance="example", role="P"}> ({"protocol.finish"() : () -> ()}) : () -> ()'
        body += '\n"protocol.entry"() <{sym_name="main", targets=[["P", @p]]}> : () -> ()'
    return f'module {{ "protocol.module"() <{{{attrs}}}> ({{{body}}}) : () -> () }}'


for profile in ('protocol', 'participant', 'exec', 'physical'):
    commands.verified(module(profile))
    malformed = module(profile).replace(f'#protocol.profile<{profile}>', f'#protocol.profile<{profile}>, unexpected=true')
    commands.verified(malformed, 'mlir-unknown-property')
for profile in ('exec', 'physical'):
    for value in ('[]', '["n"]'):
        malformed = module(profile).replace('role="P"', f'role="P", unexpected={value}')
        commands.verified(malformed, 'mlir-unknown-property')
commands.verified(module('invalid'), 'to be one of')
native = commands.verified(module('exec'))
commands.source('protocol-export', native, refuses='native-physical-required')
native = commands.verified(native, None, '--zkc-select-physical')
carrier = json.loads(commands.source('protocol-export', native))
assert carrier[0] == 'zkc.program/0'
assert len(carrier) == 5 and len(carrier[3][0]) == 8
assert json.loads(canonical_program(commands, json.dumps(carrier))) == carrier
mutant = list(carrier)
mutant[0] = 'invalid.program'
canonical_program(commands, json.dumps(mutant), refuses='interactive-format')
mutant = list(carrier)
mutant.insert(2, [])
canonical_program(commands, json.dumps(mutant), refuses='interactive-shape')
commands.verified(module('physical').replace('"protocol.finish"', '"protocol.incomplete"'), 'unregistered operation')
commands.verified(module('physical').replace('"protocol.finish"() : () -> ()', '"local.stop"() {site="end", reason="reject"} : () -> ()'), 'interactive-callable-terminator')
commands.source('invalid-command', '', refuses='unknown-command')
print(f'protocol profile checks: {commands.save()}')
