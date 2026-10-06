"""Executable calls retain effects and cannot be confused with pure helpers."""

from commands import Commands
from tools import records

commands = Commands(records())
source = '''module {
  local.func private @leaf(%arg: i1) -> i1 { return %arg : i1 }
  local.func @algorithm(%arg: i1) -> i1 {
    %result = apply @leaf(%arg) {site = "apply"} : (i1) -> i1
    return %result : i1
  }
  "protocol.participant"() <{sym_name = "participant", function_type = (i1) -> i1,
    instance = "example", role = "P", parameters = []}> ({
  ^entry(%arg: i1):
    %first = local.call @leaf(%arg) {site = "first"} : (i1) -> i1
    %second = local.call @leaf(%arg) {site = "second"} : (i1) -> i1
    "protocol.finish"(%arg) : (i1) -> ()
  }) : () -> ()
}'''

normalized = commands.verified(source)
assert commands.verified(normalized) == normalized
optimized = commands.verified(source, None, '--canonicalize', '--cse', '--inline')
assert optimized.count('local.call @leaf') == 2
assert 'apply @leaf' in optimized
assert 'local.func private @leaf' in optimized

# A pure call may not accidentally reach an executable function through the
# shared FunctionOpInterface; the reverse direction also checks the exact kind.
commands.verified(source.replace('apply @leaf', 'func.call @leaf'),
                  "does not reference a valid function")
pure = 'func.func private @pure(%a: i1) -> i1 { return %a : i1 }'
commands.verified(source.replace('module {', 'module {\n' + pure, 1)
                  .replace('apply @leaf', 'apply @pure'),
                  'interactive-symbol-kind')
commands.verified(source.replace('apply @leaf(%arg)', 'apply @leaf()')
                  .replace('{site = "apply"} : (i1) -> i1',
                           '{site = "apply"} : () -> i1'),
                  'interactive-call-signature')
commands.verified('module { local.func @bad(%a: i1) -> i32 { return %a : i1 } }',
                  'interactive-return-signature')

# The structural function op permits declarations needed by protocol_exec.
# Executability and closed native-profile admission are separate checks.
commands.verified('module { local.func private @external(i1) -> i1 }')
commands.verified(source.replace('local.func private @leaf(%arg: i1) -> i1 { return %arg : i1 }',
                                 'local.func private @leaf(i1) -> i1'),
                  'algorithm-call-symbol')
commands.verified('module { local.func @stopped() { '
                  '"local.stop"() <{site = "stop", reason = "reject"}> : () -> () } }')
commands.verified('module { local.func @bad() { '
                  '"protocol.stop"() <{site = "stop", reason = "reject"}> : () -> () } }',
                  'parent')
commands.verified('module { local.func @bad() { '
                  '"local.stop"() <{site = "stop", reason = "reject", role = "P"}> : () -> () } }',
                  'mlir-unknown-property')

print(f"local callable checks: {commands.save()}")
