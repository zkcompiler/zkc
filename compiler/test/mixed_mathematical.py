"""Mixed total mathematics and authored local execution retain separate rules."""
import json
from pathlib import Path
from commands import Commands
from tools import records

OUT = records()
commands = Commands(OUT)
source = (Path(__file__).parent / 'fixtures/mathematical/local-execution.mlir').read_text()
prepared = commands.verified(source, None, '--zkc-prepare-protocol')
assert 'func.func @work' in prepared and 'call @leaf' in prepared
assert 'runtime.site = "nested"' in prepared
participant = commands.verified(prepared, None, '--zkc-project-protocol')
simplified = commands.verified(participant, None, '--zkc-simplify-participant')
bound = commands.verified(simplified, None, '--zkc-lower-math')
assert 'lc_6_nested_4_leaf_5_twice' in bound
assert 'call @leaf' not in bound
physical = commands.verified(bound, None, '--zkc-select-physical')
carrier = json.loads(commands.source('protocol-export', physical))
(OUT / 'mixed.json').write_text(json.dumps(carrier))
(OUT / 'mixed.source.mlir').write_text(source)
(OUT / 'mixed.physical.mlir').write_text(physical)
functions = {f[1]: f for f in carrier[2]}
sender = next(p for p in carrier[3] if p[3] == 'P')
receiver = next(p for p in carrier[3] if p[3] == 'V')
assert [op[0] for op in sender[6]] == ['local'] * 5 + ['send', 'return']
assert [op[1] for op in sender[6][:5]] == ['before_work', 'first_check', 'second_check', 'calculation_0', 'work']
assert [op[0] for op in receiver[6]] == ['receive', 'return']
for call in (sender[6][0], sender[6][3]):
    function = functions[call[2]]
    assert not any('resource' in str(port) or 'rng:' in str(port) for port in function[2:4])
assert functions['work'][4][0][0] == 'if', 'math optimization changed authored control'
assert functions['work'][4][0][1] == 'lc_15_authored_branch'
assert 'host.resource/0' in functions['work'][2][1][1]

# Verify the mutation really changes the fixture before checking its refusal.
def refuses(old, new, diagnostic):
    changed = source.replace(old, new)
    assert changed != source
    commands.verified(changed, diagnostic, '--zkc-project-protocol')

refuses('input_roles=[["P"],["P"],["P"]]', 'input_roles=[["P"],["P","V"],["P"]]', 'exactly one owner')
refuses('output_roles=[["P", "V"],["P"]]', 'output_roles=[["P", "V"],["P","V"]]', 'exactly one owner')
refuses('"protocol.return"(%sent, %done#1)', '"protocol.return"(%sent, %resource)', 'affine component used more than once')
refuses('callee=@work, role="P"', 'callee=@work, role="V"', 'available owner operands')
refuses('    %sent = protocol.exchange', '    %alias = protocol.restrict_roles %done#1 {roles=["P"]} : !runtime.capability<"rng:bls12-381.fr">\n    %sent = protocol.exchange', 'owner-local values cannot be restricted')
refuses('    %sent = protocol.exchange', '    %illegal = protocol.exchange %done#1 {sender="P", receiver="V", site="resource_wire"} : !runtime.capability<"rng:bls12-381.fr">\n    %sent = protocol.exchange', 'exchange requires an admitted wire type')
# Even a never-called definition is admitted before optimization can remove it.
refuses('    func.func @check', '    func.func private @unused(!runtime.scope, i1) -> !exec.outcome<(i1)> attributes {no_inline,runtime.origin=["unused",[]]}\n    func.func @check', 'execution-source-closure')
refuses('      %2 = "exec.returned"(%1)', '      %bad = algebra.field_add %arg1, %arg1 : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">\n      %2 = "exec.returned"(%1)', 'execution-source-closure')
refuses('{runtime.site = "nested"}', '{runtime.site = "nested", bad="new_semantics"}', 'execution-source-closure')

refuses('callee=@work', 'callee=@missing', 'interactive-symbol-kind')
refuses('callee=@work', 'callee=@main', 'interactive-symbol-kind')
refuses('callee=@work', 'callee=@leaf', 'interactive-call-type')
for ty in ['!runtime.capability<"rng:bls12-381.fr">', '!commitment.polynomial<"multilinear.kzg.bls12-381/0", "prover_key">', '!commitment.polynomial<"multilinear.kzg.bls12-381/0", "verifier_key">']:
    declaration = f'relation.declare @forbidden {{kind="external", key="example/type", revision="0", signature=({ty}) -> i1, purposes=["statement"]}}'
    commands.verified('module { ' + declaration + ' }', 'relation-declaration-signature')

# Non-scalar wire data passes through the common graph as whole components.
vector = '''module { "protocol.module"() ({
"protocol.func"() ({
^entry(%x: !algebra.field_vector<"bls12-381.fr">):
  %part = protocol.restrict_roles %x {roles=["P"]} : !algebra.field_vector<"bls12-381.fr">
  %sent = protocol.exchange %part {sender="P", receiver="V", site="vector"} : !algebra.field_vector<"bls12-381.fr">
  "protocol.return"(%sent) : (!algebra.field_vector<"bls12-381.fr">) -> ()
}) {sym_name="vector", function_type=(!algebra.field_vector<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">, roles=["P","V"], input_roles=[["P","V"]], output_roles=[["P","V"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () }'''
vector_physical = commands.verified(vector, None, '--zkc-project-protocol', '--zkc-lower-math', '--zkc-select-physical')
assert 'vector:bls12-381.fr' in commands.source('protocol-export', vector_physical)
commands.verified(vector.replace('!algebra.field_vector<"bls12-381.fr">', '!algebra.fixed_vector<i1, 2>'), 'exactly one owner')
# Generate resource-transition variants for execution by mixed_native.rs.
draw = source.replace('    func.func @leaf', '  "runtime.binding"() {sym_name="draw", contract="random.draw", arguments=["bls12-381.fr"], implementation=""} : () -> ()\n    func.func @leaf', 1)
completion = '      %18 = "exec.returned"(%17, %arg2)'
assert draw.count(completion) == 1
field = '!algebra.field<"bls12-381.fr">'
rng = '!runtime.capability<"rng:bls12-381.fr">'
draw = draw.replace(completion, f'''      %sample = "exec.apply"(%arg0, %arg2) <{{binding=@draw, parameters=[], site="draw"}}> : (!runtime.scope, {rng}) -> !exec.outcome<({field}, {rng})>
      "exec.dispatch"(%sample)[^drawn,^bb2] : (!exec.outcome<({field}, {rng})>) -> ()
    ^drawn(%unused_sample: {field}, %drawn_rng: {rng}):
      %18 = "exec.returned"(%17, %drawn_rng)''')
stop_after = '\n'.join(line for line in draw.splitlines() if 'site="before_work"' not in line and 'callee=@check' not in line)
stop_after = stop_after.replace('    %sent = protocol.exchange', '    protocol.guard %go {owner="P", site="before_work"}\n    %sent = protocol.exchange')
for name, variant in [('mixed-draw', draw), ('mixed-stop-after', stop_after)]:
    ir = commands.verified(variant, None, '--zkc-project-protocol', '--zkc-simplify-participant', '--zkc-lower-math', '--zkc-select-physical')
    (OUT / (name + '.json')).write_text(commands.source('protocol-export', ir))
    (OUT / (name + '.source.mlir')).write_text(variant)
print(f'mixed mathematical checks: {commands.save()}')

# Full native pipelines for custody across interactions and stopping local work.
for name in ['mixed-unit', 'mixed-inverse', 'mixed-nonce', 'mixed-transcript']:
    variant = (Path(__file__).parent / f'fixtures/mathematical/{name}.mlir').read_text()
    ir = commands.verified(variant, None, '--zkc-project-protocol', '--zkc-simplify-participant', '--zkc-lower-math', '--zkc-select-physical')
    (OUT / (name + '.json')).write_text(commands.source('protocol-export', ir))
    (OUT / (name + '.physical.mlir')).write_text(ir)

# A reusable service root and an affine RNG have different entry/call custody.
service_draw = draw.replace('^entry(%x:', '^entry(%service: !protocol.service_ref<"random.bls12-381.fr/0">, %x:')
service_draw = service_draw.replace('function_type=(', 'function_type=(!protocol.service_ref<"random.bls12-381.fr/0">, ', 1)
service_draw = service_draw.replace('input_roles=[["P"],["P"],["P"]]', 'input_roles=[["P"],["P"],["P"],["P"]]')
service_draw = service_draw.replace('    %sum =', '    %queried = "protocol.query"(%service) {method="draw", owner="P", site="query"} : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">\n    %sum =')
service_draw = service_draw.replace('algebra.field_add %x, %x', 'algebra.field_add %x, %queried')
ir = commands.verified(service_draw, None, '--zkc-project-protocol', '--zkc-simplify-participant', '--zkc-lower-math', '--zkc-select-physical')
(OUT / 'mixed-service.json').write_text(commands.source('protocol-export', ir))
print(f'Mixed custody boundary fixtures: {commands.save()}')
