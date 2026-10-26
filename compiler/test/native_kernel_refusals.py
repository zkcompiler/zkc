"""Actual native parsing/export rejects malformed kernel signatures and parameters."""
import json
from commands import Commands
from tools import records

commands = Commands(records())

def fixture(contract, domain, inputs, result, parameters):
    arguments = ','.join(f'%a{i}:{t}' for i, t in enumerate(inputs))
    operands = ','.join(f'%a{i}' for i in range(len(inputs)))
    types = ','.join(inputs)
    roles = json.dumps([['P']] * len(inputs))
    return f'''module {{ "protocol.module"() ({{
    "runtime.binding"() {{sym_name="kernel",contract="{contract}",arguments=["{domain}"],implementation=""}} : ()->()
    func.func @Work(%scope:!runtime.scope,{arguments})->!exec.outcome<({result})> attributes {{no_inline,runtime.origin=["Work",[]]}} {{
      %r = "exec.apply"(%scope,{operands}) <{{binding=@kernel,site="kernel",parameters={json.dumps(parameters)}}}> : (!runtime.scope,{types})->!exec.outcome<({result})>
      "exec.dispatch"(%r)[^done,^stopped] : (!exec.outcome<({result})>)->()
    ^done(%value:{result}):
      %out = "exec.returned"(%value) : ({result})->!exec.outcome<({result})>
      return %out : !exec.outcome<({result})>
    ^stopped(%stop:!exec.stop):
      %failure = "exec.failed"(%stop) : (!exec.stop)->!exec.outcome<({result})>
      return %failure : !exec.outcome<({result})>
    }}
    "protocol.func"() ({{^entry({arguments}):
      %r = "protocol.local_call"({operands}) {{callee=@Work,role="P",site="work"}} : ({types})->{result}
      "protocol.return"(%r) : ({result})->()
    }}) {{sym_name="main",function_type=({types})->{result},roles=["P"],input_roles={roles},output_roles=[["P"]]}} : ()->()
    }}) {{profile=#protocol.profile<protocol>}} : ()->() }}'''

def reject(text, code):
    commands.verified(text, code)
    commands.source('protocol-export', text, refuses=code)

field = '!algebra.field<"bls12-381.fr">'
vector = '!algebra.field_vector<"bls12-381.fr">'
gather = fixture('vector.gather', 'bls12-381.fr', [vector], vector, ['0', '3'])
commands.verified(gather)
physical = commands.verified(gather, None, '--zkc-participant-pipeline')
assert json.loads(commands.source('protocol-export', physical))[0] == 'zkc.program/0'
reject(gather.replace('["0", "3"]', '["0", "01"]'), 'execution-cfg: invocation parameter formation')
reject(gather.replace('["0", "3"]', '["-1"]'), 'execution-cfg: invocation parameter formation')
reject(gather.replace('["0", "3"]', '["18446744073709551616"]'), 'execution-cfg: invocation parameter formation')
for wrong in ('!algebra.field_array<"bls12-381.fr", 4>', '!algebra.field_matrix<"bls12-381.fr">',
              '!algebra.field_vector<"ristretto255.scalar">'):
    reject(gather.replace(vector, wrong), 'execution-cfg: binding port identity')
for tensor in ('tensor<?xi64>', f'tensor<?x{field}>', f'tensor<4x{field}>', f'tensor<?x?x{field}>'):
    reject(gather.replace(vector, tensor), 'execution-formation')
selected_call = 'implementation = "arkworks/vector.gather"'
assert physical.count(selected_call) == 1
reject(physical.replace(selected_call, 'implementation = "arkworks/unknown"'),
       'binding-implementation')

addition = fixture('field.add', 'bls12-381.fr', [field, field], field, [])
commands.verified(addition)
reject(addition.replace('"exec.apply"(%scope,%a0,%a1)', '"exec.apply"(%scope,%a0)')
       .replace(f' : (!runtime.scope,{field},{field})->', f' : (!runtime.scope,{field})->', 1), 'execution-cfg: binding port count')
reject(addition.replace('parameters=[]', 'parameters=["0"]'), 'execution-cfg: invocation parameter formation')
reject(fixture('field.add', 'bls12-381.fr',
               [field, field], 'i1', []), 'execution-cfg: binding port identity')
extra_result = '\n'.join(
    line.replace(f'!exec.outcome<({field})>', f'!exec.outcome<({field},{field})>')
    if '"exec.apply"' in line or '"exec.dispatch"' in line else line
    for line in addition.splitlines())
extra_result = extra_result.replace(f'^done(%value:{field}):',
                                    f'^done(%value:{field},%unused:{field}):')
reject(extra_result, 'execution-cfg: binding port count')
# A logical primitive without a lexical binding must not verify or export.
reject(addition.replace('binding=@kernel,', ''), "requires attribute 'binding'")
print(f'native kernel boundary: {commands.save()} checks')
