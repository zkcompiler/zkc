"""Actual native parsing/export rejects malformed kernel signatures and parameters."""
import json
from commands import Commands
from tools import records

commands = Commands(records())

def fixture(contract, domain, operation, inputs, result, parameters):
    arguments = ','.join(f'%a{i}:{t}' for i, t in enumerate(inputs))
    operands = ','.join(f'%a{i}' for i in range(len(inputs)))
    types = ','.join(inputs)
    roles = json.dumps([['P']] * len(inputs))
    return f'''module {{ "protocol.module"() ({{
    "local.binding"() {{sym_name="kernel",contract="{contract}",arguments=["{domain}"],implementation=""}} : ()->()
    local.func @Work({arguments})->{result} attributes {{logical_origin=["Work",[]]}} {{
      %r = "{operation}"({operands}) {{binding=@kernel,site="kernel",parameters={json.dumps(parameters)}}} : ({types})->{result}
      local.return %r : {result}
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
gather = fixture('vector.gather', 'bls12-381.fr', 'algebra.exec.vector_gather', [vector], vector, ['0', '3'])
commands.verified(gather)
physical = commands.verified(gather, None, '--zkc-participant-pipeline')
assert json.loads(commands.source('protocol-export', physical))[0] == 'zkc.program/0'
reject(gather.replace('["0", "3"]', '["0", "01"]'), 'noncanonical-natural')
reject(gather.replace('["0", "3"]', '["-1"]'), 'expected-natural')
reject(gather.replace('["0", "3"]', '["18446744073709551616"]'), 'interactive-kernel-parameters')
for wrong in ('!algebra.field_array<"bls12-381.fr", 4>', '!algebra.field_matrix<"bls12-381.fr">',
              '!algebra.field_vector<"ristretto255.scalar">'):
    reject(gather.replace(vector, wrong), 'binding-operation-signature')
for tensor in ('tensor<?xi64>', f'tensor<?x{field}>', f'tensor<4x{field}>', f'tensor<?x?x{field}>'):
    reject(gather.replace(vector, tensor), 'logical protocol data or capability')
selected_call = 'binding = @kernel, implementation = "arkworks/vector.gather"'
assert physical.count(selected_call) == 1
reject(physical.replace(selected_call, 'binding = @kernel, implementation = "arkworks/unknown"'),
       'binding-implementation')

addition = fixture('field.add', 'bls12-381.fr', 'algebra.exec.field_add', [field, field], field, [])
commands.verified(addition)
reject(addition.replace('"algebra.exec.field_add"(%a0,%a1)', '"algebra.exec.field_add"(%a0)')
       .replace(f' : ({field},{field})->{field}', f' : ({field})->{field}', 1), 'binding-operation-signature')
reject(addition.replace('parameters=[]', 'parameters=["0"]'), 'interactive-kernel-parameters')
reject(fixture('field.add', 'bls12-381.fr', 'algebra.exec.field_add',
               [field, field], 'i1', []), 'binding-operation-signature')
extra_result = addition.replace('%r = "algebra.exec.field_add"', '%r:2 = "algebra.exec.field_add"')
extra_result = extra_result.replace(f' : ({field},{field})->{field}', f' : ({field},{field})->({field},{field})', 1)
extra_result = extra_result.replace('local.return %r :', 'local.return %r#0 :')
reject(extra_result, 'binding-operation-signature')
# A logical primitive without a lexical binding must not verify or export.
reject(f'module {{ %r = "algebra.exec.field_constant"() {{site="value",parameters=["1"]}} : ()->{field} }}', 'binding-reference')
print(f'native kernel boundary: {commands.save()} checks')
