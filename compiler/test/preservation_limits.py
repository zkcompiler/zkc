"""Repeated observations and admitted expansion sizes stay within checker work."""
import json
from cases import case, counted
from commands import Commands
from tools import records

commands = Commands(records())
field = '!algebra.field<"bls12-381.fr">'


def function(name, arguments, results, body, roles, input_roles, output_roles):
    types = ','.join(ty for _, ty in arguments)
    result_types = ','.join(results)
    return f'''"protocol.func"() ({{
    ^entry({','.join(name + ':' + ty for name, ty in arguments)}):
      {body}
    }}) {{sym_name="{name}", function_type=({types})->({result_types}),
      roles={json.dumps(roles)}, input_roles={json.dumps(input_roles)},
      output_roles={json.dumps(output_roles)}}} : ()->()'''


def module(definitions):
    return 'module { "protocol.module"() ({\n' + '\n'.join(definitions) + '\n}) {profile=#protocol.profile<protocol>} : ()->() }'


with case('one interpolation reused across many distinct received challenges'):
    samples, observations = 40, 32
    array = f'tensor<{samples}x{field}>'
    polynomial = '!poly.polynomial<"bls12-381.fr",1>'
    points = json.dumps([str(i) for i in range(samples)])
    body = [f'%p = "poly.interpolate"(%table) {{points={points}}} : ({array})->{polynomial}']
    for i in range(observations):
        body += [f'%r{i} = protocol.exchange %x{i} {{site="challenge{i}",sender="V",receiver="P"}} : {field}',
                 f'%e{i} = "poly.evaluate"(%p,%r{i}) : ({polynomial},{field})->{field}',
                 f'%o{i} = protocol.exchange %e{i} {{site="response{i}",sender="P",receiver="V"}} : {field}']
    body += [f'"protocol.return"({",".join(f"%o{i}" for i in range(observations))}) : ({",".join([field] * observations)})->()']
    text = module([function('main', [('%table', array)] + [(f'%x{i}', field) for i in range(observations)],
                            [field] * observations, '\n'.join(body), ['P', 'V'],
                            [['P']] + [['V']] * observations, [['V']] * observations)])
    participant = commands.verified(text, None, '--zkc-project-protocol=simplify=false')
    lowered = commands.verified(participant, None, '--zkc-eliminate-polynomials')
    assert '!poly.polynomial' not in lowered

with case('preparation of sixty thousand distinct instantiated arithmetic operations'):
    length, calls = 1000, 60
    chain = []
    previous = '%x'
    for i in range(length):
        chain += [f'%m{i} = algebra.field_multiply {previous},%x : ({field},{field})->{field}']
        previous = f'%m{i}'
    chain += [f'"protocol.return"({previous}) : ({field})->()']
    leaf = function('leaf', [('%x', field)], [field], '\n'.join(chain), ['P'], [['P']], [['P']])
    body = [f'%y{i} = "protocol.apply"(%x{i}) {{callee=@leaf,site="call{i}",roles=["P"]}} : ({field})->{field}' for i in range(calls)]
    body += [f'"protocol.return"({",".join(f"%y{i}" for i in range(calls))}) : ({",".join([field]*calls)})->()']
    entry = function('main', [(f'%x{i}', field) for i in range(calls)], [field]*calls,
                     '\n'.join(body), ['P'], [['P']]*calls, [['P']]*calls)
    prepared = commands.verified(module([leaf, entry]), None, '--zkc-prepare-protocol=simplify=false')
    assert '"protocol.apply"' not in prepared
    assert prepared.count('algebra.field_multiply') == (calls + 1) * length

print(f'{counted()} preservation limit cases; {commands.save()} tool checks')
