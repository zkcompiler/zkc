"""Optimizer reachability for shared field/group contractions and fixed choices."""
import json
from commands import Commands
from scoped_sources import invocation, scoped_function
from tools import records

output = records()
commands = Commands(output)


def reductions(program, contract):
    bindings = {binding[0]: binding for binding in program[1]}
    return [bindings[step[2]][3] for function in program[2] for step in function[4]
            if step[0] == 'op' and bindings[step[2]][1] == contract]


for group in (False, True):
    scalar = 'ristretto255.scalar' if group else 'bls12-381.fr'
    domain = 'ristretto255.group' if group else scalar
    value = f'!algebra.group<"{domain}">' if group else f'!algebra.field<"{scalar}">'
    mapping, reduction = ('curve.scale_each', 'curve.msm') if group else ('vector.mul', 'vector.dot')
    provider = 'dalek' if group else 'arkworks'
    operations = [
        invocation('exec.apply', ['!v', '!a'], ['!a'],
                   'binding=@map,site="map",parameters=[]',
                   ['%a2', '%a3'], ['%mapped'], 'mapped'),
        invocation('exec.apply', ['!v', '!a'], ['!r'],
                   'binding=@reduce,site="first",parameters=[]',
                   ['%a0', '%mapped'], ['%first'], 'first'),
        invocation('exec.apply', ['!v', '!a'], ['!r'],
                   'binding=@reduce,site="second",parameters=[]',
                   ['%a1', '%mapped'], ['%second'], 'second'),
    ]
    contraction = scoped_function('contract', ['!v', '!v', '!v', '!a'], ['!r', '!r'],
                                  '\n'.join(operations), ['%first', '%second'])
    source = f'''!f = !algebra.field<"{scalar}">
!r = {value}
!v = !algebra.field_vector<"{scalar}">
!a = !algebra.{"group_vector" if group else "field_vector"}<"{domain}">
module {{ "protocol.module"() ({{
 "runtime.binding"() {{sym_name="map",contract="{mapping}",arguments=["{domain}"],implementation=""}} : ()->()
 "runtime.binding"() {{sym_name="reduce",contract="{reduction}",arguments=["{domain}"],implementation=""}} : ()->()
 {contraction}
 "protocol.func"() ({{ ^entry(%w:!v,%x:!v,%f:!v,%v:!a):
  %out:2 = "protocol.local_call"(%w,%x,%f,%v) {{callee=@contract,role="P",site="contract"}} : (!v,!v,!v,!a)->(!r,!r)
  "protocol.return"(%out#0,%out#1) : (!r,!r)->()
 }}) {{sym_name="main",function_type=(!v,!v,!v,!a)->(!r,!r),roles=["P"],input_roles=[["P"],["P"],["P"],["P"]],output_roles=[["P"],["P"]]}} : ()->()
}}) {{profile=#protocol.profile<protocol>}} : ()->() }}'''
    for optimize in (False, True):
        ir = commands.verified(source, None, f'--zkc-participant-pipeline=linear-contractions={str(optimize).lower()}')
        program = json.loads(commands.source('protocol-export', ir))
        assert program[0] == 'zkc.program/0'
        implementations = {binding[3] for binding in program[1]}
        expected = f'{provider}{"-diagonal" if optimize else ""}/{reduction}'
        assert expected in implementations, implementations
        assert reductions(program, reduction) == [expected, expected], reductions(program, reduction)
        (output / f'{"group" if group else "field"}_{optimize}.json').write_text(json.dumps(program))
    selected = source.replace('contract="' + reduction + '",arguments=["' + domain + '"],implementation=""',
                              'contract="' + reduction + '",arguments=["' + domain + '"],implementation="' + provider + '/' + reduction + '"')
    assert selected != source
    ir = commands.verified(selected, None, '--zkc-participant-pipeline=linear-contractions=true')
    program = json.loads(commands.source('protocol-export', ir))
    assert reductions(program, reduction) == [f'{provider}/{reduction}'] * 2, reductions(program, reduction)
    if group:
        commands.verified(selected.replace('dalek/curve.msm', 'dalek-vartime/curve.msm'), 'binding-implementation')
print(f'linear contraction optimizer checks: {commands.save()}')
