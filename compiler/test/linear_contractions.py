"""Optimizer reachability for shared field/group contractions and fixed choices."""
import json
from commands import Commands
from tools import records

output = records()
commands = Commands(output)
for group in (False, True):
    scalar = 'ristretto255.scalar' if group else 'bls12-381.fr'
    domain = 'ristretto255.group' if group else scalar
    value = f'!algebra.group<"{domain}">' if group else f'!algebra.field<"{scalar}">'
    mapping, reduction = ('curve.scale_each', 'curve.msm') if group else ('vector.mul', 'vector.dot')
    map_op, reduce_op = ('group_scale_each', 'group_msm') if group else ('vector_mul', 'vector_dot')
    provider = 'dalek' if group else 'arkworks'
    source = f'''!f = !algebra.field<"{scalar}">
!r = {value}
!v = tensor<?x!f>
!a = tensor<?x!r>
module {{ "protocol.module"() ({{
 "local.binding"() {{sym_name="map",contract="{mapping}",arguments=["{domain}"],implementation=""}} : ()->()
 "local.binding"() {{sym_name="reduce",contract="{reduction}",arguments=["{domain}"],implementation=""}} : ()->()
 local.func @contract(%w:!v,%x:!v,%f:!v,%v:!a)->(!r,!r) attributes {{logical_origin=["contract",[]]}} {{
  %mapped = "algebra.exec.{map_op}"(%f,%v) {{binding=@map,site="map",parameters=[]}} : (!v,!a)->!a
  %first = "algebra.exec.{reduce_op}"(%w,%mapped) {{binding=@reduce,site="first",parameters=[]}} : (!v,!a)->!r
  %second = "algebra.exec.{reduce_op}"(%x,%mapped) {{binding=@reduce,site="second",parameters=[]}} : (!v,!a)->!r
  local.return %first,%second : !r,!r
 }}
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
        (output / f'{"group" if group else "field"}_{optimize}.json').write_text(json.dumps(program))
    selected = source.replace('contract="' + reduction + '",arguments=["' + domain + '"],implementation=""',
                              'contract="' + reduction + '",arguments=["' + domain + '"],implementation="' + provider + '/' + reduction + '"')
    assert selected != source
    ir = commands.verified(selected, None, '--zkc-participant-pipeline=linear-contractions=true')
    program = json.loads(commands.source('protocol-export', ir))
    assert any(b[3] == f'{provider}/{reduction}' for b in program[1])
    if group:
        commands.verified(selected.replace('dalek/curve.msm', 'dalek-vartime/curve.msm'), 'binding-implementation')
print(f'linear contraction optimizer checks: {commands.save()}')
