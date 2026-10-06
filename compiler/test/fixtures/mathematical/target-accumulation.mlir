!f = !algebra.field<"bn254.fr">
!g1 = !algebra.group<"bn254.g1">
!g2 = !algebra.group<"bn254.g2">
!gt = !algebra.group<"bn254.gt">
module { "protocol.module"() ({
"local.binding"() {sym_name="field_from_index",contract="field.from_index",arguments=["bn254.fr"],implementation=""} : ()->()

local.func @count_scalar(%count:ui64)->(!f) attributes {logical_origin=["count_scalar",[]]} {
  %scalar = "algebra.exec.field_from_index"(%count) {binding=@field_from_index,parameters=[],site="scalar"} : (ui64)->(!f)
  local.return %scalar : !f
}
"protocol.func"() ({ ^entry(%a:!g1,%b:!g2,%x:!f,%n:ui64):
 %zero = "algebra.constant"() {value="0"} : ()->!f
 %base = algebra.pairing %a,%b : (!g1,!g2)->!gt
 %term = algebra.group_scale %base,%x : (!gt,!f)->!gt
 %identity = algebra.group_scale %base,%zero : (!gt,!f)->!gt
 %sum = "protocol.repeat"(%n,%identity,%term) ({ ^body(%i:ui64,%state:!gt,%addend:!gt):
   %next = algebra.group_add %state,%addend : (!gt,!gt)->!gt
   "protocol.yield"(%next) : (!gt)->()
 }) {site="accumulate",carried=1:i64,maximum=16:i64,roles=["P","V"],carried_roles=[["P"]]} : (ui64,!gt,!gt)->!gt
 %received = protocol.exchange %sum {sender="P",receiver="V",site="target"} : !gt
 %count = "protocol.local_call"(%n) {callee=@count_scalar,role="V",site="count"} : (ui64)->!f
 %exponent = algebra.field_multiply %count,%x : (!f,!f)->!f
 %expected_a = algebra.group_scale %a,%exponent : (!g1,!f)->!g1
 %expected = algebra.pairing %expected_a,%b : (!g1,!g2)->!gt
 %valid = algebra.group_equal %received,%expected : (!gt,!gt)->i1
 "protocol.return"(%valid) : (i1)->()
}) {sym_name="main",function_type=(!g1,!g2,!f,ui64)->i1,roles=["P","V"],input_roles=[["P","V"],["P","V"],["P","V"],["P","V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
