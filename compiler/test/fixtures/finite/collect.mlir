!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
 "local.binding"() {sym_name="mul",contract="field.mul",arguments=["bls12-381.fr"],implementation=""} : () -> ()
 "data.domain"() ({
 ^entry(%xs:!V):
   %d = "data.domain_elements"(%xs) : (!V) -> !data.domain<!F>
   "data.domain_yield"(%d) : (!data.domain<!F>) -> ()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
 local.func private @square(%x:!F,%xs:!V) -> !F attributes {logical_origin=["square",[]]} {
   %y = "algebra.exec.field_multiply"(%x,%x) {binding=@mul,parameters=[],site="square"} : (!F,!F)->!F
   local.return %y : !F
 }
 "local.finite_collect"() {sym_name="collect",function_type=(!V)->!V,domain=@items,body=@square} : ()->()
 local.func @work(%xs:!V) -> !V attributes {logical_origin=["work",[]]} {
   %r = local.apply @collect(%xs) {site="collect"} : (!V)->!V
   local.return %r : !V
 }
 "protocol.func"() ({
 ^entry(%xs:!V):
   %r = "protocol.local_call"(%xs) {callee=@work,role="P",site="work"} : (!V)->!V
   "protocol.return"(%r) : (!V)->()
 }) {sym_name="main",function_type=(!V)->!V,roles=["P"],input_roles=[["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
