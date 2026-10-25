!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
 "runtime.binding"() {sym_name="multiply",contract="field.mul",arguments=["bls12-381.fr"],implementation="arkworks/field.mul"} : ()->()
 "runtime.binding"() {sym_name="add",contract="field.add",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "data.domain"() ({ ^entry(%xs:!V):
   %d = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
   "data.domain_yield"(%d) : (!data.domain<!F>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
 local.func private @body(%x:!F,%xs:!V)->!F attributes {logical_origin=["body",[]]} {
   %r = "algebra.exec.field_multiply"(%x,%x) {binding=@multiply,parameters=[],site="square"} : (!F,!F)->!F
   local.return %r : !F
 }
 local.func private @step(%state:!F,%x:!F,%xs:!V)->!F attributes {logical_origin=["step",[]]} {
   %r = "algebra.exec.field_add"(%state,%x) {binding=@add,parameters=[],site="add"} : (!F,!F)->!F
   local.return %r : !F
 }
 "local.finite_collect"() {sym_name="collect",function_type=(!V)->!V,domain=@items,body=@body} : ()->()
 "local.finite_fold"() {sym_name="fold",function_type=(!V,!F)->!F,domain=@items,step=@step} : ()->()
 local.func @evaluate(%xs:!V,%seed:!F)->!F attributes {logical_origin=["evaluate",[]]} {
   %ys = local.apply @collect(%xs) {site="collect"} : (!V)->!V
   %r = local.apply @fold(%ys,%seed) {site="fold"} : (!V,!F)->!F
   local.return %r : !F
 }
 "protocol.func"() ({ "protocol.return"() : ()->() })
 {sym_name="main",function_type=()->(),roles=["P"],input_roles=[],output_roles=[]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
