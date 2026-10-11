!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
 "local.binding"() {sym_name="add",contract="field.add",arguments=["bls12-381.fr"],implementation=""} : () -> ()
 "local.binding"() {sym_name="mul",contract="field.mul",arguments=["bls12-381.fr"],implementation=""} : () -> ()
 "data.domain"() ({
 ^entry(%xs:!V,%ys:!V,%ignored:!V):
   %x = "data.domain_elements"(%xs) : (!V) -> !data.domain<!F>
   %y = "data.domain_elements"(%ys) : (!V) -> !data.domain<!F>
   %z = "data.domain_elements"(%ignored) : (!V) -> !data.domain<!F>
   %d = "data.domain_zip"(%x,%y,%z) : (!data.domain<!F>,!data.domain<!F>,!data.domain<!F>) -> !data.domain<!F,!F,!F>
   "data.domain_yield"(%d) : (!data.domain<!F,!F,!F>) -> ()
 }) {sym_name="items",sym_visibility="private",function_type=(!V,!V,!V)->!data.domain<!F,!F,!F>} : ()->()
 local.func private @step(%state:!F,%x:!F,%y:!F,%ignored:!F,%xs:!V,%ys:!V,%zs:!V) -> !F attributes {logical_origin=["step",[]]} {
   %term = "algebra.exec.field_multiply"(%x,%y) {binding=@mul,parameters=[],site="term"} : (!F,!F)->!F
   %next = "algebra.exec.field_add"(%state,%term) {binding=@add,parameters=[],site="add"} : (!F,!F)->!F
   local.return %next : !F
 }
 "local.finite_fold"() {sym_name="fold",function_type=(!V,!V,!V,!F)->!F,domain=@items,step=@step} : ()->()
 local.func private @eager(%s:!F)->!F attributes {logical_origin=["eager",[]]} {
   "local.stop"() {reason="reject",site="eager"} : ()->()
 }
 local.func @work(%xs:!V,%ys:!V,%zs:!V,%init:!F) -> !F attributes {logical_origin=["work",[]]} {
   %first = local.apply @eager(%init) {site="first"} : (!F)->!F
   %r = local.apply @fold(%xs,%ys,%zs,%first) {site="fold"} : (!V,!V,!V,!F)->!F
   local.return %r : !F
 }
 "protocol.func"() ({
 ^entry(%xs:!V,%ys:!V,%zs:!V,%init:!F):
   %r = "protocol.local_call"(%xs,%ys,%zs,%init) {callee=@work,role="P",site="work"} : (!V,!V,!V,!F)->!F
   "protocol.return"(%r) : (!F)->()
 }) {sym_name="main",function_type=(!V,!V,!V,!F)->!F,roles=["P"],input_roles=[["P"],["P"],["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
