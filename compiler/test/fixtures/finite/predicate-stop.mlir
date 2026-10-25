!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
 "runtime.binding"() {sym_name="add",contract="field.add",arguments=["bls12-381.fr"],implementation=""} : () -> ()
 "runtime.binding"() {sym_name="mul",contract="field.mul",arguments=["bls12-381.fr"],implementation=""} : () -> ()
 "data.domain"() ({
 ^entry(%xs:!V,%ys:!V,%ignored:!V):
   %x = "data.domain_elements"(%xs) : (!V) -> !data.domain<!F>
   %y = "data.domain_elements"(%ys) : (!V) -> !data.domain<!F>
   %z = "data.domain_elements"(%ignored) : (!V) -> !data.domain<!F>
   %d = "data.domain_zip"(%x,%y,%z) : (!data.domain<!F>,!data.domain<!F>,!data.domain<!F>) -> !data.domain<!F,!F,!F>
   "data.domain_yield"(%d) : (!data.domain<!F,!F,!F>) -> ()
 }) {sym_name="items",sym_visibility="private",function_type=(!V,!V,!V)->!data.domain<!F,!F,!F>} : ()->()
 local.func private @step(%state:!F,%x:!F,%y:!F,%ignored:!F,%xs:!V,%ys:!V,%zs:!V) -> !F attributes {logical_origin=["step",[]]} {
   "local.stop"() {site="body_stop",reason="abort"} : ()->()
 }
 local.func private @predicate(%x:!F,%y:!F,%ignored:!F,%xs:!V,%ys:!V,%zs:!V) -> i1 attributes {logical_origin=["predicate",[]]} {
   "local.stop"() {site="predicate_stop",reason="reject"} : ()->()
 }
 "local.finite_fold"() {sym_name="fold",function_type=(!V,!V,!V,!F)->!F,domain=@items,step=@step,predicate=@predicate} : ()->()
 local.func @work(%xs:!V,%ys:!V,%zs:!V,%init:!F) -> !F attributes {logical_origin=["work",[]]} {
   %r = local.apply @fold(%xs,%ys,%zs,%init) {site="fold"} : (!V,!V,!V,!F)->!F
   local.return %r : !F
 }
 "protocol.func"() ({
 ^entry(%xs:!V,%ys:!V,%zs:!V,%init:!F):
   %r = "protocol.local_call"(%xs,%ys,%zs,%init) {callee=@work,role="P",site="work"} : (!V,!V,!V,!F)->!F
   "protocol.return"(%r) : (!F)->()
 }) {sym_name="main",function_type=(!V,!V,!V,!F)->!F,roles=["P"],input_roles=[["P"],["P"],["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
