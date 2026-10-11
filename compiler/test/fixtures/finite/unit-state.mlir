!F = !algebra.field<"bls12-381.fr">
!V = tensor<?x!F>
module { "protocol.module"() ({
 "data.domain"() ({
 ^entry(%xs:!V):
   %d = "data.domain_elements"(%xs) : (!V) -> !data.domain<!F>
   "data.domain_yield"(%d) : (!data.domain<!F>) -> ()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
 local.func private @step(%item:!F,%xs:!V,%enabled:i1) attributes {logical_origin=["step",[]]} {
   "local.stop"() {site="body_stop",reason="abort"} : ()->()
 }
 local.func private @predicate(%item:!F,%xs:!V,%enabled:i1) -> i1 attributes {logical_origin=["predicate",[]]} {
   local.return %enabled : i1
 }
 "local.finite_fold"() {sym_name="fold",function_type=(!V,i1)->(),domain=@items,step=@step,predicate=@predicate} : ()->()
 local.func @work(%xs:!V,%enabled:i1) -> i1 attributes {logical_origin=["work",[]]} {
   local.apply @fold(%xs,%enabled) {site="fold"} : (!V,i1)->()
   local.return %enabled : i1
 }
 "protocol.func"() ({
 ^entry(%xs:!V,%enabled:i1):
   %r = "protocol.local_call"(%xs,%enabled) {callee=@work,role="P",site="work"} : (!V,i1)->i1
   "protocol.return"(%r) : (i1)->()
 }) {sym_name="main",function_type=(!V,i1)->i1,roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
