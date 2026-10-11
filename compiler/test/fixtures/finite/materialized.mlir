
!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
 "local.binding"() {sym_name="add",contract="field.add",arguments=["bls12-381.fr"],implementation=""} : () -> ()
 "data.domain"() ({
 ^entry(%xs:!V):
   %d = "data.domain_elements"(%xs) : (!V) -> !data.domain<!F>
   "data.domain_yield"(%d) : (!data.domain<!F>) -> ()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
 local.func private @body(%item:!F,%xs:!V) -> !F attributes {logical_origin=["body",[]]} {
   "local.stop"() {site="body",reason="abort"} : ()->()
 }
 "local.finite_collect"() {sym_name="collect",function_type=(!V)->!V,domain=@items,body=@body} : ()->()
 local.func private @reduce(%xs:!V,%init:!F) -> !F attributes {logical_origin=["reduce",[]]} {
   "local.stop"() {site="reducer",reason="reject"} : ()->()
 }
 local.func @work(%xs:!V,%init:!F) -> !F attributes {logical_origin=["work",[]]} {
   %collected = local.apply @collect(%xs) {site="collect"} : (!V)->!V
   %r = local.apply @reduce(%collected,%init) {site="reduce"} : (!V,!F)->!F
   local.return %r : !F
 }
 "protocol.func"() ({
 ^entry(%xs:!V,%init:!F):
   %r = "protocol.local_call"(%xs,%init) {callee=@work,role="P",site="work"} : (!V,!F)->!F
   "protocol.return"(%r) : (!F)->()
 }) {sym_name="main",function_type=(!V,!F)->!F,roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
