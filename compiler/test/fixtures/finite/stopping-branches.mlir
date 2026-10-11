
!F = !algebra.field<"bls12-381.fr">
!V = tensor<?x!F>
module { "protocol.module"() ({
 "local.binding"() {sym_name="add",contract="field.add",arguments=["bls12-381.fr"],implementation=""} : () -> ()
 "data.domain"() ({
 ^entry(%xs:!V):
   %d = "data.domain_elements"(%xs) : (!V) -> !data.domain<!F>
   "data.domain_yield"(%d) : (!data.domain<!F>) -> ()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
 local.func private @halt(%s:!F) -> !F attributes {logical_origin=["halt",[]]} {
   "local.stop"() {site="halt",reason="abort"} : ()->()
 }
 local.func private @step(%state:!F,%item:!F,%xs:!V) -> !F attributes {logical_origin=["step",[]]} {
   %yes = "local.bool_constant"() {value=true,site="yes"} : ()->i1
   %next = "local.if"(%yes,%state) ({ ^left(%s:!F):
     %x = local.apply @halt(%s) {site="left"} : (!F)->!F
     "local.yield"(%x) : (!F)->()
   }, { ^right(%s:!F):
     %x = local.apply @halt(%s) {site="right"} : (!F)->!F
     "local.yield"(%x) : (!F)->()
   }) {site="branch"} : (i1,!F)->!F
   local.return %next : !F
 }
 "local.finite_fold"() {sym_name="fold",function_type=(!V,!F)->!F,domain=@items,step=@step} : ()->()
 local.func @work(%xs:!V,%init:!F) -> !F attributes {logical_origin=["work",[]]} {
   %r = local.apply @fold(%xs,%init) {site="fold"} : (!V,!F)->!F
   local.return %r : !F
 }
 "protocol.func"() ({
 ^entry(%xs:!V,%init:!F):
   %r = "protocol.local_call"(%xs,%init) {callee=@work,role="P",site="work"} : (!V,!F)->!F
   "protocol.return"(%r) : (!F)->()
 }) {sym_name="main",function_type=(!V,!F)->!F,roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
