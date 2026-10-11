
!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
!tag = !local.variant<"variant:5b227a6b632e76617269616e742f30222c5b2243686f696365222c226c656674222c5b5d2c5b2231222c2232225d2c227269676874222c5b2234222c2232225d2c5b2233222c2235225d2c5b2230222c2236225d5d5d">
module { "protocol.module"() ({
 "local.binding"() {sym_name="add",contract="field.add",arguments=["bls12-381.fr"],implementation=""} : () -> ()
 "data.domain"() ({
 ^entry(%xs:!V):
   %d = "data.domain_elements"(%xs) : (!V) -> !data.domain<!F>
   "data.domain_yield"(%d) : (!data.domain<!F>) -> ()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
 local.func private @step(%state:!F,%item:!F,%xs:!V) -> !F attributes {logical_origin=["step",[]]} {
   %choice = "local.variant_inject"() {alternative="left",site="choice"} : ()->!tag
   %next = "local.match"(%choice,%state,%item) ({ ^left(%s:!F,%x:!F):
     %r = "algebra.exec.field_add"(%s,%x) {binding=@add,parameters=[],site="add"} : (!F,!F)->!F
     "local.yield"(%r) : (!F)->()
   }, { ^right(%s:!F,%x:!F):
     "local.stop"() {reason="reject",site="stop"} : ()->()
   }) {alternatives=["left","right"],site="match"} : (!tag,!F,!F)->!F
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
