!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
!M = !algebra.field_matrix<"bls12-381.fr">
module { "protocol.module"() ({
 "runtime.binding"() {sym_name="add",contract="field.add",arguments=["bls12-381.fr"],implementation=""} : () -> ()
 "runtime.binding"() {sym_name="mul",contract="field.mul",arguments=["bls12-381.fr"],implementation=""} : () -> ()
 "data.domain"() ({
 ^entry(%xs:!M,%ys:!V,%ignored:!V,%selected:ui64):
   %x = "data.domain_matrix_row"(%xs,%selected) : (!M,ui64) -> !data.domain<!F>
   %y = "data.domain_elements"(%ys) : (!V) -> !data.domain<!F>
   %z = "data.domain_elements"(%ignored) : (!V) -> !data.domain<!F>
   %d = "data.domain_zip"(%x,%y,%z) : (!data.domain<!F>,!data.domain<!F>,!data.domain<!F>) -> !data.domain<!F,!F,!F>
   "data.domain_yield"(%d) : (!data.domain<!F,!F,!F>) -> ()
 }) {sym_name="items",sym_visibility="private",function_type=(!M,!V,!V,ui64)->!data.domain<!F,!F,!F>} : ()->()
 local.func private @step(%state:!F,%x:!F,%y:!F,%ignored:!F,%xs:!M,%ys:!V,%zs:!V,%selected:ui64) -> !F attributes {logical_origin=["step",[]]} {
   %term = "algebra.exec.field_multiply"(%x,%y) {binding=@mul,parameters=[],site="term"} : (!F,!F)->!F
   %next = "algebra.exec.field_add"(%state,%term) {binding=@add,parameters=[],site="add"} : (!F,!F)->!F
   local.return %next : !F
 }
 "local.finite_fold"() {sym_name="fold",function_type=(!M,!V,!V,ui64,!F)->!F,domain=@items,step=@step} : ()->()
 local.func @work(%xs:!M,%ys:!V,%zs:!V,%selected:ui64,%init:!F) -> !F attributes {logical_origin=["work",[]]} {
   %r = local.apply @fold(%xs,%ys,%zs,%selected,%init) {site="fold"} : (!M,!V,!V,ui64,!F)->!F
   local.return %r : !F
 }
 "protocol.func"() ({
 ^entry(%xs:!M,%ys:!V,%zs:!V,%selected:ui64,%init:!F):
   %r = "protocol.local_call"(%xs,%ys,%zs,%selected,%init) {callee=@work,role="P",site="work"} : (!M,!V,!V,ui64,!F)->!F
   "protocol.return"(%r) : (!F)->()
 }) {sym_name="main",function_type=(!M,!V,!V,ui64,!F)->!F,roles=["P"],input_roles=[["P"],["P"],["P"],["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
