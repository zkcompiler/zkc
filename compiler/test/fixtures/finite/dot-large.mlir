!F = !algebra.field<"bls12-381.fr">
!V = tensor<?x!F>
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
 local.func @work(%xs:!V,%ys:!V,%zs:!V,%init:!F) -> !F attributes {logical_origin=["work",[]]} {
   %r = local.apply @fold(%xs,%ys,%zs,%init) {site="fold"} : (!V,!V,!V,!F)->!F
   local.return %r : !F
 }
 "local.binding"() {sym_name="length",contract="vector.length",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="fill",contract="vector.fill",arguments=["bls12-381.fr"],implementation=""} : ()->()
 local.func @large(%xs:!V,%factor:!F,%init:!F) -> !F attributes {logical_origin=["large",[]]} {
   %n = "algebra.exec.vector_length"(%xs) {binding=@length,parameters=[],site="length"} : (!V)->ui64
   %ys = "algebra.exec.vector_fill"(%factor,%n) {binding=@fill,parameters=[],site="fill"} : (!F,ui64)->!V
   %r = local.apply @work(%xs,%ys,%xs,%init) {site="work"} : (!V,!V,!V,!F)->!F
   local.return %r : !F
 }
 "protocol.func"() ({ ^entry(%xs:!V,%factor:!F,%init:!F):
   %r = "protocol.local_call"(%xs,%factor,%init) {callee=@large,role="P",site="large"} : (!V,!F,!F)->!F
   "protocol.return"(%r) : (!F)->()
 }) {sym_name="main",function_type=(!V,!F,!F)->!F,roles=["P"],input_roles=[["P"],["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
