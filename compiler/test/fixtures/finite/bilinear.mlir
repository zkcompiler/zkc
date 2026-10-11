!F = !algebra.field<"bls12-381.fr">
!V = tensor<?x!F>
!M = tensor<?x?x!F>
module { "protocol.module"() ({
 "local.binding"() {sym_name="get",contract="matrix.get",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="add",contract="field.add",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="mul",contract="field.mul",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "data.domain"() ({ ^entry(%matrix:!M,%left:!V,%right:!V):
   %rows = "data.domain_indices"(%matrix) {axis=0:i64} : (!M)->!data.domain<ui64>
   %columns = "data.domain_indices"(%matrix) {axis=1:i64} : (!M)->!data.domain<ui64>
   %x = "data.domain_elements"(%left) : (!V)->!data.domain<!F>
   %y = "data.domain_elements"(%right) : (!V)->!data.domain<!F>
   %a = "data.domain_zip"(%rows,%x) : (!data.domain<ui64>,!data.domain<!F>)->!data.domain<ui64,!F>
   %b = "data.domain_zip"(%columns,%y) : (!data.domain<ui64>,!data.domain<!F>)->!data.domain<ui64,!F>
   %d = "data.domain_product"(%a,%b) : (!data.domain<ui64,!F>,!data.domain<ui64,!F>)->!data.domain<ui64,!F,ui64,!F>
   "data.domain_yield"(%d) : (!data.domain<ui64,!F,ui64,!F>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!M,!V,!V)->!data.domain<ui64,!F,ui64,!F>} : ()->()
 local.func private @step(%state:!F,%i:ui64,%x:!F,%j:ui64,%y:!F,%matrix:!M,%left:!V,%right:!V)->!F attributes {logical_origin=["step",[]]} {
   %cell = "algebra.exec.matrix_get"(%matrix,%i,%j) {binding=@get,parameters=[],site="get"} : (!M,ui64,ui64)->!F
   %first = "algebra.exec.field_multiply"(%x,%cell) {binding=@mul,parameters=[],site="left"} : (!F,!F)->!F
   %second = "algebra.exec.field_multiply"(%first,%y) {binding=@mul,parameters=[],site="right"} : (!F,!F)->!F
   %next = "algebra.exec.field_add"(%state,%second) {binding=@add,parameters=[],site="add"} : (!F,!F)->!F
   local.return %next : !F
 }
 "local.finite_fold"() {sym_name="fold",function_type=(!M,!V,!V,!F)->!F,domain=@items,step=@step} : ()->()
 local.func @work(%matrix:!M,%left:!V,%right:!V,%init:!F)->!F attributes {logical_origin=["work",[]]} {
   %r = local.apply @fold(%matrix,%left,%right,%init) {site="fold"} : (!M,!V,!V,!F)->!F
   local.return %r : !F
 }
 "protocol.func"() ({ ^entry(%matrix:!M,%left:!V,%right:!V,%init:!F):
   %r = "protocol.local_call"(%matrix,%left,%right,%init) {callee=@work,role="P",site="work"} : (!M,!V,!V,!F)->!F
   "protocol.return"(%r) : (!F)->()
 }) {sym_name="main",function_type=(!M,!V,!V,!F)->!F,roles=["P"],input_roles=[["P"],["P"],["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
