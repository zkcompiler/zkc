!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
!I = !algebra.indices
!M = !algebra.field_matrix<"bls12-381.fr">
module { "protocol.module"() ({
 "local.binding"() {sym_name="get",contract="matrix.get",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "data.domain"() ({ ^entry(%matrix:!M):
   %d = "data.domain_matrix_coordinates"(%matrix) {order="row_major"} : (!M)->!data.domain<ui64,ui64>
   "data.domain_yield"(%d) : (!data.domain<ui64,ui64>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!M)->!data.domain<ui64,ui64>} : ()->()
 local.func private @body(%i:ui64,%j:ui64,%matrix:!M) -> !F attributes {logical_origin=["body",[]]} {
   %value = "algebra.exec.matrix_get"(%matrix,%i,%j) {binding=@get,parameters=[],site="get"} : (!M,ui64,ui64)->!F
   local.return %value : !F
 }
 "local.finite_collect"() {sym_name="collect",function_type=(!M)->!V,domain=@items,body=@body} : ()->()
 local.func @work(%matrix:!M) -> !V attributes {logical_origin=["work",[]]} {
   %r = local.apply @collect(%matrix) {site="collect"} : (!M)->!V
   local.return %r : !V
 }
 "protocol.func"() ({ ^entry(%matrix:!M):
   %r = "protocol.local_call"(%matrix) {callee=@work,role="P",site="work"} : (!M)->!V
   "protocol.return"(%r) : (!V)->()
 }) {sym_name="main",function_type=(!M)->!V,roles=["P"],input_roles=[["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
