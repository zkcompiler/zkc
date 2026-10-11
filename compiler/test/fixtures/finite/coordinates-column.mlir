!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
!I = !algebra.indices
!M = !algebra.field_matrix<"bls12-381.fr">
module { "protocol.module"() ({
 "local.binding"() {sym_name="mul",contract="index.mul",arguments=[],implementation=""} : ()->()
 "local.binding"() {sym_name="add",contract="index.add",arguments=[],implementation=""} : ()->()
 "data.domain"() ({ ^entry(%matrix:!M):
   %d = "data.domain_matrix_coordinates"(%matrix) {order="column_major"} : (!M)->!data.domain<ui64,ui64>
   "data.domain_yield"(%d) : (!data.domain<ui64,ui64>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!M)->!data.domain<ui64,ui64>} : ()->()
 local.func private @body(%i:ui64,%j:ui64,%matrix:!M,%base:ui64) -> ui64 attributes {logical_origin=["body",[]]} {
   %major = "algebra.exec.index_mul"(%i,%base) {binding=@mul,parameters=[],site="major"} : (ui64,ui64)->ui64
   %value = "algebra.exec.index_add"(%major,%j) {binding=@add,parameters=[],site="value"} : (ui64,ui64)->ui64
   local.return %value : ui64
 }
 "local.finite_collect"() {sym_name="collect",function_type=(!M,ui64)->!I,domain=@items,body=@body} : ()->()
 local.func @work(%matrix:!M,%base:ui64) -> !I attributes {logical_origin=["work",[]]} {
   %r = local.apply @collect(%matrix,%base) {site="collect"} : (!M,ui64)->!I
   local.return %r : !I
 }
 "protocol.func"() ({ ^entry(%matrix:!M,%base:ui64):
   %r = "protocol.local_call"(%matrix,%base) {callee=@work,role="P",site="work"} : (!M,ui64)->!I
   "protocol.return"(%r) : (!I)->()
 }) {sym_name="main",function_type=(!M,ui64)->!I,roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
