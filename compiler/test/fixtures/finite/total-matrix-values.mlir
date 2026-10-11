!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
!I = !algebra.indices
!M = !algebra.field_matrix<"bls12-381.fr">
module { "protocol.module"() ({
 "data.domain"() ({ ^entry(%matrix:!M):
   %d = "data.domain_matrix_coordinates"(%matrix) {order="row_major"} : (!M)->!data.domain<ui64,ui64>
   "data.domain_yield"(%d) : (!data.domain<ui64,ui64>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!M)->!data.domain<ui64,ui64>} : ()->()
 func.func private @body(%i:ui64,%j:ui64,%matrix:!M)->!F attributes {data.preconditions=[#data.index_bound<0,2,0>,#data.index_bound<1,2,1>]} {
   %v = "data.bounded_matrix_at"(%matrix,%i,%j) : (!M,ui64,ui64)->!F
   func.return %v : !F
 }
 "protocol.func"() ({ ^entry(%matrix:!M):
   %r = "algebra.finite_collect"(%matrix) {domain=@items,body=@body} : (!M)->!V
   "protocol.return"(%r) : (!V)->()
 }) {sym_name="main",function_type=(!M)->!V,roles=["P"],input_roles=[["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
