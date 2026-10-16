!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
 "data.domain"() ({
 ^entry(%xs:!V,%other:!V):
   %d = "data.domain_indices"(%xs) {axis=0:i64} : (!V)->!data.domain<ui64>
   "data.domain_yield"(%d) : (!data.domain<ui64>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V,!V)->!data.domain<ui64>} : ()->()
 func.func private @read(%xs:!V,%i:ui64) -> !F attributes {data.preconditions=[#data.index_bound<1,0,0>]} {
   %v = "data.bounded_at"(%xs,%i) : (!V,ui64)->!F
   func.return %v : !F
 }
 func.func private @step(%a:!F,%i:ui64,%xs:!V,%other:!V) -> !F attributes {data.preconditions=[#data.index_bound<1,2,0>]} {
   %v = func.call @read(%xs,%i) : (!V,ui64)->!F
   %sum = algebra.field_add %a,%v : (!F,!F)->!F
   func.return %sum : !F
 }
 "protocol.func"() ({
 ^entry(%xs:!V,%other:!V,%a:!F):
   %r = "algebra.finite_fold"(%xs,%other,%a) {domain=@items,step=@step} : (!V,!V,!F)->!F
   "protocol.return"(%r) : (!F)->()
 }) {sym_name="main",function_type=(!V,!V,!F)->!F,roles=["P"],input_roles=[["P"],["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
