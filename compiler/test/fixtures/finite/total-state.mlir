!F = !algebra.field<"bls12-381.fr">
!V = !data.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
 "data.domain"() ({
 ^entry(%xs:!V):
   %d = "data.domain_indices"(%xs) {axis=0:i64} : (!V) -> !data.domain<ui64>
   "data.domain_yield"(%d) : (!data.domain<ui64>) -> ()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<ui64>} : ()->()
 func.func private @step(%a:!F,%b:!F,%i:ui64,%xs:!V) -> (!F,!F) attributes {data.preconditions=[#data.index_bound<2,3,0>]} {
   %v = "data.bounded_at"(%xs,%i) : (!V,ui64)->!F
   func.return %b,%v : !F,!F
 }
 "protocol.func"() ({
 ^entry(%xs:!V,%a:!F,%b:!F):
   %r:2 = "data.finite_fold"(%xs,%a,%b) {domain=@items,step=@step} : (!V,!F,!F)->(!F,!F)
   "protocol.return"(%r#0,%r#1) : (!F,!F)->()
 }) {sym_name="main",origin=["main",[]],function_type=(!V,!F,!F)->(!F,!F),roles=["P"],input_roles=[["P"],["P"],["P"]],output_roles=[["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
