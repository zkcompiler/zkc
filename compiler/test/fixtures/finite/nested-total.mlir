!F = !algebra.field<"bls12-381.fr">
!V = !data.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
 "data.domain"() ({ ^entry(%xs:!V):
   %d = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
   "data.domain_yield"(%d) : (!data.domain<!F>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
 func.func private @inside(%s:!F,%x:!F,%xs:!V) -> !F {
   %r = algebra.field_add %s,%x : (!F,!F)->!F
   func.return %r : !F
 }
 func.func private @outside(%s:!F,%x:!F,%xs:!V) -> !F {
   %r = "data.finite_fold"(%xs,%s) {domain=@items,step=@inside} : (!V,!F)->!F
   func.return %r : !F
 }
 "protocol.func"() ({ ^entry(%xs:!V,%init:!F):
   %r = "data.finite_fold"(%xs,%init) {domain=@items,step=@outside} : (!V,!F)->!F
   "protocol.return"(%r) : (!F)->()
 }) {sym_name="main",function_type=(!V,!F)->!F,roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
