!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
 "data.domain"() ({ ^entry(%xs:!V):
   %d = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
   "data.domain_yield"(%d) : (!data.domain<!F>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
 func.func private @body(%x:!F,%xs:!V,%factor:!F) -> !F {
   %y = algebra.field_multiply %x,%factor : (!F,!F)->!F
   %z = algebra.field_add %y,%factor : (!F,!F)->!F
   func.return %z : !F
 }
 "protocol.func"() ({ ^entry(%xs:!V,%factor:!F):
   %r = "algebra.finite_collect"(%xs,%factor) {domain=@items,body=@body} : (!V,!F)->!V
   "protocol.return"(%r) : (!V)->()
 }) {sym_name="main",function_type=(!V,!F)->!V,roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
