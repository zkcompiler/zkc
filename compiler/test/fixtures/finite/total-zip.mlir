!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
 "data.domain"() ({ ^entry(%xs:!V,%ys:!V):
   %x = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
   %y = "data.domain_elements"(%ys) : (!V)->!data.domain<!F>
   %d = "data.domain_zip"(%x,%y) : (!data.domain<!F>,!data.domain<!F>)->!data.domain<!F,!F>
   "data.domain_yield"(%d) : (!data.domain<!F,!F>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V,!V)->!data.domain<!F,!F>} : ()->()
 func.func private @body(%x:!F,%y:!F,%xs:!V,%ys:!V,%factor:!F) -> !F {
   %product = algebra.field_multiply %x,%y : (!F,!F)->!F
   %z = algebra.field_add %product,%factor : (!F,!F)->!F
   func.return %z : !F
 }
 "protocol.func"() ({ ^entry(%xs:!V,%factor:!F):
   %r = "algebra.finite_collect"(%xs,%xs,%factor) {domain=@items,body=@body} : (!V,!V,!F)->!V
   "protocol.return"(%r) : (!V)->()
 }) {sym_name="main",function_type=(!V,!F)->!V,roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
