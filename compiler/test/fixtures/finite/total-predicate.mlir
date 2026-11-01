!F = !algebra.field<"bls12-381.fr">
!V = !data.field_vector<"bls12-381.fr">
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
 func.func private @predicate(%x:!F,%xs:!V,%factor:!F)->i1 {
   %ok = algebra.field_equal %x,%factor : (!F,!F)->i1
   func.return %ok : i1
 }
 "protocol.func"() ({ ^entry(%xs:!V,%factor:!F):
   %r = "data.finite_collect"(%xs,%factor) {domain=@items,body=@body,predicate=@predicate} : (!V,!F)->!V
   "protocol.return"(%r) : (!V)->()
 }) {sym_name="main",function_type=(!V,!F)->!V,roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
