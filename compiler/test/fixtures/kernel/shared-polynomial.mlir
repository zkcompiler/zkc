!F = !algebra.field<"bls12-381.fr">
!P = !poly.polynomial<"bls12-381.fr", 1>
!A = !algebra.field_array<"bls12-381.fr", 2>
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%a:!F,%b:!F,%x:!F,%y:!F):
   %difference = algebra.field_subtract %a,%b : (!F,!F)->!F
   %values = "algebra.array_from_elements"(%difference,%b) : (!F,!F)->!A
   %p = "poly.interpolate"(%values) {points=["0","1"]} : (!A)->!P
   %first = "poly.evaluate"(%p,%x) : (!P,!F)->!F
   %condition = algebra.field_equal %first,%a : (!F,!F)->i1
   protocol.guard %condition {site="checkpoint",owner="P"}
   %second = "poly.evaluate"(%p,%y) : (!P,!F)->!F
   "protocol.return"(%first,%second) : (!F,!F)->()
 }) {sym_name="main",function_type=(!F,!F,!F,!F)->(!F,!F),roles=["P"],input_roles=[["P"],["P"],["P"],["P"]],output_roles=[["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
