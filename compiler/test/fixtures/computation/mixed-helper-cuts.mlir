!F = !algebra.field<"bls12-381.fr">
!P = !poly.polynomial<"bls12-381.fr", 1>
!A = !data.field_array<"bls12-381.fr", 2>
module { "protocol.module"() ({
 func.func private @mixed(%a:!F,%b:!F)->(!F,!P,!F) {
   %difference = algebra.field_subtract %a,%b : (!F,!F)->!F
   %values = "data.array_from_elements"(%difference,%b) : (!F,!F)->!A
   %p = "poly.interpolate"(%values) {points=[#algebra.literal<!algebra.field<"bls12-381.fr">, 0 : ui255>,#algebra.literal<!algebra.field<"bls12-381.fr">, 1 : ui255>]} : (!A)->!P
   %product = algebra.field_multiply %difference,%b : (!F,!F)->!F
   func.return %product,%p,%difference : !F,!P,!F
 }
 "protocol.func"() ({ ^entry(%a:!F,%b:!F,%x:!F,%y:!F):
   %work:3 = func.call @mixed(%a,%b) : (!F,!F)->(!F,!P,!F)
   %condition = algebra.field_equal %work#0,%a : (!F,!F)->i1
   protocol.guard %condition {site="checkpoint",owner="P"}
   %first = "poly.evaluate"(%work#1,%x) : (!P,!F)->!F
   %second = "poly.evaluate"(%work#1,%y) : (!P,!F)->!F
   "protocol.return"(%work#2,%first,%second) : (!F,!F,!F)->()
 }) {sym_name="main",function_type=(!F,!F,!F,!F)->(!F,!F,!F),roles=["P"],input_roles=[["P"],["P"],["P"],["P"]],output_roles=[["P"],["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
