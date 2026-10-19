!F = !algebra.field<"bls12-381.fr">
!P = !poly.polynomial<"bls12-381.fr", 1>
!A = !algebra.field_array<"bls12-381.fr", 2>
module { "protocol.module"() ({
 func.func private @mixed(%a:!F,%b:!F)->(!F,!P,!F) {
   %difference = algebra.field_subtract %a,%b : (!F,!F)->!F
   %values = "algebra.array_from_elements"(%difference,%b) : (!F,!F)->!A
   %p = "poly.interpolate"(%values) {points=["0","1"]} : (!A)->!P
   %product = algebra.field_multiply %difference,%b : (!F,!F)->!F
   func.return %product,%p,%difference : !F,!P,!F
 }
 func.func private @calculate(%a:!F,%b:!F,%x:!F)->(!F,!F,!F) {
   %work:3 = func.call @mixed(%a,%b) : (!F,!F)->(!F,!P,!F)
   %value = "poly.evaluate"(%work#1,%x) : (!P,!F)->!F
   func.return %work#0,%value,%work#2 : !F,!F,!F
 }
 local.realize @realized = @calculate : (!F,!F,!F)->(!F,!F,!F)
 "protocol.func"() ({ "protocol.return"() : ()->() })
 {sym_name="main",function_type=()->(),roles=["P"],input_roles=[],output_roles=[]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
