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
 func.func private @calculate(%a:!F,%b:!F,%x:!F)->(!F,!F,!F) {
   %work:3 = func.call @mixed(%a,%b) : (!F,!F)->(!F,!P,!F)
   %value = "poly.evaluate"(%work#1,%x) : (!P,!F)->!F
   func.return %work#0,%value,%work#2 : !F,!F,!F
 }
 func.func @realized(%scope:!runtime.scope,%a0:!F,%a1:!F,%a2:!F)->!exec.outcome<(!F,!F,!F)> attributes {no_inline,runtime.origin=["realized",[]]} {
   %call = "exec.compute"(%scope,%a0,%a1,%a2) {callee=@calculate,site="kernel"} : (!runtime.scope,!F,!F,!F)->!exec.outcome<(!F,!F,!F)>
   "exec.dispatch"(%call)[^done,^failed] : (!exec.outcome<(!F,!F,!F)>)->()
 ^done(%r0:!F,%r1:!F,%r2:!F):
   %result = "exec.returned"(%r0,%r1,%r2) : (!F,!F,!F)->!exec.outcome<(!F,!F,!F)>
   func.return %result : !exec.outcome<(!F,!F,!F)>
 ^failed(%stop:!exec.stop):
   %failure = "exec.failed"(%stop) : (!exec.stop)->!exec.outcome<(!F,!F,!F)>
   func.return %failure : !exec.outcome<(!F,!F,!F)>
 }
 "protocol.func"() ({ "protocol.return"() : ()->() })
 {sym_name="main",function_type=()->(),roles=["P"],input_roles=[],output_roles=[]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
