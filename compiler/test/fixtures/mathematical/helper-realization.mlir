!F = !algebra.field<"bls12-381.fr">
!P = !poly.polynomial<"bls12-381.fr", 1>
!A = tensor<2x!F>
module { "protocol.module"() ({
 func.func private @polynomial(%a:!F,%b:!F,%x:!F)->!F {
   %v = "tensor.from_elements"(%a,%b) : (!F,!F)->!A
   %p = "poly.from_coefficients"(%v) : (!A)->!P
   %q = "poly.multiply"(%p,%p) : (!P,!P)->!P
   %r = "poly.evaluate"(%q,%x) : (!P,!F)->!F
   func.return %r : !F
 }
 local.realize @realized = @polynomial : (!F,!F,!F)->!F
 local.func @work(%a:!F,%b:!F,%x:!F)->!F attributes {logical_origin=["work",[]]} {
   %r = local.apply @realized(%a,%b,%x) {site="evaluate"} : (!F,!F,!F)->!F
   local.return %r : !F
 }
 "protocol.func"() ({
 ^entry(%a:!F,%b:!F,%x:!F):
   %r = "protocol.local_call"(%a,%b,%x) {callee=@work,role="P",site="work"} : (!F,!F,!F)->!F
   "protocol.return"(%r) : (!F)->()
 }) {sym_name="main",function_type=(!F,!F,!F)->!F,roles=["P"],input_roles=[["P"],["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
