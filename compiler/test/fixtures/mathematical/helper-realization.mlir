!F = !algebra.field<"bls12-381.fr">
!P = !poly.polynomial<"bls12-381.fr", 1>
!A = !algebra.field_array<"bls12-381.fr", 2>
module { "protocol.module"() ({
 func.func private @polynomial(%a:!F,%b:!F,%x:!F)->!F {
   %v = "algebra.array_from_elements"(%a,%b) : (!F,!F)->!A
   %p = "poly.from_coefficients"(%v) : (!A)->!P
   %q = "poly.multiply"(%p,%p) : (!P,!P)->!P
   %r = "poly.evaluate"(%q,%x) : (!P,!F)->!F
   func.return %r : !F
 }
    func.func @work(%arg0: !runtime.scope, %arg1: !F, %arg2: !F, %arg3: !F) -> !exec.outcome<(!F)> attributes {no_inline, runtime.origin = ["work", []]} {
      %0 = "exec.compute"(%arg0, %arg1, %arg2, %arg3) <{callee = @polynomial, site = "evaluate"}> : (!runtime.scope, !F, !F, !F) -> !exec.outcome<(!F)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!F)>) -> ()
    ^bb1(%1: !F):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!F) -> !exec.outcome<(!F)>
      return %2 : !exec.outcome<(!F)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!F)>
      return %4 : !exec.outcome<(!F)>
    }

 "protocol.func"() ({
 ^entry(%a:!F,%b:!F,%x:!F):
   %r = "protocol.local_call"(%a,%b,%x) {callee=@work,role="P",site="work"} : (!F,!F,!F)->!F
   "protocol.return"(%r) : (!F)->()
 }) {sym_name="main",function_type=(!F,!F,!F)->!F,roles=["P"],input_roles=[["P"],["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
