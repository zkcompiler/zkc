!F = !algebra.field<"bls12-381.fr">
!A = !data.field_array<"bls12-381.fr", 2>
module { "protocol.module"() ({
  module @first_unit attributes {exec.computation} {
    func.func @evaluate(%a: !F, %b: !F) -> !A {
      %x = algebra.field_subtract %a, %b : (!F, !F) -> !F
      %y = algebra.field_subtract %a, %b : (!F, !F) -> !F
      %p = "data.array_from_elements"(%x, %y) : (!F, !F)->!A
      func.return %p : !A
    }
  }
  module @second_unit attributes {exec.computation} {
    func.func @evaluate(%a: !A) -> !F {
      %v = "data.array_at"(%a) {index=1:i64} : (!A)->!F
      func.return %v : !F
    }
  }
  func.func @first(%scope: !runtime.scope, %a: !F, %b: !F) -> !exec.outcome<(!A)> attributes {no_inline, runtime.origin=["first", []]} {
    %r = "exec.compute"(%scope, %a, %b) {callee=@first_unit::@evaluate, site="first_math"} : (!runtime.scope, !F, !F) -> !exec.outcome<(!A)>
    "exec.dispatch"(%r)[^success, ^failure] : (!exec.outcome<(!A)>) -> ()
  ^success(%v0: !A):
    %returned = "exec.returned"(%v0) : (!A) -> !exec.outcome<(!A)>
    return %returned : !exec.outcome<(!A)>
  ^failure(%stopped: !exec.stop):
    %failed = "exec.failed"(%stopped) : (!exec.stop) -> !exec.outcome<(!A)>
    return %failed : !exec.outcome<(!A)>
  }
  func.func @second(%scope: !runtime.scope, %a: !A) -> !exec.outcome<(!F)> attributes {no_inline, runtime.origin=["second", []]} {
    %r = "exec.compute"(%scope, %a) {callee=@second_unit::@evaluate, site="second_math"} : (!runtime.scope, !A) -> !exec.outcome<(!F)>
    "exec.dispatch"(%r)[^success, ^failure] : (!exec.outcome<(!F)>) -> ()
  ^success(%v0: !F):
    %returned = "exec.returned"(%v0) : (!F) -> !exec.outcome<(!F)>
    return %returned : !exec.outcome<(!F)>
  ^failure(%stopped: !exec.stop):
    %failed = "exec.failed"(%stopped) : (!exec.stop) -> !exec.outcome<(!F)>
    return %failed : !exec.outcome<(!F)>
  }
  "protocol.participant"() ({ ^entry(%a: !F, %b: !F):
    %first = "protocol.local_call"(%a, %b) {callee=@first, site="first_cut", role="P"} : (!F, !F) -> !A
    %second = "protocol.local_call"(%first) {callee=@second, site="second_cut", role="P"} : (!A) -> !F
    "protocol.finish"(%second) : (!F)->()
  }) {sym_name="participant", function_type=(!F, !F)->!F, instance="main", role="P"} : ()->()
  "protocol.projection"() {interfaces=[], calculations=[
    {participant=@participant, callee=@first, site="first_cut"},
    {participant=@participant, callee=@second, site="second_cut"}
  ]} : ()->()
}) {profile=#protocol.profile<exec>} : ()->() }
