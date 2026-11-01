!F = !algebra.field<"bls12-381.fr">
!A = !data.field_array<"bls12-381.fr", 2>
module { "protocol.module"() ({
  module @first_unit attributes {exec.computation} {
    func.func @evaluate(%a: !F, %b: !F) -> (!A, !F) {
      %x = algebra.field_subtract %a, %b : (!F, !F) -> !F
      %y = algebra.field_subtract %a, %b : (!F, !F) -> !F
      %p = "data.array_from_elements"(%x, %y) : (!F, !F)->!A
      func.return %p, %y : !A, !F
    }
  }
  module @second_unit attributes {exec.computation} {
    func.func @evaluate(%a: !A, %element: !F) -> !F {
      func.return %element : !F
    }
  }
  func.func @first(%scope: !runtime.scope, %a: !F, %b: !F) -> !exec.outcome<(!A, !F)> attributes {no_inline, runtime.origin=["first", []]} {
    %r = "exec.compute"(%scope, %a, %b) {callee=@first_unit::@evaluate, site="first_math"} : (!runtime.scope, !F, !F) -> !exec.outcome<(!A, !F)>
    "exec.dispatch"(%r)[^success, ^failure] : (!exec.outcome<(!A, !F)>) -> ()
  ^success(%v0: !A, %v1: !F):
    %returned = "exec.returned"(%v0, %v1) : (!A, !F) -> !exec.outcome<(!A, !F)>
    return %returned : !exec.outcome<(!A, !F)>
  ^failure(%stopped: !exec.stop):
    %failed = "exec.failed"(%stopped) : (!exec.stop) -> !exec.outcome<(!A, !F)>
    return %failed : !exec.outcome<(!A, !F)>
  }
  func.func @second(%scope: !runtime.scope, %a: !A, %element: !F) -> !exec.outcome<(!F)> attributes {no_inline, runtime.origin=["second", []]} {
    %r = "exec.compute"(%scope, %a, %element) {callee=@second_unit::@evaluate, site="second_math"} : (!runtime.scope, !A, !F) -> !exec.outcome<(!F)>
    "exec.dispatch"(%r)[^success, ^failure] : (!exec.outcome<(!F)>) -> ()
  ^success(%v0: !F):
    %returned = "exec.returned"(%v0) : (!F) -> !exec.outcome<(!F)>
    return %returned : !exec.outcome<(!F)>
  ^failure(%stopped: !exec.stop):
    %failed = "exec.failed"(%stopped) : (!exec.stop) -> !exec.outcome<(!F)>
    return %failed : !exec.outcome<(!F)>
  }
  "protocol.participant"() ({ ^entry(%a: !F, %b: !F):
    %first:2 = "protocol.local_call"(%a, %b) {callee=@first, site="first_cut", role="P"} : (!F, !F) -> (!A, !F)
    %second = "protocol.local_call"(%first#0, %first#1) {callee=@second, site="second_cut", role="P"} : (!A, !F) -> !F
    "protocol.finish"(%second) : (!F)->()
  }) {sym_name="participant", function_type=(!F, !F)->!F, instance="main", role="P"} : ()->()
  "protocol.projection"() {interfaces=[], calculations=[
    {participant=@participant, callee=@first, site="first_cut"},
    {participant=@participant, callee=@second, site="second_cut"}
  ]} : ()->()
}) {profile=#protocol.profile<exec>} : ()->() }
