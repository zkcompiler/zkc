!F = !algebra.field<"bls12-381.fr">
!A = !algebra.field_array<"bls12-381.fr", 2>
module { "protocol.module"() ({
  module @first_unit attributes {exec.computation} {
    func.func @evaluate(%a: !F, %b: !F) -> !A {
      %x = algebra.field_subtract %a, %b : (!F, !F) -> !F
      %y = algebra.field_subtract %a, %b : (!F, !F) -> !F
      %p = "algebra.array_from_elements"(%x, %y) : (!F, !F)->!A
      func.return %p : !A
    }
  }
  module @second_unit attributes {exec.computation} {
    func.func @evaluate(%a: !A) -> !F {
      %v = "algebra.array_at"(%a) {index=1:i64} : (!A)->!F
      func.return %v : !F
    }
  }
  local.func @first(%a: !F, %b: !F) -> !A {
    %r = kernel.call @first_unit::@evaluate(%a, %b) {site="first_math"} : (!F, !F)->!A
    local.return %r : !A
  }
  local.func @second(%a: !A) -> !F {
    %r = kernel.call @second_unit::@evaluate(%a) {site="second_math"} : (!A)->!F
    local.return %r : !F
  }
  "protocol.participant"() ({ ^entry(%a: !F, %b: !F):
    %first = local.call @first(%a, %b) {site="first_cut"} : (!F, !F)->!A
    %second = local.call @second(%first) {site="second_cut"} : (!A)->!F
    "protocol.finish"(%second) : (!F)->()
  }) {sym_name="participant", function_type=(!F, !F)->!F, instance="main", role="P"} : ()->()
  "protocol.projection"() {interfaces=[], calculations=[
    {participant=@participant, callee=@first, site="first_cut"},
    {participant=@participant, callee=@second, site="second_cut"}
  ]} : ()->()
}) {profile=#protocol.profile<exec>} : ()->() }
