!F = !algebra.field<"bls12-381.fr">
!A = !algebra.field_array<"bls12-381.fr", 2>
module { "protocol.module"() ({
  module @first_unit attributes {exec.computation} {
    func.func @evaluate(%a: !F, %b: !F) -> (!A, !F) {
      %x = algebra.field_subtract %a, %b : (!F, !F) -> !F
      %y = algebra.field_subtract %a, %b : (!F, !F) -> !F
      %p = "algebra.array_from_elements"(%x, %y) : (!F, !F)->!A
      func.return %p, %y : !A, !F
    }
  }
  module @second_unit attributes {exec.computation} {
    func.func @evaluate(%a: !A, %element: !F) -> !F {
      func.return %element : !F
    }
  }
  local.func @first(%a: !F, %b: !F) -> (!A, !F) {
    %r:2 = kernel.call @first_unit::@evaluate(%a, %b) {site="first_math"} : (!F, !F)->(!A, !F)
    local.return %r#0, %r#1 : !A, !F
  }
  local.func @second(%a: !A, %element: !F) -> !F {
    %r = kernel.call @second_unit::@evaluate(%a, %element) {site="second_math"} : (!A, !F)->!F
    local.return %r : !F
  }
  "protocol.participant"() ({ ^entry(%a: !F, %b: !F):
    %first:2 = local.call @first(%a, %b) {site="first_cut"} : (!F, !F)->(!A, !F)
    %second = local.call @second(%first#0, %first#1) {site="second_cut"} : (!A, !F)->!F
    "protocol.finish"(%second) : (!F)->()
  }) {sym_name="participant", function_type=(!F, !F)->!F, instance="main", role="P"} : ()->()
  "protocol.projection"() {interfaces=[], calculations=[
    {participant=@participant, callee=@first, site="first_cut"},
    {participant=@participant, callee=@second, site="second_cut"}
  ]} : ()->()
}) {profile=#protocol.profile<exec>} : ()->() }
