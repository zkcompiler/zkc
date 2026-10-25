!F = !algebra.field<"bls12-381.fr">
module { "protocol.module"() ({
  module @first_unit attributes {exec.computation} {
    func.func @evaluate(%a: !F, %b: !F, %ok: i1, %other: i1) -> (!F, !F, !F) {
      %g = algebra.field_multiply %a, %b : (!F, !F) -> !F
      %h = algebra.field_multiply %b, %a : (!F, !F) -> !F
      %c0 = algebra.field_subtract %a, %b : (!F, !F) -> !F
      %c1 = algebra.field_subtract %a, %b : (!F, !F) -> !F
      %dead = algebra.field_subtract %a, %b : (!F, !F) -> !F
      %v = algebra.field_add %g, %c0 : (!F, !F) -> !F
      %u = algebra.field_add %h, %c1 : (!F, !F) -> !F
      func.return %v, %u, %c1 : !F, !F, !F
    }
  }
  module @second_unit attributes {exec.computation} {
    func.func @evaluate(%a: !F, %b: !F, %ok: i1, %other: i1) -> (!F, !F, !F) {
      %g = algebra.field_multiply %a, %b : (!F, !F) -> !F
      %identical = algebra.field_multiply %a, %b : (!F, !F) -> !F
      %c0 = algebra.field_subtract %a, %b : (!F, !F) -> !F
      %c1 = algebra.field_subtract %a, %b : (!F, !F) -> !F
      %v = algebra.field_add %g, %c0 : (!F, !F) -> !F
      func.return %v, %c0, %c1 : !F, !F, !F
    }
  }
  local.func @first(%a: !F, %b: !F, %ok: i1, %other: i1) -> (!F, !F, !F) {
    %r:3 = kernel.call @first_unit::@evaluate(%a, %b, %ok, %other) {site="first_math"} : (!F, !F, i1, i1) -> (!F, !F, !F)
    local.guard %ok {site="inner_guard"}
    local.return %r#0, %r#1, %r#2 : !F, !F, !F
  }
  local.func @second(%a: !F, %b: !F, %ok: i1, %other: i1) -> (!F, !F, !F) {
    %r:3 = kernel.call @second_unit::@evaluate(%a, %b, %ok, %other) {site="second_math"} : (!F, !F, i1, i1) -> (!F, !F, !F)
    local.return %r#0, %r#1, %r#2 : !F, !F, !F
  }
  local.func @authored(%a: !F, %b: !F) -> !F {
    %v = algebra.field_subtract %a, %b : (!F, !F) -> !F
    local.return %v : !F
  }
  "protocol.participant"() ({ ^entry(%a: !F, %b: !F, %ok: i1, %other: i1):
    %first:3 = local.call @first(%a, %b, %ok, %other) {site="first_cut"} : (!F, !F, i1, i1) -> (!F, !F, !F)
    local.guard %ok {site="outer_guard"}
    %second:3 = local.call @second(%a, %b, %ok, %other) {site="second_cut"} : (!F, !F, i1, i1) -> (!F, !F, !F)
    "protocol.finish"(%second#0, %second#1, %second#2) : (!F, !F, !F) -> ()
  }) {sym_name="participant", function_type=(!F, !F, i1, i1)->(!F, !F, !F), instance="main", role="P"} : () -> ()
  "protocol.projection"() {interfaces=[], calculations=[
    {participant=@participant, callee=@first, site="first_cut"},
    {participant=@participant, callee=@second, site="second_cut"}
  ]} : () -> ()
}) {profile=#protocol.profile<exec>} : () -> () }
