!F = !algebra.field<"bls12-381.fr">
module {
  "protocol.module"() ({
    func.func private @pair(%a: !F, %b: !F) -> (!F, !F) {
      %sum = algebra.field_add %a, %b : (!F, !F) -> !F
      %difference = algebra.field_subtract %a, %b : (!F, !F) -> !F
      func.return %sum, %difference : !F, !F
    }
    "protocol.func"() ({
    ^entry(%a: !F, %b: !F):
      %first:2 = func.call @pair(%a, %b) : (!F, !F) -> (!F, !F)
      %second:2 = func.call @pair(%first#1, %first#0) : (!F, !F) -> (!F, !F)
      %product = algebra.field_multiply %second#0, %second#1 : (!F, !F) -> !F
      "protocol.return"(%first#0, %first#1, %second#0, %second#1, %product) : (!F, !F, !F, !F, !F) -> ()
    }) {sym_name = "main", function_type = (!F, !F) -> (!F, !F, !F, !F, !F), roles = ["P"], input_roles = [["P"], ["P"]], output_roles = [["P"], ["P"], ["P"], ["P"], ["P"]]} : () -> ()
  }) {profile = #protocol.profile<protocol>} : () -> ()
}
