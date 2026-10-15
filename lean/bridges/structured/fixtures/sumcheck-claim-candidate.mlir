module {
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "protocol.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, input_roles = [["role00000000"], ["role00000000"], ["role00000000"]], output_roles = [["role00000000"]], roles = ["role00000000"], sym_name = "s14h73756d636865636b5f636c61696d5h436c61696d"}> ({
    ^bb0(%arg0: !algebra.field<"bls12-381.fr">, %arg1: !algebra.field<"bls12-381.fr">, %arg2: !algebra.field<"bls12-381.fr">):
      %0 = algebra.field_multiply %arg2, %arg0 : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %1 = algebra.field_subtract %arg0, %0 : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %2 = algebra.field_multiply %arg2, %arg1 : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %3 = algebra.field_add %1, %2 : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "protocol.return"(%3) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    func.func private @s14h73756d636865636b5f636c61696d5h636c61696d(%arg0: !algebra.field<"bls12-381.fr">, %arg1: !algebra.field<"bls12-381.fr">, %arg2: !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr"> {
      %0 = call @s14h73756d636865636b5f636c61696d8h7765696768746564(%arg0, %arg2) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %1 = algebra.field_subtract %arg0, %0 : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %2 = call @s14h73756d636865636b5f636c61696d8h7765696768746564(%arg1, %arg2) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %3 = algebra.field_add %1, %2 : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      return %3 : !algebra.field<"bls12-381.fr">
    }
    func.func private @s14h73756d636865636b5f636c61696d8h7765696768746564(%arg0: !algebra.field<"bls12-381.fr">, %arg1: !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr"> {
      %0 = algebra.field_multiply %arg1, %arg0 : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      return %0 : !algebra.field<"bls12-381.fr">
    }
  }) : () -> ()
}

