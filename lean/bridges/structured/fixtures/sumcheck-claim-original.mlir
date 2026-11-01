"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "protocol.func"() <{contracts = [], function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, input_roles = [["role00000000"], ["role00000000"], ["role00000000"]], origin = ["sumcheck_claim::Claim", []], output_roles = [["role00000000"]], roles = ["role00000000"], sym_name = "s14h73756d636865636b5f636c61696d5h436c61696d"}> ({
    ^bb0(%arg5: !algebra.field<"bls12-381.fr">, %arg6: !algebra.field<"bls12-381.fr">, %arg7: !algebra.field<"bls12-381.fr">):
      %6 = "func.call"(%arg5, %arg6, %arg7) <{callee = @s14h73756d636865636b5f636c61696d5h636c61696d}> : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "protocol.return"(%6) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "s14h73756d636865636b5f636c61696d5h636c61696d", sym_visibility = "private"}> ({
    ^bb0(%arg2: !algebra.field<"bls12-381.fr">, %arg3: !algebra.field<"bls12-381.fr">, %arg4: !algebra.field<"bls12-381.fr">):
      %1 = "algebra.constant"() <{value = #algebra.literal<<"bls12-381.fr">, 1 : ui255> : !algebra.field<"bls12-381.fr">}> : () -> !algebra.field<"bls12-381.fr">
      %2 = "algebra.field_subtract"(%1, %arg4) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %3 = "func.call"(%arg2, %2) <{callee = @s14h73756d636865636b5f636c61696d8h7765696768746564}> : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %4 = "func.call"(%arg3, %arg4) <{callee = @s14h73756d636865636b5f636c61696d8h7765696768746564}> : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %5 = "algebra.field_add"(%3, %4) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%5) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "s14h73756d636865636b5f636c61696d8h7765696768746564", sym_visibility = "private"}> ({
    ^bb0(%arg0: !algebra.field<"bls12-381.fr">, %arg1: !algebra.field<"bls12-381.fr">):
      %0 = "algebra.field_multiply"(%arg1, %arg0) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%0) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
  }) : () -> ()
}) : () -> ()

