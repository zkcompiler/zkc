"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "protocol.func"() <{contracts = [], function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, input_roles = [["role00000000"], ["role00000000"], ["role00000000"]], output_roles = [["role00000000"]], roles = ["role00000000"], sym_name = "s16h7363686e6f72725f726573706f6e73658h526573706f6e7365"}> ({
    ^bb0(%arg3: !algebra.field<"bls12-381.fr">, %arg4: !algebra.field<"bls12-381.fr">, %arg5: !algebra.field<"bls12-381.fr">):
      %2 = "func.call"(%arg3, %arg4, %arg5) <{callee = @s16h7363686e6f72725f726573706f6e73658h726573706f6e7365}> : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "protocol.return"(%2) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "s16h7363686e6f72725f726573706f6e73658h726573706f6e7365", sym_visibility = "private"}> ({
    ^bb0(%arg0: !algebra.field<"bls12-381.fr">, %arg1: !algebra.field<"bls12-381.fr">, %arg2: !algebra.field<"bls12-381.fr">):
      %0 = "algebra.field_multiply"(%arg1, %arg2) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %1 = "algebra.field_add"(%arg0, %0) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%1) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
  }) : () -> ()
}) : () -> ()

