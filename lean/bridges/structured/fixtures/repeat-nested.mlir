"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "protocol.func"() <{function_type = (ui64, ui64, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, input_roles = [["role00000000"], ["role00000000"], ["role00000000"]], output_roles = [["role00000000"]], roles = ["role00000000"], sym_name = "s6h73616d706c653h52756e"}> ({
    ^bb0(%arg0: ui64, %arg1: ui64, %arg2: !algebra.field<"bls12-381.fr">):
      %0 = "protocol.repeat"(%arg0, %arg2, %arg1, %arg2) <{carried = 1 : i64, carried_roles = [["role00000000"]], maximum = 3 : i64, roles = ["role00000000"], site = "s3"}> ({
      ^bb0(%arg3: ui64, %arg4: !algebra.field<"bls12-381.fr">, %arg5: ui64, %arg6: !algebra.field<"bls12-381.fr">):
        %1 = "protocol.repeat"(%arg5, %arg4, %arg6) <{carried = 1 : i64, carried_roles = [["role00000000"]], maximum = 2 : i64, roles = ["role00000000"], site = "s5"}> ({
        ^bb0(%arg7: ui64, %arg8: !algebra.field<"bls12-381.fr">, %arg9: !algebra.field<"bls12-381.fr">):
          %2 = "algebra.field_add"(%arg8, %arg9) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
          "protocol.yield"(%2) : (!algebra.field<"bls12-381.fr">) -> ()
        }) : (ui64, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        "protocol.yield"(%1) : (!algebra.field<"bls12-381.fr">) -> ()
      }) : (ui64, !algebra.field<"bls12-381.fr">, ui64, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "protocol.return"(%0) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
  }) : () -> ()
}) : () -> ()

