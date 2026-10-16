"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "algebra.map_realize"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">, helper = @s12h6d61705f6578616d706c65738h636f6e7374616e74, rowwise = array<i1: true, true, false>, sym_name = "zkl_map_d0cef3b4f0130cd7cc48739618179807e7defff3083f46ef2a798ffc1b23ce96"}> : () -> ()
    "protocol.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">, input_roles = [["role00000000"], ["role00000000"], ["role00000000"]], output_roles = [["role00000000"]], roles = ["role00000000", "role00000001"], sym_name = "s12h6d61705f6578616d706c657312h436f6e7374616e74526f7773"}> ({
    ^bb0(%arg6: !algebra.field_vector<"bls12-381.fr">, %arg7: !algebra.field_vector<"bls12-381.fr">, %arg8: !algebra.field<"bls12-381.fr">):
      %2 = "protocol.local_call"(%arg6, %arg7, %arg8) <{callee = @s12h6d61705f6578616d706c657313h636f6e7374616e745f726f7773, role = "role00000000", site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
      "protocol.return"(%2) : (!algebra.field_vector<"bls12-381.fr">) -> ()
    }) : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">, sym_name = "s12h6d61705f6578616d706c657313h636f6e7374616e745f726f7773"}> ({
    ^bb0(%arg3: !algebra.field_vector<"bls12-381.fr">, %arg4: !algebra.field_vector<"bls12-381.fr">, %arg5: !algebra.field<"bls12-381.fr">):
      %1 = "local.apply"(%arg3, %arg4, %arg5) <{callee = @zkl_map_d0cef3b4f0130cd7cc48739618179807e7defff3083f46ef2a798ffc1b23ce96, site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
      "local.return"(%1) : (!algebra.field_vector<"bls12-381.fr">) -> ()
    }) {logical_origin = ["s12h6d61705f6578616d706c657313h636f6e7374616e745f726f7773", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "s12h6d61705f6578616d706c65738h636f6e7374616e74", sym_visibility = "private"}> ({
    ^bb0(%arg0: !algebra.field<"bls12-381.fr">, %arg1: !algebra.field<"bls12-381.fr">, %arg2: !algebra.field<"bls12-381.fr">):
      %0 = "algebra.constant"() <{value = "7"}> : () -> !algebra.field<"bls12-381.fr">
      "func.return"(%0) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
  }) : () -> ()
}) : () -> ()

