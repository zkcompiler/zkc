"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "algebra.map_realize"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">, helper = @s12h6d61705f6578616d706c65736h6c696e656172, rowwise = array<i1: false, true, false, true, true, false>, sym_name = "zkl_map_69915d69b63fed11da18dc3f9faf1a502e85fc5b9d1dbc28c8d156b3a27304b2"}> : () -> ()
    "protocol.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">, input_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"]], output_roles = [["role00000000"]], roles = ["role00000000", "role00000001"], sym_name = "s12h6d61705f6578616d706c657317h4c696e656172436f6d62696e6174696f6e"}> ({
    ^bb0(%arg14: !algebra.field<"bls12-381.fr">, %arg15: !algebra.field_vector<"bls12-381.fr">, %arg16: !algebra.field<"bls12-381.fr">, %arg17: !algebra.field_vector<"bls12-381.fr">, %arg18: !algebra.field_vector<"bls12-381.fr">, %arg19: !algebra.field<"bls12-381.fr">):
      %7 = "protocol.local_call"(%arg14, %arg15, %arg16, %arg17, %arg18, %arg19) <{callee = @s12h6d61705f6578616d706c657311h636f6d62696e6174696f6e, role = "role00000000", site = "s0"}> : (!algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
      "protocol.return"(%7) : (!algebra.field_vector<"bls12-381.fr">) -> ()
    }) : () -> ()
    "local.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">, sym_name = "s12h6d61705f6578616d706c657311h636f6d62696e6174696f6e"}> ({
    ^bb0(%arg8: !algebra.field<"bls12-381.fr">, %arg9: !algebra.field_vector<"bls12-381.fr">, %arg10: !algebra.field<"bls12-381.fr">, %arg11: !algebra.field_vector<"bls12-381.fr">, %arg12: !algebra.field_vector<"bls12-381.fr">, %arg13: !algebra.field<"bls12-381.fr">):
      %6 = "local.apply"(%arg8, %arg9, %arg10, %arg11, %arg12, %arg13) <{callee = @zkl_map_69915d69b63fed11da18dc3f9faf1a502e85fc5b9d1dbc28c8d156b3a27304b2, site = "s0"}> : (!algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
      "local.return"(%6) : (!algebra.field_vector<"bls12-381.fr">) -> ()
    }) {logical_origin = ["s12h6d61705f6578616d706c657311h636f6d62696e6174696f6e", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "s12h6d61705f6578616d706c65736h6c696e656172", sym_visibility = "private"}> ({
    ^bb0(%arg2: !algebra.field<"bls12-381.fr">, %arg3: !algebra.field<"bls12-381.fr">, %arg4: !algebra.field<"bls12-381.fr">, %arg5: !algebra.field<"bls12-381.fr">, %arg6: !algebra.field<"bls12-381.fr">, %arg7: !algebra.field<"bls12-381.fr">):
      %1 = "func.call"(%arg2, %arg3) <{callee = @s12h6d61705f6578616d706c65735h7363616c65}> : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %2 = "func.call"(%arg4, %arg5) <{callee = @s12h6d61705f6578616d706c65735h7363616c65}> : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %3 = "algebra.field_subtract"(%1, %2) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %4 = "algebra.constant"() <{value = "3"}> : () -> !algebra.field<"bls12-381.fr">
      %5 = "algebra.field_add"(%3, %4) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%5) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "s12h6d61705f6578616d706c65735h7363616c65", sym_visibility = "private"}> ({
    ^bb0(%arg0: !algebra.field<"bls12-381.fr">, %arg1: !algebra.field<"bls12-381.fr">):
      %0 = "algebra.field_multiply"(%arg0, %arg1) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%0) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
  }) : () -> ()
}) : () -> ()

