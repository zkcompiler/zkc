"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "protocol.func"() <{contracts = [], function_type = (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">, !protocol.service_ref<"random.bls12-381.fr/0">) -> i1, input_roles = [["role00000000", "role00000001"], ["role00000000", "role00000001"], ["role00000000"], ["role00000000"], ["role00000001"]], origin = ["schnorr_forms::HelpersProtocol", []], output_roles = [["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "s13h7363686e6f72725f666f726d7315h48656c7065727350726f746f636f6c"}> ({
    ^bb0(%arg8: !algebra.group<"bls12-381.g1">, %arg9: !algebra.group<"bls12-381.g1">, %arg10: !algebra.field<"bls12-381.fr">, %arg11: !protocol.service_ref<"random.bls12-381.fr/0">, %arg12: !protocol.service_ref<"random.bls12-381.fr/0">):
      %6 = "protocol.query"(%arg11) <{method = "draw", owner = "role00000000", site = "s0"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
      %7 = "algebra.group_scale"(%arg8, %6) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %8 = "protocol.exchange"(%7) <{receiver = "role00000001", sender = "role00000000", site = "label_636f6d6d69746d656e74_0"}> : (!algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %9 = "protocol.restrict_roles"(%8) <{roles = ["role00000001"]}> : (!algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %10 = "protocol.query"(%arg12) <{method = "draw", owner = "role00000001", site = "label_6368616c6c656e6765"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
      %11 = "protocol.exchange"(%10) <{receiver = "role00000000", sender = "role00000001", site = "label_64656c6976657279_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %12 = "protocol.restrict_roles"(%11) <{roles = ["role00000000"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %13 = "func.call"(%6, %12, %arg10) <{callee = @s13h7363686e6f72725f666f726d738h726573706f6e7365}> : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %14 = "protocol.exchange"(%13) <{receiver = "role00000001", sender = "role00000000", site = "label_726573706f6e7365_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %15 = "protocol.restrict_roles"(%14) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %16 = "func.call"(%arg8, %arg9, %9, %10, %15) <{callee = @s13h7363686e6f72725f666f726d738h6571756174696f6e}> : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "protocol.return"(%16) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "s13h7363686e6f72725f666f726d738h726573706f6e7365", sym_visibility = "private"}> ({
    ^bb0(%arg5: !algebra.field<"bls12-381.fr">, %arg6: !algebra.field<"bls12-381.fr">, %arg7: !algebra.field<"bls12-381.fr">):
      %4 = "algebra.field_multiply"(%arg6, %arg7) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %5 = "algebra.field_add"(%arg5, %4) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%5) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "s13h7363686e6f72725f666f726d738h6571756174696f6e", sym_visibility = "private"}> ({
    ^bb0(%arg0: !algebra.group<"bls12-381.g1">, %arg1: !algebra.group<"bls12-381.g1">, %arg2: !algebra.group<"bls12-381.g1">, %arg3: !algebra.field<"bls12-381.fr">, %arg4: !algebra.field<"bls12-381.fr">):
      %0 = "algebra.group_scale"(%arg0, %arg4) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %1 = "algebra.group_scale"(%arg1, %arg3) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %2 = "algebra.group_add"(%arg2, %1) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %3 = "algebra.group_equal"(%0, %2) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> i1
      "func.return"(%3) : (i1) -> ()
    }) : () -> ()
  }) : () -> ()
}) : () -> ()

