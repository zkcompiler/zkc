"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "protocol.func"() <{contracts = [], function_type = (ui64, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, i1, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), input_roles = [["role00000000", "role00000001"], ["role00000000"], ["role00000001"], ["role00000001"], ["role00000001"]], output_roles = [["role00000000"], ["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_815724e04d3a27336a925a984d17bdc75b5a2cab63258eba5e870621d2b4b2fe"}> ({
    ^bb0(%arg3: ui64, %arg4: !algebra.field<"bls12-381.fr">, %arg5: !algebra.field<"bls12-381.fr">, %arg6: i1, %arg7: !protocol.service_ref<"random.bls12-381.fr/0">):
      %5:2 = "protocol.repeat"(%arg3, %arg4, %arg5, %arg6, %arg7) <{carried = 2 : i64, carried_roles = [["role00000000"], ["role00000001"]], maximum = 4 : i64, roles = ["role00000000", "role00000001"], site = "s3"}> ({
      ^bb0(%arg8: ui64, %arg9: !algebra.field<"bls12-381.fr">, %arg10: !algebra.field<"bls12-381.fr">, %arg11: i1, %arg12: !protocol.service_ref<"random.bls12-381.fr/0">):
        "protocol.guard"(%arg11) <{owner = "role00000001", site = "s4"}> : (i1) -> ()
        %6:2 = "protocol.apply"(%arg9, %arg10, %arg12) <{callee = @zkl_477249e6aab42d11d39ecc6a67e0e99b7107d8f3e8f0d2bdcdad9431e8bc18b4, roles = ["role00000000", "role00000001"], site = "s5"}> : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        "protocol.yield"(%6#0, %6#1) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
      }) : (ui64, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, i1, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      "protocol.return"(%5#0, %5#1) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "protocol.func"() <{contracts = [], function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), input_roles = [["role00000000"], ["role00000001"], ["role00000001"]], output_roles = [["role00000000"], ["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_477249e6aab42d11d39ecc6a67e0e99b7107d8f3e8f0d2bdcdad9431e8bc18b4"}> ({
    ^bb0(%arg0: !algebra.field<"bls12-381.fr">, %arg1: !algebra.field<"bls12-381.fr">, %arg2: !protocol.service_ref<"random.bls12-381.fr/0">):
      %0 = "protocol.query"(%arg2) <{method = "draw", owner = "role00000001", site = "s0"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
      %1 = "protocol.exchange"(%0) <{receiver = "role00000000", sender = "role00000001", site = "s2_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %2 = "protocol.restrict_roles"(%1) <{roles = ["role00000000"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %3 = "algebra.field_add"(%arg0, %2) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %4 = "algebra.field_add"(%arg1, %0) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "protocol.return"(%3, %4) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
  }) : () -> ()
}) : () -> ()

