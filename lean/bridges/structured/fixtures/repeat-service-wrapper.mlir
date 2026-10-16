"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "protocol.func"() <{function_type = (ui64, !algebra.field<"bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), input_roles = [["role00000000", "role00000002"], ["role00000001"], ["role00000000"], ["role00000000"]], output_roles = [["role00000000"], ["role00000001"], ["role00000002"]], roles = ["role00000000", "role00000001", "role00000002"], sym_name = "s6h73616d706c655h4f75746572"}> ({
    ^bb0(%arg10: ui64, %arg11: !algebra.field<"bls12-381.fr">, %arg12: !protocol.service_ref<"random.bls12-381.fr/0">, %arg13: !protocol.service_ref<"random.bls12-381.fr/0">):
      %15:2 = "protocol.apply"(%arg10, %arg12, %arg13) <{callee = @s6h73616d706c653h52756e, roles = ["role00000002", "role00000000"], site = "s0"}> : (ui64, !protocol.service_ref<"random.bls12-381.fr/0">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      "protocol.return"(%15#1, %arg11, %15#0) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "protocol.func"() <{function_type = (ui64, !protocol.service_ref<"random.bls12-381.fr/0">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), input_roles = [["role00000000", "role00000001"], ["role00000001"], ["role00000001"]], output_roles = [["role00000000"], ["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "s6h73616d706c653h52756e"}> ({
    ^bb0(%arg2: ui64, %arg3: !protocol.service_ref<"random.bls12-381.fr/0">, %arg4: !protocol.service_ref<"random.bls12-381.fr/0">):
      %6 = "protocol.query"(%arg3) <{method = "draw", owner = "role00000001", site = "s0"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
      %7 = "algebra.constant"() <{value = "0"}> : () -> !algebra.field<"bls12-381.fr">
      %8 = "protocol.restrict_roles"(%7) <{roles = ["role00000000"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %9:2 = "protocol.repeat"(%arg2, %8, %6, %arg3, %arg4) <{carried = 2 : i64, carried_roles = [["role00000000"], ["role00000001"]], maximum = 3 : i64, roles = ["role00000000", "role00000001"], site = "s6"}> ({
      ^bb0(%arg5: ui64, %arg6: !algebra.field<"bls12-381.fr">, %arg7: !algebra.field<"bls12-381.fr">, %arg8: !protocol.service_ref<"random.bls12-381.fr/0">, %arg9: !protocol.service_ref<"random.bls12-381.fr/0">):
        %12:2 = "protocol.apply"(%arg8, %arg9) <{callee = @s6h73616d706c654h44726177, roles = ["role00000000", "role00000001"], site = "s7"}> : (!protocol.service_ref<"random.bls12-381.fr/0">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %13 = "algebra.field_add"(%arg6, %12#0) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %14 = "algebra.field_add"(%arg7, %12#1) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        "protocol.yield"(%13, %14) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
      }) : (ui64, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %10 = "protocol.query"(%arg3) <{method = "draw", owner = "role00000001", site = "s16"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
      %11 = "algebra.field_add"(%9#1, %10) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "protocol.return"(%9#0, %11) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "protocol.func"() <{function_type = (!protocol.service_ref<"random.bls12-381.fr/0">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), input_roles = [["role00000001"], ["role00000001"]], output_roles = [["role00000000"], ["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "s6h73616d706c654h44726177"}> ({
    ^bb0(%arg0: !protocol.service_ref<"random.bls12-381.fr/0">, %arg1: !protocol.service_ref<"random.bls12-381.fr/0">):
      %0 = "protocol.query"(%arg0) <{method = "draw", owner = "role00000001", site = "s0"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
      %1 = "protocol.query"(%arg1) <{method = "draw", owner = "role00000001", site = "s2"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
      %2 = "algebra.field_add"(%0, %1) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %3 = "protocol.exchange"(%2) <{receiver = "role00000000", sender = "role00000001", site = "s5_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %4 = "protocol.restrict_roles"(%3) <{roles = ["role00000000"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %5 = "algebra.field_add"(%0, %1) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "protocol.return"(%4, %5) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
  }) : () -> ()
}) : () -> ()

