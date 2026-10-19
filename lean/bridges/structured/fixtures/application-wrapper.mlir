"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "protocol.func"() <{contracts = [], function_type = (i1, !protocol.service_ref<"random.bls12-381.fr/0">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), input_roles = [["role00000001"], ["role00000001"], ["role00000001"]], output_roles = [["role00000000"], ["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "s6h73616d706c655h4f75746572"}> ({
    ^bb0(%arg5: i1, %arg6: !protocol.service_ref<"random.bls12-381.fr/0">, %arg7: !protocol.service_ref<"random.bls12-381.fr/0">):
      %11:2 = "protocol.apply"(%arg5, %arg6, %arg7) <{callee = @s6h73616d706c653h52756e, roles = ["role00000000", "role00000001"], site = "s0"}> : (i1, !protocol.service_ref<"random.bls12-381.fr/0">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      "protocol.return"(%11#0, %11#1) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "protocol.func"() <{contracts = [], function_type = (i1, !protocol.service_ref<"random.bls12-381.fr/0">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), input_roles = [["role00000001"], ["role00000001"], ["role00000001"]], output_roles = [["role00000000"], ["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "s6h73616d706c653h52756e"}> ({
    ^bb0(%arg2: i1, %arg3: !protocol.service_ref<"random.bls12-381.fr/0">, %arg4: !protocol.service_ref<"random.bls12-381.fr/0">):
      %6 = "protocol.query"(%arg3) <{method = "draw", owner = "role00000001", site = "s0"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
      "protocol.guard"(%arg2) <{owner = "role00000001", site = "s2"}> : (i1) -> ()
      %7:2 = "protocol.apply"(%arg3, %arg4) <{callee = @s6h73616d706c654h44726177, roles = ["role00000000", "role00000001"], site = "s3"}> : (!protocol.service_ref<"random.bls12-381.fr/0">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %8 = "protocol.query"(%arg3) <{method = "draw", owner = "role00000001", site = "s6"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
      %9 = "algebra.field_add"(%6, %7#1) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %10 = "algebra.field_add"(%9, %8) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "protocol.return"(%7#0, %10) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "protocol.func"() <{contracts = [], function_type = (!protocol.service_ref<"random.bls12-381.fr/0">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), input_roles = [["role00000001"], ["role00000001"]], output_roles = [["role00000000"], ["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "s6h73616d706c654h44726177"}> ({
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

