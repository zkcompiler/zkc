"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "protocol.func"() <{function_type = (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">, !protocol.service_ref<"random.bls12-381.fr/0">) -> i1, input_roles = [["role00000000", "role00000001"], ["role00000000", "role00000001"], ["role00000000"], ["role00000000"], ["role00000001"]], output_roles = [["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "s13h7363686e6f72725f666f726d7317h52656f72646572656450726f746f636f6c"}> ({
    ^bb0(%arg0: !algebra.group<"bls12-381.g1">, %arg1: !algebra.group<"bls12-381.g1">, %arg2: !algebra.field<"bls12-381.fr">, %arg3: !protocol.service_ref<"random.bls12-381.fr/0">, %arg4: !protocol.service_ref<"random.bls12-381.fr/0">):
      %0 = "protocol.query"(%arg3) <{method = "draw", owner = "role00000000", site = "s0"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
      %1 = "algebra.group_scale"(%arg0, %0) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %2 = "protocol.exchange"(%1) <{receiver = "role00000001", sender = "role00000000", site = "label_636f6d6d69746d656e74_0"}> : (!algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %3 = "protocol.restrict_roles"(%2) <{roles = ["role00000001"]}> : (!algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %4 = "protocol.query"(%arg4) <{method = "draw", owner = "role00000001", site = "label_6368616c6c656e6765"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
      %5 = "protocol.exchange"(%4) <{receiver = "role00000000", sender = "role00000001", site = "label_64656c6976657279_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %6 = "protocol.restrict_roles"(%5) <{roles = ["role00000000"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %7 = "algebra.field_multiply"(%6, %arg2) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %8 = "algebra.field_add"(%7, %0) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %9 = "protocol.exchange"(%8) <{receiver = "role00000001", sender = "role00000000", site = "label_726573706f6e7365_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %10 = "protocol.restrict_roles"(%9) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %11 = "algebra.group_scale"(%arg0, %10) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %12 = "algebra.group_scale"(%arg1, %4) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %13 = "algebra.group_add"(%12, %3) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %14 = "algebra.group_equal"(%11, %13) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> i1
      "protocol.return"(%14) : (i1) -> ()
    }) : () -> ()
  }) : () -> ()
}) : () -> ()

