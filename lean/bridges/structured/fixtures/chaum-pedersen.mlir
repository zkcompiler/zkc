"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "protocol.func"() <{contracts = [["target", "knowledge", [@zkl_6fa494d885c8d82de9abef99a9a62e27fcf8c7f2af288743241532ee562f92e7, [["input", 0, "role00000001"], ["input", 1, "role00000001"], ["input", 2, "role00000001"], ["input", 3, "role00000001"], ["input", 4, "role00000000"]]], unit, ["output", 0, "role00000001"]]], function_type = (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">, !protocol.service_ref<"random.bls12-381.fr/0">) -> i1, input_roles = [["role00000000", "role00000001"], ["role00000000", "role00000001"], ["role00000000", "role00000001"], ["role00000000", "role00000001"], ["role00000000"], ["role00000000"], ["role00000001"]], output_roles = [["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111"}> ({
    ^bb0(%arg5: !algebra.group<"bls12-381.g1">, %arg6: !algebra.group<"bls12-381.g1">, %arg7: !algebra.group<"bls12-381.g1">, %arg8: !algebra.group<"bls12-381.g1">, %arg9: !algebra.field<"bls12-381.fr">, %arg10: !protocol.service_ref<"random.bls12-381.fr/0">, %arg11: !protocol.service_ref<"random.bls12-381.fr/0">):
      %5 = "protocol.query"(%arg10) <{method = "draw", owner = "role00000000", site = "s0"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
      %6 = "algebra.group_scale"(%arg5, %5) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %7 = "protocol.exchange"(%6) <{receiver = "role00000001", sender = "role00000000", site = "label_66697273745f636f6d6d69746d656e74_0"}> : (!algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %8 = "protocol.restrict_roles"(%7) <{roles = ["role00000001"]}> : (!algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %9 = "algebra.group_scale"(%arg7, %5) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %10 = "protocol.exchange"(%9) <{receiver = "role00000001", sender = "role00000000", site = "label_7365636f6e645f636f6d6d69746d656e74_0"}> : (!algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %11 = "protocol.restrict_roles"(%10) <{roles = ["role00000001"]}> : (!algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %12 = "protocol.query"(%arg11) <{method = "draw", owner = "role00000001", site = "label_6368616c6c656e6765"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
      %13 = "protocol.exchange"(%12) <{receiver = "role00000000", sender = "role00000001", site = "label_64656c6976657279_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %14 = "protocol.restrict_roles"(%13) <{roles = ["role00000000"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %15 = "algebra.field_multiply"(%14, %arg9) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %16 = "algebra.field_add"(%5, %15) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %17 = "protocol.exchange"(%16) <{receiver = "role00000001", sender = "role00000000", site = "label_726573706f6e7365_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %18 = "protocol.restrict_roles"(%17) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %19 = "algebra.group_scale"(%arg5, %18) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %20 = "algebra.group_scale"(%arg6, %12) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %21 = "algebra.group_add"(%8, %20) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %22 = "algebra.group_equal"(%19, %21) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> i1
      %23 = "algebra.group_scale"(%arg7, %18) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %24 = "algebra.group_scale"(%arg8, %12) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %25 = "algebra.group_add"(%11, %24) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %26 = "algebra.group_equal"(%23, %25) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> i1
      %27 = "arith.andi"(%22, %26) : (i1, i1) -> i1
      "protocol.return"(%27) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "zkf_0fd0bc9206a16953b9f027e3c2bf28737cd91c0b40c440ff5e38197b21b98147", sym_visibility = "private"}> ({
    ^bb0(%arg0: !algebra.group<"bls12-381.g1">, %arg1: !algebra.group<"bls12-381.g1">, %arg2: !algebra.group<"bls12-381.g1">, %arg3: !algebra.group<"bls12-381.g1">, %arg4: !algebra.field<"bls12-381.fr">):
      %0 = "algebra.group_scale"(%arg0, %arg4) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %1 = "algebra.group_equal"(%arg1, %0) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> i1
      %2 = "algebra.group_scale"(%arg2, %arg4) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %3 = "algebra.group_equal"(%arg3, %2) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> i1
      %4 = "arith.andi"(%1, %3) : (i1, i1) -> i1
      "func.return"(%4) : (i1) -> ()
    }) : () -> ()
    "relation.declare"() <{formula = @zkf_0fd0bc9206a16953b9f027e3c2bf28737cd91c0b40c440ff5e38197b21b98147, key = "zkl_6fa494d885c8d82de9abef99a9a62e27fcf8c7f2af288743241532ee562f92e7", kind = "zkc.language.formula/0", purposes = ["parameter", "statement", "parameter", "statement", "witness"], revision = "ba2059dcc14692a71d992f2aaac1ac15f1b224edb53a0ae9e59fdfc364a956a4", signature = (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "zkl_6fa494d885c8d82de9abef99a9a62e27fcf8c7f2af288743241532ee562f92e7"}> : () -> ()
  }) : () -> ()
}) : () -> ()

