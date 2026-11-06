"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "protocol.func"() <{contracts = [["target", "knowledge", [@zkl_6fa494d885c8d82de9abef99a9a62e27fcf8c7f2af288743241532ee562f92e7, [["input", 0, "role00000001"], ["input", 1, "role00000001"], ["input", 2, "role00000001"], ["input", 3, "role00000001"], ["input", 4, "role00000000"]]], unit, ["output", 0, "role00000001"]]], function_type = (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">, !protocol.service_ref<"random.bls12-381.fr/0">) -> i1, input_roles = [["role00000000", "role00000001"], ["role00000000", "role00000001"], ["role00000000", "role00000001"], ["role00000000", "role00000001"], ["role00000000"], ["role00000000"], ["role00000001"]], origin = ["sigma::ChaumPedersen", [["G", ["group", "bls12-381.g1"]]]], output_roles = [["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_171308863f7ffea0edd6d7c73a76733c4d6cae9ba8a58405e8c7862fb91df111"}> ({
    ^bb0(%arg29: !algebra.group<"bls12-381.g1">, %arg30: !algebra.group<"bls12-381.g1">, %arg31: !algebra.group<"bls12-381.g1">, %arg32: !algebra.group<"bls12-381.g1">, %arg33: !algebra.field<"bls12-381.fr">, %arg34: !protocol.service_ref<"random.bls12-381.fr/0">, %arg35: !protocol.service_ref<"random.bls12-381.fr/0">):
      %16 = "protocol.query"(%arg34) <{method = "draw", owner = "role00000000", site = "s0"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
      %17 = "algebra.group_scale"(%arg29, %16) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %18 = "protocol.exchange"(%17) <{receiver = "role00000001", sender = "role00000000", site = "label_66697273745f636f6d6d69746d656e74_0"}> : (!algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %19 = "protocol.restrict_roles"(%18) <{roles = ["role00000001"]}> : (!algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %20 = "algebra.group_scale"(%arg31, %16) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %21 = "protocol.exchange"(%20) <{receiver = "role00000001", sender = "role00000000", site = "label_7365636f6e645f636f6d6d69746d656e74_0"}> : (!algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %22 = "protocol.restrict_roles"(%21) <{roles = ["role00000001"]}> : (!algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %23 = "protocol.query"(%arg35) <{method = "draw", owner = "role00000001", site = "label_6368616c6c656e6765"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
      %24 = "protocol.exchange"(%23) <{receiver = "role00000000", sender = "role00000001", site = "label_64656c6976657279_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %25 = "protocol.restrict_roles"(%24) <{roles = ["role00000000"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %26 = "algebra.field_multiply"(%25, %arg33) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %27 = "algebra.field_add"(%16, %26) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %28 = "protocol.exchange"(%27) <{receiver = "role00000001", sender = "role00000000", site = "label_726573706f6e7365_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %29 = "protocol.restrict_roles"(%28) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %30 = "func.call"(%arg29, %29, %19, %arg30, %23, %arg31, %22, %arg32) <{callee = @zkl_4f9550b3befb5d34799290dfef3d1db12a4f36b45d06fdf2d0fba8ee6e8d4da9}> : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> i1
      "protocol.return"(%30) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "zkf_0fd0bc9206a16953b9f027e3c2bf28737cd91c0b40c440ff5e38197b21b98147", sym_visibility = "private"}> ({
    ^bb0(%arg18: !algebra.group<"bls12-381.g1">, %arg19: !algebra.group<"bls12-381.g1">, %arg20: !algebra.group<"bls12-381.g1">, %arg21: !algebra.group<"bls12-381.g1">, %arg22: !algebra.field<"bls12-381.fr">):
      %10 = "algebra.group_scale"(%arg18, %arg22) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %11 = "algebra.group_equal"(%arg19, %10) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> i1
      %12 = "data.branch"(%11, %arg20, %arg21, %arg22) <{alternatives = ["then", "else"]}> ({
      ^bb0(%arg26: !algebra.group<"bls12-381.g1">, %arg27: !algebra.group<"bls12-381.g1">, %arg28: !algebra.field<"bls12-381.fr">):
        %14 = "algebra.group_scale"(%arg26, %arg28) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
        %15 = "algebra.group_equal"(%arg27, %14) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> i1
        "data.yield"(%15) : (i1) -> ()
      }, {
      ^bb0(%arg23: !algebra.group<"bls12-381.g1">, %arg24: !algebra.group<"bls12-381.g1">, %arg25: !algebra.field<"bls12-381.fr">):
        %13 = "arith.constant"() <{value = false}> : () -> i1
        "data.yield"(%13) : (i1) -> ()
      }) : (i1, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> i1
      "func.return"(%12) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> i1, sym_name = "zkl_4f9550b3befb5d34799290dfef3d1db12a4f36b45d06fdf2d0fba8ee6e8d4da9", sym_visibility = "private"}> ({
    ^bb0(%arg0: !algebra.group<"bls12-381.g1">, %arg1: !algebra.field<"bls12-381.fr">, %arg2: !algebra.group<"bls12-381.g1">, %arg3: !algebra.group<"bls12-381.g1">, %arg4: !algebra.field<"bls12-381.fr">, %arg5: !algebra.group<"bls12-381.g1">, %arg6: !algebra.group<"bls12-381.g1">, %arg7: !algebra.group<"bls12-381.g1">):
      %0 = "algebra.group_scale"(%arg0, %arg1) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %1 = "algebra.group_scale"(%arg3, %arg4) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %2 = "algebra.group_add"(%arg2, %1) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %3 = "algebra.group_equal"(%0, %2) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> i1
      %4 = "data.branch"(%3, %arg5, %arg7, %arg6, %arg4, %arg1) <{alternatives = ["then", "else"]}> ({
      ^bb0(%arg13: !algebra.group<"bls12-381.g1">, %arg14: !algebra.group<"bls12-381.g1">, %arg15: !algebra.group<"bls12-381.g1">, %arg16: !algebra.field<"bls12-381.fr">, %arg17: !algebra.field<"bls12-381.fr">):
        %6 = "algebra.group_scale"(%arg13, %arg17) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
        %7 = "algebra.group_scale"(%arg14, %arg16) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
        %8 = "algebra.group_add"(%arg15, %7) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
        %9 = "algebra.group_equal"(%6, %8) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> i1
        "data.yield"(%9) : (i1) -> ()
      }, {
      ^bb0(%arg8: !algebra.group<"bls12-381.g1">, %arg9: !algebra.group<"bls12-381.g1">, %arg10: !algebra.group<"bls12-381.g1">, %arg11: !algebra.field<"bls12-381.fr">, %arg12: !algebra.field<"bls12-381.fr">):
        %5 = "arith.constant"() <{value = false}> : () -> i1
        "data.yield"(%5) : (i1) -> ()
      }) : (i1, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "func.return"(%4) : (i1) -> ()
    }) : () -> ()
    "relation.declare"() <{formula = @zkf_0fd0bc9206a16953b9f027e3c2bf28737cd91c0b40c440ff5e38197b21b98147, key = "zkl_6fa494d885c8d82de9abef99a9a62e27fcf8c7f2af288743241532ee562f92e7", kind = "zkc.language.formula/0", purposes = ["parameter", "statement", "parameter", "statement", "witness"], revision = "0adb19bdb4867e412249ffd2123ba7a548368f71f34502858733e9703bc7889c", signature = (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> i1, static_arguments = [], sym_name = "zkl_6fa494d885c8d82de9abef99a9a62e27fcf8c7f2af288743241532ee562f92e7"}> : () -> ()
  }) : () -> ()
}) : () -> ()

