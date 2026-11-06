"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "protocol.func"() <{contracts = [["target", "knowledge", [@zkl_c0ba4fcd9fc5cad717b8a516be11f316ea8ea6ce0d721ba5e44a7408e5d76479, [["input", 0, "role00000001"], ["input", 1, "role00000001"], ["input", 2, "role00000001"], ["input", 3, "role00000001"], ["input", 4, "role00000000"], ["input", 5, "role00000000"]]], unit, ["output", 0, "role00000001"]]], function_type = (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">, !protocol.service_ref<"random.bls12-381.fr/0">) -> i1, input_roles = [["role00000000", "role00000001"], ["role00000000", "role00000001"], ["role00000000", "role00000001"], ["role00000000", "role00000001"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"]], origin = ["sigma::SchnorrAnd", [["G", ["group", "bls12-381.g1"]]]], output_roles = [["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c"}> ({
    ^bb0(%arg31: !algebra.group<"bls12-381.g1">, %arg32: !algebra.group<"bls12-381.g1">, %arg33: !algebra.group<"bls12-381.g1">, %arg34: !algebra.group<"bls12-381.g1">, %arg35: !algebra.field<"bls12-381.fr">, %arg36: !algebra.field<"bls12-381.fr">, %arg37: !protocol.service_ref<"random.bls12-381.fr/0">, %arg38: !protocol.service_ref<"random.bls12-381.fr/0">):
      %16 = "protocol.query"(%arg37) <{method = "draw", owner = "role00000000", site = "s0"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
      %17 = "protocol.query"(%arg37) <{method = "draw", owner = "role00000000", site = "s2"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
      %18 = "algebra.group_scale"(%arg31, %16) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %19 = "protocol.exchange"(%18) <{receiver = "role00000001", sender = "role00000000", site = "label_66697273745f636f6d6d69746d656e74_0"}> : (!algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %20 = "protocol.restrict_roles"(%19) <{roles = ["role00000001"]}> : (!algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %21 = "algebra.group_scale"(%arg33, %17) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %22 = "protocol.exchange"(%21) <{receiver = "role00000001", sender = "role00000000", site = "label_7365636f6e645f636f6d6d69746d656e74_0"}> : (!algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %23 = "protocol.restrict_roles"(%22) <{roles = ["role00000001"]}> : (!algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %24 = "protocol.query"(%arg38) <{method = "draw", owner = "role00000001", site = "label_6368616c6c656e6765"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
      %25 = "protocol.exchange"(%24) <{receiver = "role00000000", sender = "role00000001", site = "label_64656c6976657279_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %26 = "protocol.restrict_roles"(%25) <{roles = ["role00000000"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %27 = "algebra.field_multiply"(%26, %arg35) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %28 = "algebra.field_add"(%16, %27) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %29 = "protocol.exchange"(%28) <{receiver = "role00000001", sender = "role00000000", site = "label_66697273745f726573706f6e7365_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %30 = "protocol.restrict_roles"(%29) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %31 = "algebra.field_multiply"(%26, %arg36) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %32 = "algebra.field_add"(%17, %31) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %33 = "protocol.exchange"(%32) <{receiver = "role00000001", sender = "role00000000", site = "label_7365636f6e645f726573706f6e7365_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %34 = "protocol.restrict_roles"(%33) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %35 = "func.call"(%arg31, %30, %20, %arg32, %24, %arg33, %34, %23, %arg34) <{callee = @zkl_58c3e21ec903d97998e4e0fbc53e6da76c0f9a6d09bd13bcd30d778eb1f644b0}> : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> i1
      "protocol.return"(%35) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "zkf_49bce65071a20df1cff727e48d886938c8c9df8435e9fe20ce75346e20a2f1d2", sym_visibility = "private"}> ({
    ^bb0(%arg19: !algebra.group<"bls12-381.g1">, %arg20: !algebra.group<"bls12-381.g1">, %arg21: !algebra.group<"bls12-381.g1">, %arg22: !algebra.group<"bls12-381.g1">, %arg23: !algebra.field<"bls12-381.fr">, %arg24: !algebra.field<"bls12-381.fr">):
      %10 = "algebra.group_scale"(%arg19, %arg23) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %11 = "algebra.group_equal"(%arg20, %10) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> i1
      %12 = "data.branch"(%11, %arg21, %arg22, %arg24) <{alternatives = ["then", "else"]}> ({
      ^bb0(%arg28: !algebra.group<"bls12-381.g1">, %arg29: !algebra.group<"bls12-381.g1">, %arg30: !algebra.field<"bls12-381.fr">):
        %14 = "algebra.group_scale"(%arg28, %arg30) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
        %15 = "algebra.group_equal"(%arg29, %14) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> i1
        "data.yield"(%15) : (i1) -> ()
      }, {
      ^bb0(%arg25: !algebra.group<"bls12-381.g1">, %arg26: !algebra.group<"bls12-381.g1">, %arg27: !algebra.field<"bls12-381.fr">):
        %13 = "arith.constant"() <{value = false}> : () -> i1
        "data.yield"(%13) : (i1) -> ()
      }) : (i1, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> i1
      "func.return"(%12) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> i1, sym_name = "zkl_58c3e21ec903d97998e4e0fbc53e6da76c0f9a6d09bd13bcd30d778eb1f644b0", sym_visibility = "private"}> ({
    ^bb0(%arg0: !algebra.group<"bls12-381.g1">, %arg1: !algebra.field<"bls12-381.fr">, %arg2: !algebra.group<"bls12-381.g1">, %arg3: !algebra.group<"bls12-381.g1">, %arg4: !algebra.field<"bls12-381.fr">, %arg5: !algebra.group<"bls12-381.g1">, %arg6: !algebra.field<"bls12-381.fr">, %arg7: !algebra.group<"bls12-381.g1">, %arg8: !algebra.group<"bls12-381.g1">):
      %0 = "algebra.group_scale"(%arg0, %arg1) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %1 = "algebra.group_scale"(%arg3, %arg4) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %2 = "algebra.group_add"(%arg2, %1) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %3 = "algebra.group_equal"(%0, %2) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> i1
      %4 = "data.branch"(%3, %arg5, %arg8, %arg7, %arg4, %arg6) <{alternatives = ["then", "else"]}> ({
      ^bb0(%arg14: !algebra.group<"bls12-381.g1">, %arg15: !algebra.group<"bls12-381.g1">, %arg16: !algebra.group<"bls12-381.g1">, %arg17: !algebra.field<"bls12-381.fr">, %arg18: !algebra.field<"bls12-381.fr">):
        %6 = "algebra.group_scale"(%arg14, %arg18) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
        %7 = "algebra.group_scale"(%arg15, %arg17) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
        %8 = "algebra.group_add"(%arg16, %7) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
        %9 = "algebra.group_equal"(%6, %8) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> i1
        "data.yield"(%9) : (i1) -> ()
      }, {
      ^bb0(%arg9: !algebra.group<"bls12-381.g1">, %arg10: !algebra.group<"bls12-381.g1">, %arg11: !algebra.group<"bls12-381.g1">, %arg12: !algebra.field<"bls12-381.fr">, %arg13: !algebra.field<"bls12-381.fr">):
        %5 = "arith.constant"() <{value = false}> : () -> i1
        "data.yield"(%5) : (i1) -> ()
      }) : (i1, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "func.return"(%4) : (i1) -> ()
    }) : () -> ()
    "relation.declare"() <{formula = @zkf_49bce65071a20df1cff727e48d886938c8c9df8435e9fe20ce75346e20a2f1d2, key = "zkl_c0ba4fcd9fc5cad717b8a516be11f316ea8ea6ce0d721ba5e44a7408e5d76479", kind = "zkc.language.formula/0", purposes = ["parameter", "statement", "parameter", "statement", "witness", "witness"], revision = "616a353fe82e807dd7b167264e5e3c13a5ac8a15e222e77f7061419c0141cb3a", signature = (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, static_arguments = [], sym_name = "zkl_c0ba4fcd9fc5cad717b8a516be11f316ea8ea6ce0d721ba5e44a7408e5d76479"}> : () -> ()
  }) : () -> ()
}) : () -> ()

