"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "protocol.func"() <{contracts = [["target", "knowledge", [@zkl_c0ba4fcd9fc5cad717b8a516be11f316ea8ea6ce0d721ba5e44a7408e5d76479, [["input", 0, "role00000001"], ["input", 1, "role00000001"], ["input", 2, "role00000001"], ["input", 3, "role00000001"], ["input", 4, "role00000000"], ["input", 5, "role00000000"]]], unit, ["output", 0, "role00000001"]]], function_type = (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">, !protocol.service_ref<"random.bls12-381.fr/0">) -> i1, input_roles = [["role00000000", "role00000001"], ["role00000000", "role00000001"], ["role00000000", "role00000001"], ["role00000000", "role00000001"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"]], output_roles = [["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_ca4d47255ab472c390dbc54e901ce9c73b3e2fdf3d860ea5dd1ae37ae3995c1c"}> ({
    ^bb0(%arg6: !algebra.group<"bls12-381.g1">, %arg7: !algebra.group<"bls12-381.g1">, %arg8: !algebra.group<"bls12-381.g1">, %arg9: !algebra.group<"bls12-381.g1">, %arg10: !algebra.field<"bls12-381.fr">, %arg11: !algebra.field<"bls12-381.fr">, %arg12: !protocol.service_ref<"random.bls12-381.fr/0">, %arg13: !protocol.service_ref<"random.bls12-381.fr/0">):
      %5 = "protocol.query"(%arg12) <{method = "draw", owner = "role00000000", site = "s0"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
      %6 = "protocol.query"(%arg12) <{method = "draw", owner = "role00000000", site = "s2"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
      %7 = "algebra.group_scale"(%arg6, %5) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %8 = "protocol.exchange"(%7) <{receiver = "role00000001", sender = "role00000000", site = "label_66697273745f636f6d6d69746d656e74_0"}> : (!algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %9 = "protocol.restrict_roles"(%8) <{roles = ["role00000001"]}> : (!algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %10 = "algebra.group_scale"(%arg8, %6) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %11 = "protocol.exchange"(%10) <{receiver = "role00000001", sender = "role00000000", site = "label_7365636f6e645f636f6d6d69746d656e74_0"}> : (!algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %12 = "protocol.restrict_roles"(%11) <{roles = ["role00000001"]}> : (!algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %13 = "protocol.query"(%arg13) <{method = "draw", owner = "role00000001", site = "label_6368616c6c656e6765"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
      %14 = "protocol.exchange"(%13) <{receiver = "role00000000", sender = "role00000001", site = "label_64656c6976657279_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %15 = "protocol.restrict_roles"(%14) <{roles = ["role00000000"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %16 = "algebra.field_multiply"(%15, %arg10) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %17 = "algebra.field_add"(%5, %16) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %18 = "protocol.exchange"(%17) <{receiver = "role00000001", sender = "role00000000", site = "label_66697273745f726573706f6e7365_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %19 = "protocol.restrict_roles"(%18) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %20 = "algebra.field_multiply"(%15, %arg11) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %21 = "algebra.field_add"(%6, %20) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %22 = "protocol.exchange"(%21) <{receiver = "role00000001", sender = "role00000000", site = "label_7365636f6e645f726573706f6e7365_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %23 = "protocol.restrict_roles"(%22) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %24 = "algebra.group_scale"(%arg6, %19) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %25 = "algebra.group_scale"(%arg7, %13) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %26 = "algebra.group_add"(%9, %25) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %27 = "algebra.group_equal"(%24, %26) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> i1
      %28 = "algebra.group_scale"(%arg8, %23) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %29 = "algebra.group_scale"(%arg9, %13) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %30 = "algebra.group_add"(%12, %29) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %31 = "algebra.group_equal"(%28, %30) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> i1
      %32 = "arith.andi"(%27, %31) : (i1, i1) -> i1
      "protocol.return"(%32) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "zkf_49bce65071a20df1cff727e48d886938c8c9df8435e9fe20ce75346e20a2f1d2", sym_visibility = "private"}> ({
    ^bb0(%arg0: !algebra.group<"bls12-381.g1">, %arg1: !algebra.group<"bls12-381.g1">, %arg2: !algebra.group<"bls12-381.g1">, %arg3: !algebra.group<"bls12-381.g1">, %arg4: !algebra.field<"bls12-381.fr">, %arg5: !algebra.field<"bls12-381.fr">):
      %0 = "algebra.group_scale"(%arg0, %arg4) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %1 = "algebra.group_equal"(%arg1, %0) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> i1
      %2 = "algebra.group_scale"(%arg2, %arg5) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %3 = "algebra.group_equal"(%arg3, %2) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> i1
      %4 = "arith.andi"(%1, %3) : (i1, i1) -> i1
      "func.return"(%4) : (i1) -> ()
    }) : () -> ()
    "relation.declare"() <{formula = @zkf_49bce65071a20df1cff727e48d886938c8c9df8435e9fe20ce75346e20a2f1d2, key = "zkl_c0ba4fcd9fc5cad717b8a516be11f316ea8ea6ce0d721ba5e44a7408e5d76479", kind = "zkc.language.formula/0", purposes = ["parameter", "statement", "parameter", "statement", "witness", "witness"], revision = "24ff615d21d3bf32066480e5ab928bbf981474b85cb311042926e1c5f7299bb6", signature = (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "zkl_c0ba4fcd9fc5cad717b8a516be11f316ea8ea6ce0d721ba5e44a7408e5d76479"}> : () -> ()
  }) : () -> ()
}) : () -> ()

