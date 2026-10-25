"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "protocol.func"() <{contracts = [["target", "knowledge", [@zkl_953e9730b1a3459b686ab1fc4c9b32625aee39f5957b8c87bb62e2a814b74b8b, [["input", 0, "role00000001"], ["input", 1, "role00000001"], ["input", 2, "role00000001"], ["input", 3, "role00000000"], ["input", 4, "role00000000"]]], unit, ["output", 0, "role00000001"]]], function_type = (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">, !protocol.service_ref<"random.bls12-381.fr/0">) -> i1, input_roles = [["role00000000", "role00000001"], ["role00000000", "role00000001"], ["role00000000", "role00000001"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"]], origin = ["okamoto::Okamoto", [["G", ["group", "bls12-381.g1"]]]], output_roles = [["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_cb3e72883b485338da9280b19db8db790298fd13d2324e645c75fcbf0f3b86c9"}> ({
    ^bb0(%arg5: !algebra.group<"bls12-381.g1">, %arg6: !algebra.group<"bls12-381.g1">, %arg7: !algebra.group<"bls12-381.g1">, %arg8: !algebra.field<"bls12-381.fr">, %arg9: !algebra.field<"bls12-381.fr">, %arg10: !protocol.service_ref<"random.bls12-381.fr/0">, %arg11: !protocol.service_ref<"random.bls12-381.fr/0">):
      %4 = "protocol.query"(%arg10) <{method = "draw", owner = "role00000000", site = "label_66697273745f6e6f6e6365"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
      %5 = "protocol.query"(%arg10) <{method = "draw", owner = "role00000000", site = "label_7365636f6e645f6e6f6e6365"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
      %6 = "algebra.group_scale"(%arg5, %4) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %7 = "algebra.group_scale"(%arg6, %5) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %8 = "algebra.group_add"(%6, %7) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %9 = "protocol.exchange"(%8) <{receiver = "role00000001", sender = "role00000000", site = "label_636f6d6d69746d656e74_0"}> : (!algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %10 = "protocol.restrict_roles"(%9) <{roles = ["role00000001"]}> : (!algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %11 = "protocol.query"(%arg11) <{method = "draw", owner = "role00000001", site = "label_6368616c6c656e6765"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
      %12 = "protocol.exchange"(%11) <{receiver = "role00000000", sender = "role00000001", site = "label_64656c6976657279_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %13 = "protocol.restrict_roles"(%12) <{roles = ["role00000000"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %14 = "algebra.field_multiply"(%13, %arg8) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %15 = "algebra.field_add"(%4, %14) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %16 = "protocol.exchange"(%15) <{receiver = "role00000001", sender = "role00000000", site = "label_66697273745f726573706f6e7365_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %17 = "protocol.restrict_roles"(%16) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %18 = "algebra.field_multiply"(%13, %arg9) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %19 = "algebra.field_add"(%5, %18) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %20 = "protocol.exchange"(%19) <{receiver = "role00000001", sender = "role00000000", site = "label_7365636f6e645f726573706f6e7365_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %21 = "protocol.restrict_roles"(%20) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %22 = "algebra.group_scale"(%arg5, %17) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %23 = "algebra.group_scale"(%arg6, %21) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %24 = "algebra.group_add"(%22, %23) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %25 = "algebra.group_scale"(%arg7, %11) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %26 = "algebra.group_add"(%10, %25) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %27 = "algebra.group_equal"(%24, %26) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> i1
      "protocol.return"(%27) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "zkf_01154fec8af291aca8be519c449a67c049aa4dcb065a920025604d72b145cb5c", sym_visibility = "private"}> ({
    ^bb0(%arg0: !algebra.group<"bls12-381.g1">, %arg1: !algebra.group<"bls12-381.g1">, %arg2: !algebra.group<"bls12-381.g1">, %arg3: !algebra.field<"bls12-381.fr">, %arg4: !algebra.field<"bls12-381.fr">):
      %0 = "algebra.group_scale"(%arg0, %arg3) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %1 = "algebra.group_scale"(%arg1, %arg4) : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
      %2 = "algebra.group_add"(%0, %1) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
      %3 = "algebra.group_equal"(%arg2, %2) : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> i1
      "func.return"(%3) : (i1) -> ()
    }) : () -> ()
    "relation.declare"() <{formula = @zkf_01154fec8af291aca8be519c449a67c049aa4dcb065a920025604d72b145cb5c, key = "zkl_953e9730b1a3459b686ab1fc4c9b32625aee39f5957b8c87bb62e2a814b74b8b", kind = "zkc.language.formula/0", purposes = ["parameter", "parameter", "statement", "witness", "witness"], revision = "df5dd2e7e263c52a9cf241755236669ffbef101adf20da7012c766d10fbcfc92", signature = (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "zkl_953e9730b1a3459b686ab1fc4c9b32625aee39f5957b8c87bb62e2a814b74b8b"}> : () -> ()
  }) : () -> ()
}) : () -> ()

