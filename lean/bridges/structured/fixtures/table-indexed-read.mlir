"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "local.realize"() <{function_type = (!algebra.field_vector<"koala-bear">, ui64, !algebra.field<"koala-bear">) -> i1, helper = @zkl_513fafc86f60e415471e1286479cbd64b87fc18d657412194e4e0974b61e260a, sym_name = "zkl_realization_f23e2cf91e13194bc53b5a53cc8b12fd546c4daae64d3751bb30899d04fa3be4"}> : () -> ()
    "protocol.func"() <{contracts = [["target", "selected_read", [@zkl_4a7527ef14d9b3ec64519e018a58da326ed309327b8561291731722a15176757, [["input", 0, "role00000001"], ["input", 1, "role00000001"], ["input", 2, "role00000001"]]], unit, ["output", 0, "role00000001"]]], function_type = (!algebra.field_vector<"koala-bear">, ui64, !algebra.field<"koala-bear">) -> i1, input_roles = [["role00000001"], ["role00000001"], ["role00000001"]], output_roles = [["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_4597680e78fa47047d8f8fcedcf8fe295ebd02cf0856991e260e9130a8d2ea87"}> ({
    ^bb0(%arg20: !algebra.field_vector<"koala-bear">, %arg21: ui64, %arg22: !algebra.field<"koala-bear">):
      %11 = "protocol.local_call"(%arg20, %arg21, %arg22) <{callee = @zkl_f1d7fac3d3ce489e30442c70b43fb2fd1ecf6ba206d6f59492b3f75b72249a66, role = "role00000001", site = "s0"}> : (!algebra.field_vector<"koala-bear">, ui64, !algebra.field<"koala-bear">) -> i1
      "protocol.return"(%11) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"koala-bear">, ui64, !algebra.field<"koala-bear">) -> i1, sym_name = "zkf_eeb8bf15a7659bce5aa909302f5a359e054778ba70f159e4c02088dc98b55444", sym_visibility = "private"}> ({
    ^bb0(%arg17: !algebra.field_vector<"koala-bear">, %arg18: ui64, %arg19: !algebra.field<"koala-bear">):
      %10 = "func.call"(%arg17, %arg18, %arg19) <{callee = @zkl_513fafc86f60e415471e1286479cbd64b87fc18d657412194e4e0974b61e260a}> : (!algebra.field_vector<"koala-bear">, ui64, !algebra.field<"koala-bear">) -> i1
      "func.return"(%10) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"koala-bear">, ui64, !algebra.field<"koala-bear">) -> i1, sym_name = "zkl_513fafc86f60e415471e1286479cbd64b87fc18d657412194e4e0974b61e260a", sym_visibility = "private"}> ({
    ^bb0(%arg14: !algebra.field_vector<"koala-bear">, %arg15: ui64, %arg16: !algebra.field<"koala-bear">):
      %8 = "arith.constant"() <{value = false}> : () -> i1
      %9 = "algebra.finite_fold"(%arg14, %8, %arg15, %arg16) <{domain = @finite_zkl_513fafc86f60e415471e1286479cbd64b87fc18d657412194e4e0974b61e260a_s4_domain, step = @finite_zkl_513fafc86f60e415471e1286479cbd64b87fc18d657412194e4e0974b61e260a_s4_body}> : (!algebra.field_vector<"koala-bear">, i1, ui64, !algebra.field<"koala-bear">) -> i1
      "func.return"(%9) : (i1) -> ()
    }) : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"koala-bear">) -> !data.domain<ui64>, sym_name = "finite_zkl_513fafc86f60e415471e1286479cbd64b87fc18d657412194e4e0974b61e260a_s4_domain", sym_visibility = "private"}> ({
    ^bb0(%arg13: !algebra.field_vector<"koala-bear">):
      %7 = "data.domain_indices"(%arg13) <{axis = 0 : i64}> : (!algebra.field_vector<"koala-bear">) -> !data.domain<ui64>
      "data.domain_yield"(%7) : (!data.domain<ui64>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (i1, ui64, !algebra.field_vector<"koala-bear">, ui64, !algebra.field<"koala-bear">) -> i1, sym_name = "finite_zkl_513fafc86f60e415471e1286479cbd64b87fc18d657412194e4e0974b61e260a_s4_body", sym_visibility = "private"}> ({
    ^bb0(%arg8: i1, %arg9: ui64, %arg10: !algebra.field_vector<"koala-bear">, %arg11: ui64, %arg12: !algebra.field<"koala-bear">):
      %6 = "func.call"(%arg8, %arg9, %arg11, %arg10, %arg12) <{callee = @zkl_b495e0ed1417c211869f7fedf6d130630630d8ae869a74d3e0edf61af30302b3}> : (i1, ui64, ui64, !algebra.field_vector<"koala-bear">, !algebra.field<"koala-bear">) -> i1
      "func.return"(%6) : (i1) -> ()
    }) {data.preconditions = [#data.index_bound<1, 2, 0>]} : () -> ()
    "func.func"() <{function_type = (i1, ui64, ui64, !algebra.field_vector<"koala-bear">, !algebra.field<"koala-bear">) -> i1, sym_name = "zkl_b495e0ed1417c211869f7fedf6d130630630d8ae869a74d3e0edf61af30302b3", sym_visibility = "private"}> ({
    ^bb0(%arg3: i1, %arg4: ui64, %arg5: ui64, %arg6: !algebra.field_vector<"koala-bear">, %arg7: !algebra.field<"koala-bear">):
      %1 = "data.index_equal"(%arg4, %arg5) : (ui64, ui64) -> i1
      %2 = "data.bounded_at"(%arg6, %arg4) : (!algebra.field_vector<"koala-bear">, ui64) -> !algebra.field<"koala-bear">
      %3 = "algebra.field_equal"(%2, %arg7) : (!algebra.field<"koala-bear">, !algebra.field<"koala-bear">) -> i1
      %4 = "arith.andi"(%1, %3) : (i1, i1) -> i1
      %5 = "arith.ori"(%arg3, %4) : (i1, i1) -> i1
      "func.return"(%5) : (i1) -> ()
    }) {data.preconditions = [#data.index_bound<1, 3, 0>]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"koala-bear">, ui64, !algebra.field<"koala-bear">) -> i1, sym_name = "zkl_f1d7fac3d3ce489e30442c70b43fb2fd1ecf6ba206d6f59492b3f75b72249a66"}> ({
    ^bb0(%arg0: !algebra.field_vector<"koala-bear">, %arg1: ui64, %arg2: !algebra.field<"koala-bear">):
      %0 = "local.apply"(%arg0, %arg1, %arg2) <{callee = @zkl_realization_f23e2cf91e13194bc53b5a53cc8b12fd546c4daae64d3751bb30899d04fa3be4, site = "s0"}> : (!algebra.field_vector<"koala-bear">, ui64, !algebra.field<"koala-bear">) -> i1
      "local.return"(%0) : (i1) -> ()
    }) {logical_origin = ["s14h7461626c655f72656c6174696f6e10h636865636b5f72656164", []]} : () -> ()
    "relation.declare"() <{formula = @zkf_eeb8bf15a7659bce5aa909302f5a359e054778ba70f159e4c02088dc98b55444, key = "zkl_4a7527ef14d9b3ec64519e018a58da326ed309327b8561291731722a15176757", kind = "zkc.language.formula/0", purposes = ["parameter", "statement", "statement"], revision = "ae9fe16a4a5ff9b0b0dea1491f4b761b2cb11e19451a102fb23355c2e24c644d", signature = (!algebra.field_vector<"koala-bear">, ui64, !algebra.field<"koala-bear">) -> i1, sym_name = "zkl_4a7527ef14d9b3ec64519e018a58da326ed309327b8561291731722a15176757"}> : () -> ()
  }) : () -> ()
}) : () -> ()

