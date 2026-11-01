"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "protocol.func"() <{contracts = [["target", "selected_read", [@zkl_4a7527ef14d9b3ec64519e018a58da326ed309327b8561291731722a15176757, [["input", 0, "role00000001"], ["input", 1, "role00000001"], ["input", 2, "role00000001"]]], unit, ["output", 0, "role00000001"]]], function_type = (!algebra.field_vector<"koala-bear">, ui64, !algebra.field<"koala-bear">) -> i1, input_roles = [["role00000001"], ["role00000001"], ["role00000001"]], origin = ["table_relation::CheckRead", [["F", ["field", "koala-bear"]]]], output_roles = [["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_4597680e78fa47047d8f8fcedcf8fe295ebd02cf0856991e260e9130a8d2ea87"}> ({
    ^bb0(%arg21: !algebra.field_vector<"koala-bear">, %arg22: ui64, %arg23: !algebra.field<"koala-bear">):
      %15 = "protocol.local_call"(%arg21, %arg22, %arg23) <{callee = @zkl_f1d7fac3d3ce489e30442c70b43fb2fd1ecf6ba206d6f59492b3f75b72249a66, role = "role00000001", site = "s0"}> : (!algebra.field_vector<"koala-bear">, ui64, !algebra.field<"koala-bear">) -> i1
      "protocol.return"(%15) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"koala-bear">, ui64, !algebra.field<"koala-bear">) -> i1, sym_name = "zkf_eeb8bf15a7659bce5aa909302f5a359e054778ba70f159e4c02088dc98b55444", sym_visibility = "private"}> ({
    ^bb0(%arg18: !algebra.field_vector<"koala-bear">, %arg19: ui64, %arg20: !algebra.field<"koala-bear">):
      %14 = "func.call"(%arg18, %arg19, %arg20) <{callee = @zkl_513fafc86f60e415471e1286479cbd64b87fc18d657412194e4e0974b61e260a}> : (!algebra.field_vector<"koala-bear">, ui64, !algebra.field<"koala-bear">) -> i1
      "func.return"(%14) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"koala-bear">, ui64, !algebra.field<"koala-bear">) -> i1, sym_name = "zkl_513fafc86f60e415471e1286479cbd64b87fc18d657412194e4e0974b61e260a", sym_visibility = "private"}> ({
    ^bb0(%arg15: !algebra.field_vector<"koala-bear">, %arg16: ui64, %arg17: !algebra.field<"koala-bear">):
      %12 = "arith.constant"() <{value = false}> : () -> i1
      %13 = "algebra.finite_fold"(%arg15, %12, %arg16, %arg17) <{domain = @finite_zkl_513fafc86f60e415471e1286479cbd64b87fc18d657412194e4e0974b61e260a_s4_domain, step = @finite_zkl_513fafc86f60e415471e1286479cbd64b87fc18d657412194e4e0974b61e260a_s4_body}> : (!algebra.field_vector<"koala-bear">, i1, ui64, !algebra.field<"koala-bear">) -> i1
      "func.return"(%13) : (i1) -> ()
    }) : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"koala-bear">) -> !data.domain<ui64>, sym_name = "finite_zkl_513fafc86f60e415471e1286479cbd64b87fc18d657412194e4e0974b61e260a_s4_domain", sym_visibility = "private"}> ({
    ^bb0(%arg14: !algebra.field_vector<"koala-bear">):
      %11 = "data.domain_indices"(%arg14) <{axis = 0 : i64}> : (!algebra.field_vector<"koala-bear">) -> !data.domain<ui64>
      "data.domain_yield"(%11) : (!data.domain<ui64>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (i1, ui64, !algebra.field_vector<"koala-bear">, ui64, !algebra.field<"koala-bear">) -> i1, sym_name = "finite_zkl_513fafc86f60e415471e1286479cbd64b87fc18d657412194e4e0974b61e260a_s4_body", sym_visibility = "private"}> ({
    ^bb0(%arg9: i1, %arg10: ui64, %arg11: !algebra.field_vector<"koala-bear">, %arg12: ui64, %arg13: !algebra.field<"koala-bear">):
      %10 = "func.call"(%arg9, %arg10, %arg12, %arg11, %arg13) <{callee = @zkl_b495e0ed1417c211869f7fedf6d130630630d8ae869a74d3e0edf61af30302b3}> : (i1, ui64, ui64, !algebra.field_vector<"koala-bear">, !algebra.field<"koala-bear">) -> i1
      "func.return"(%10) : (i1) -> ()
    }) {data.preconditions = [#data.index_bound<1, 2, 0>]} : () -> ()
    "func.func"() <{function_type = (i1, ui64, ui64, !algebra.field_vector<"koala-bear">, !algebra.field<"koala-bear">) -> i1, sym_name = "zkl_b495e0ed1417c211869f7fedf6d130630630d8ae869a74d3e0edf61af30302b3", sym_visibility = "private"}> ({
    ^bb0(%arg4: i1, %arg5: ui64, %arg6: ui64, %arg7: !algebra.field_vector<"koala-bear">, %arg8: !algebra.field<"koala-bear">):
      %5 = "data.index_equal"(%arg5, %arg6) : (ui64, ui64) -> i1
      %6 = "data.bounded_at"(%arg7, %arg5) : (!algebra.field_vector<"koala-bear">, ui64) -> !algebra.field<"koala-bear">
      %7 = "algebra.field_equal"(%6, %arg8) : (!algebra.field<"koala-bear">, !algebra.field<"koala-bear">) -> i1
      %8 = "arith.andi"(%5, %7) : (i1, i1) -> i1
      %9 = "arith.ori"(%arg4, %8) : (i1, i1) -> i1
      "func.return"(%9) : (i1) -> ()
    }) {data.preconditions = [#data.index_bound<1, 3, 0>]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"koala-bear">, ui64, !algebra.field<"koala-bear">) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_f1d7fac3d3ce489e30442c70b43fb2fd1ecf6ba206d6f59492b3f75b72249a66", sym_visibility = "private"}> ({
    ^bb0(%arg0: !runtime.scope, %arg1: !algebra.field_vector<"koala-bear">, %arg2: ui64, %arg3: !algebra.field<"koala-bear">):
      %0 = "exec.compute"(%arg0, %arg1, %arg2, %arg3) <{callee = @zkl_513fafc86f60e415471e1286479cbd64b87fc18d657412194e4e0974b61e260a, site = "s0"}> : (!runtime.scope, !algebra.field_vector<"koala-bear">, ui64, !algebra.field<"koala-bear">) -> !exec.outcome<(i1)>
      "exec.dispatch"(%0)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1: i1):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%2) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%4) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.origin = ["s14h7461626c655f72656c6174696f6e10h636865636b5f72656164", []]} : () -> ()
    "relation.declare"() <{formula = @zkf_eeb8bf15a7659bce5aa909302f5a359e054778ba70f159e4c02088dc98b55444, key = "zkl_4a7527ef14d9b3ec64519e018a58da326ed309327b8561291731722a15176757", kind = "zkc.language.formula/0", purposes = ["parameter", "statement", "statement"], revision = "ae9fe16a4a5ff9b0b0dea1491f4b761b2cb11e19451a102fb23355c2e24c644d", signature = (!algebra.field_vector<"koala-bear">, ui64, !algebra.field<"koala-bear">) -> i1, static_arguments = [], sym_name = "zkl_4a7527ef14d9b3ec64519e018a58da326ed309327b8561291731722a15176757"}> : () -> ()
  }) : () -> ()
}) : () -> ()

