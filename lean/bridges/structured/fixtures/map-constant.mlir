"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "protocol.func"() <{contracts = [], function_type = (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !data.field_vector<"bls12-381.fr">, input_roles = [["role00000000"], ["role00000000"], ["role00000000"]], origin = ["map_examples::ConstantRows", []], output_roles = [["role00000000"]], roles = ["role00000000", "role00000001"], sym_name = "s12h6d61705f6578616d706c657312h436f6e7374616e74526f7773"}> ({
    ^bb0(%arg15: !data.field_vector<"bls12-381.fr">, %arg16: !data.field_vector<"bls12-381.fr">, %arg17: !algebra.field<"bls12-381.fr">):
      %14 = "protocol.local_call"(%arg15, %arg16, %arg17) <{callee = @s12h6d61705f6578616d706c657313h636f6e7374616e745f726f7773, role = "role00000000", site = "s0"}> : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !data.field_vector<"bls12-381.fr">
      "protocol.return"(%14) : (!data.field_vector<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "s12h6d61705f6578616d706c657313h636f6e7374616e745f726f7773", sym_visibility = "private"}> ({
    ^bb0(%arg11: !runtime.scope, %arg12: !data.field_vector<"bls12-381.fr">, %arg13: !data.field_vector<"bls12-381.fr">, %arg14: !algebra.field<"bls12-381.fr">):
      %9 = "exec.collect"(%arg11, %arg12, %arg13, %arg14) <{body = @zkl_map_ccc1c016ea1f3b312948766a4b0f01a07c3864afef7b0f65db06e33c83c5a16c_body, domain = @zkl_map_ccc1c016ea1f3b312948766a4b0f01a07c3864afef7b0f65db06e33c83c5a16c_domain, site = "s0"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%9)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%10: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %11 = "exec.returned"(%10) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%11) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%12: !exec.stop):  // pred: ^bb0
      %13 = "exec.failed"(%12) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%13) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s12h6d61705f6578616d706c657313h636f6e7374616e745f726f7773", []]} : () -> ()
    "data.domain"() <{function_type = (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, sym_name = "zkl_map_ccc1c016ea1f3b312948766a4b0f01a07c3864afef7b0f65db06e33c83c5a16c_domain", sym_visibility = "private"}> ({
    ^bb0(%arg9: !data.field_vector<"bls12-381.fr">, %arg10: !data.field_vector<"bls12-381.fr">):
      %6 = "data.domain_elements"(%arg9) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %7 = "data.domain_elements"(%arg10) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %8 = "data.domain_zip"(%6, %7) : (!data.domain<!algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%8) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_map_ccc1c016ea1f3b312948766a4b0f01a07c3864afef7b0f65db06e33c83c5a16c_body", sym_visibility = "private"}> ({
    ^bb0(%arg3: !runtime.scope, %arg4: !algebra.field<"bls12-381.fr">, %arg5: !algebra.field<"bls12-381.fr">, %arg6: !data.field_vector<"bls12-381.fr">, %arg7: !data.field_vector<"bls12-381.fr">, %arg8: !algebra.field<"bls12-381.fr">):
      %1 = "exec.compute"(%arg3, %arg4, %arg5, %arg8) <{callee = @s12h6d61705f6578616d706c65738h636f6e7374616e74, site = "body"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%1)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%2: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %3 = "exec.returned"(%2) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%3) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%4: !exec.stop):  // pred: ^bb0
      %5 = "exec.failed"(%4) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%5) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zkl_map_ccc1c016ea1f3b312948766a4b0f01a07c3864afef7b0f65db06e33c83c5a16c_body", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "s12h6d61705f6578616d706c65738h636f6e7374616e74", sym_visibility = "private"}> ({
    ^bb0(%arg0: !algebra.field<"bls12-381.fr">, %arg1: !algebra.field<"bls12-381.fr">, %arg2: !algebra.field<"bls12-381.fr">):
      %0 = "algebra.constant"() <{value = #algebra.literal<<"bls12-381.fr">, 7 : ui255> : !algebra.field<"bls12-381.fr">}> : () -> !algebra.field<"bls12-381.fr">
      "func.return"(%0) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
  }) : () -> ()
}) : () -> ()

