"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "protocol.func"() <{contracts = [], function_type = (!algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">, input_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"]], origin = ["map_examples::LinearCombination", []], output_roles = [["role00000000"]], roles = ["role00000000", "role00000001"], sym_name = "s12h6d61705f6578616d706c657317h4c696e656172436f6d62696e6174696f6e"}> ({
    ^bb0(%arg28: !algebra.field<"bls12-381.fr">, %arg29: !algebra.field_vector<"bls12-381.fr">, %arg30: !algebra.field<"bls12-381.fr">, %arg31: !algebra.field_vector<"bls12-381.fr">, %arg32: !algebra.field_vector<"bls12-381.fr">, %arg33: !algebra.field<"bls12-381.fr">):
      %20 = "protocol.local_call"(%arg28, %arg29, %arg30, %arg31, %arg32, %arg33) <{callee = @s12h6d61705f6578616d706c657311h636f6d62696e6174696f6e, role = "role00000000", site = "s0"}> : (!algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
      "protocol.return"(%20) : (!algebra.field_vector<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "s12h6d61705f6578616d706c657311h636f6d62696e6174696f6e", sym_visibility = "private"}> ({
    ^bb0(%arg21: !runtime.scope, %arg22: !algebra.field<"bls12-381.fr">, %arg23: !algebra.field_vector<"bls12-381.fr">, %arg24: !algebra.field<"bls12-381.fr">, %arg25: !algebra.field_vector<"bls12-381.fr">, %arg26: !algebra.field_vector<"bls12-381.fr">, %arg27: !algebra.field<"bls12-381.fr">):
      %15 = "exec.collect"(%arg21, %arg23, %arg25, %arg26, %arg22, %arg24, %arg27) <{body = @zkl_map_40c6231bdcafed97eac948be749084ce0abec13b10621543e354f70698ea9db6_body, domain = @zkl_map_40c6231bdcafed97eac948be749084ce0abec13b10621543e354f70698ea9db6_domain, site = "s0"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%15)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%16: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %17 = "exec.returned"(%16) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%17) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%18: !exec.stop):  // pred: ^bb0
      %19 = "exec.failed"(%18) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%19) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s12h6d61705f6578616d706c657311h636f6d62696e6174696f6e", []]} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, sym_name = "zkl_map_40c6231bdcafed97eac948be749084ce0abec13b10621543e354f70698ea9db6_domain", sym_visibility = "private"}> ({
    ^bb0(%arg18: !algebra.field_vector<"bls12-381.fr">, %arg19: !algebra.field_vector<"bls12-381.fr">, %arg20: !algebra.field_vector<"bls12-381.fr">):
      %11 = "data.domain_elements"(%arg18) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %12 = "data.domain_elements"(%arg19) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %13 = "data.domain_elements"(%arg20) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %14 = "data.domain_zip"(%11, %12, %13) : (!data.domain<!algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%14) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_map_40c6231bdcafed97eac948be749084ce0abec13b10621543e354f70698ea9db6_body", sym_visibility = "private"}> ({
    ^bb0(%arg8: !runtime.scope, %arg9: !algebra.field<"bls12-381.fr">, %arg10: !algebra.field<"bls12-381.fr">, %arg11: !algebra.field<"bls12-381.fr">, %arg12: !algebra.field_vector<"bls12-381.fr">, %arg13: !algebra.field_vector<"bls12-381.fr">, %arg14: !algebra.field_vector<"bls12-381.fr">, %arg15: !algebra.field<"bls12-381.fr">, %arg16: !algebra.field<"bls12-381.fr">, %arg17: !algebra.field<"bls12-381.fr">):
      %6 = "exec.compute"(%arg8, %arg15, %arg9, %arg16, %arg10, %arg11, %arg17) <{callee = @s12h6d61705f6578616d706c65736h6c696e656172, site = "body"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%6)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%7: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %8 = "exec.returned"(%7) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%8) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%9: !exec.stop):  // pred: ^bb0
      %10 = "exec.failed"(%9) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%10) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zkl_map_40c6231bdcafed97eac948be749084ce0abec13b10621543e354f70698ea9db6_body", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "s12h6d61705f6578616d706c65736h6c696e656172", sym_visibility = "private"}> ({
    ^bb0(%arg2: !algebra.field<"bls12-381.fr">, %arg3: !algebra.field<"bls12-381.fr">, %arg4: !algebra.field<"bls12-381.fr">, %arg5: !algebra.field<"bls12-381.fr">, %arg6: !algebra.field<"bls12-381.fr">, %arg7: !algebra.field<"bls12-381.fr">):
      %1 = "func.call"(%arg2, %arg3) <{callee = @s12h6d61705f6578616d706c65735h7363616c65}> : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %2 = "func.call"(%arg4, %arg5) <{callee = @s12h6d61705f6578616d706c65735h7363616c65}> : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %3 = "algebra.field_subtract"(%1, %2) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %4 = "algebra.constant"() <{value = "3"}> : () -> !algebra.field<"bls12-381.fr">
      %5 = "algebra.field_add"(%3, %4) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%5) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "s12h6d61705f6578616d706c65735h7363616c65", sym_visibility = "private"}> ({
    ^bb0(%arg0: !algebra.field<"bls12-381.fr">, %arg1: !algebra.field<"bls12-381.fr">):
      %0 = "algebra.field_multiply"(%arg0, %arg1) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%0) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
  }) : () -> ()
}) : () -> ()

