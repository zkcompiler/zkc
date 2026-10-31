"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "protocol.func"() <{contracts = [["target", "selected_rows", [@zkl_aa6cad78c79deb547564210553621dc9541842525ea5d4e499acd16c8895174a, [["input", 0, "role00000001"], ["input", 1, "role00000001"]]], unit, ["output", 0, "role00000001"]]], function_type = (!algebra.field_vector<"koala-bear">, !data.sequence<!data.variant<<["tuple", [["atom", "zkc.language.pack"], ["atom", "373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a"]]]>, [<"case00000000", [i1, !algebra.field<"koala-bear">]>]>>) -> i1, input_roles = [["role00000001"], ["role00000001"]], origin = ["table_relation::CheckMembership", [["F", ["field", "koala-bear"]]]], output_roles = [["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_a640d0482dc3e22330cd86a653acff52afd2c13a23627566f0df20496d35cc9e"}> ({
    ^bb0(%arg26: !algebra.field_vector<"koala-bear">, %arg27: !data.sequence<!data.variant<<["tuple", [["atom", "zkc.language.pack"], ["atom", "373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a"]]]>, [<"case00000000", [i1, !algebra.field<"koala-bear">]>]>>):
      %23 = "protocol.local_call"(%arg26, %arg27) <{callee = @zkl_f18bdcf572d9314cf4dc17c3f79aac407e5b361f6c3a3358e8555754cc1af470, role = "role00000001", site = "s0"}> : (!algebra.field_vector<"koala-bear">, !data.sequence<!data.variant<<["tuple", [["atom", "zkc.language.pack"], ["atom", "373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a"]]]>, [<"case00000000", [i1, !algebra.field<"koala-bear">]>]>>) -> i1
      "protocol.return"(%23) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"koala-bear">, !data.sequence<!data.variant<<["tuple", [["atom", "zkc.language.pack"], ["atom", "373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a"]]]>, [<"case00000000", [i1, !algebra.field<"koala-bear">]>]>>) -> i1, sym_name = "zkf_39125dccf0dcbcb245fd5a5617424f01d0123f2a50f923aaf33eafa5487b4955", sym_visibility = "private"}> ({
    ^bb0(%arg24: !algebra.field_vector<"koala-bear">, %arg25: !data.sequence<!data.variant<<["tuple", [["atom", "zkc.language.pack"], ["atom", "373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a"]]]>, [<"case00000000", [i1, !algebra.field<"koala-bear">]>]>>):
      %22 = "func.call"(%arg24, %arg25) <{callee = @zkl_7c501270678eb45dbc3cb957141b65bbf2789c13f88546f5cc825219f80b9d98}> : (!algebra.field_vector<"koala-bear">, !data.sequence<!data.variant<<["tuple", [["atom", "zkc.language.pack"], ["atom", "373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a"]]]>, [<"case00000000", [i1, !algebra.field<"koala-bear">]>]>>) -> i1
      "func.return"(%22) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"koala-bear">, !data.sequence<!data.variant<<["tuple", [["atom", "zkc.language.pack"], ["atom", "373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a"]]]>, [<"case00000000", [i1, !algebra.field<"koala-bear">]>]>>) -> i1, sym_name = "zkl_7c501270678eb45dbc3cb957141b65bbf2789c13f88546f5cc825219f80b9d98", sym_visibility = "private"}> ({
    ^bb0(%arg22: !algebra.field_vector<"koala-bear">, %arg23: !data.sequence<!data.variant<<["tuple", [["atom", "zkc.language.pack"], ["atom", "373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a"]]]>, [<"case00000000", [i1, !algebra.field<"koala-bear">]>]>>):
      %20 = "arith.constant"() <{value = true}> : () -> i1
      %21 = "algebra.finite_fold"(%arg23, %20, %arg22) <{domain = @finite_zkl_7c501270678eb45dbc3cb957141b65bbf2789c13f88546f5cc825219f80b9d98_s2_domain, step = @finite_zkl_7c501270678eb45dbc3cb957141b65bbf2789c13f88546f5cc825219f80b9d98_s2_body}> : (!data.sequence<!data.variant<<["tuple", [["atom", "zkc.language.pack"], ["atom", "373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a"]]]>, [<"case00000000", [i1, !algebra.field<"koala-bear">]>]>>, i1, !algebra.field_vector<"koala-bear">) -> i1
      "func.return"(%21) : (i1) -> ()
    }) : () -> ()
    "data.domain"() <{function_type = (!data.sequence<!data.variant<<["tuple", [["atom", "zkc.language.pack"], ["atom", "373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a"]]]>, [<"case00000000", [i1, !algebra.field<"koala-bear">]>]>>) -> !data.domain<!data.variant<<["tuple", [["atom", "zkc.language.pack"], ["atom", "373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a"]]]>, [<"case00000000", [i1, !algebra.field<"koala-bear">]>]>>, sym_name = "finite_zkl_7c501270678eb45dbc3cb957141b65bbf2789c13f88546f5cc825219f80b9d98_s2_domain", sym_visibility = "private"}> ({
    ^bb0(%arg21: !data.sequence<!data.variant<<["tuple", [["atom", "zkc.language.pack"], ["atom", "373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a"]]]>, [<"case00000000", [i1, !algebra.field<"koala-bear">]>]>>):
      %19 = "data.domain_elements"(%arg21) : (!data.sequence<!data.variant<<["tuple", [["atom", "zkc.language.pack"], ["atom", "373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a"]]]>, [<"case00000000", [i1, !algebra.field<"koala-bear">]>]>>) -> !data.domain<!data.variant<<["tuple", [["atom", "zkc.language.pack"], ["atom", "373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a"]]]>, [<"case00000000", [i1, !algebra.field<"koala-bear">]>]>>
      "data.domain_yield"(%19) : (!data.domain<!data.variant<<["tuple", [["atom", "zkc.language.pack"], ["atom", "373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a"]]]>, [<"case00000000", [i1, !algebra.field<"koala-bear">]>]>>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (i1, !data.variant<<["tuple", [["atom", "zkc.language.pack"], ["atom", "373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a"]]]>, [<"case00000000", [i1, !algebra.field<"koala-bear">]>]>, !data.sequence<!data.variant<<["tuple", [["atom", "zkc.language.pack"], ["atom", "373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a"]]]>, [<"case00000000", [i1, !algebra.field<"koala-bear">]>]>>, !algebra.field_vector<"koala-bear">) -> i1, sym_name = "finite_zkl_7c501270678eb45dbc3cb957141b65bbf2789c13f88546f5cc825219f80b9d98_s2_body", sym_visibility = "private"}> ({
    ^bb0(%arg17: i1, %arg18: !data.variant<<["tuple", [["atom", "zkc.language.pack"], ["atom", "373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a"]]]>, [<"case00000000", [i1, !algebra.field<"koala-bear">]>]>, %arg19: !data.sequence<!data.variant<<["tuple", [["atom", "zkc.language.pack"], ["atom", "373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a"]]]>, [<"case00000000", [i1, !algebra.field<"koala-bear">]>]>>, %arg20: !algebra.field_vector<"koala-bear">):
      %16 = "data.get"(%arg18) <{index = 0 : i64}> : (!data.variant<<["tuple", [["atom", "zkc.language.pack"], ["atom", "373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a"]]]>, [<"case00000000", [i1, !algebra.field<"koala-bear">]>]>) -> i1
      %17 = "data.get"(%arg18) <{index = 1 : i64}> : (!data.variant<<["tuple", [["atom", "zkc.language.pack"], ["atom", "373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a"]]]>, [<"case00000000", [i1, !algebra.field<"koala-bear">]>]>) -> !algebra.field<"koala-bear">
      %18 = "func.call"(%arg17, %16, %17, %arg20) <{callee = @zkl_030ec014d62aacfcdf410a9867a0d256777f66bbad418c7438d2d11c402b4918}> : (i1, i1, !algebra.field<"koala-bear">, !algebra.field_vector<"koala-bear">) -> i1
      "func.return"(%18) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (i1, i1, !algebra.field<"koala-bear">, !algebra.field_vector<"koala-bear">) -> i1, sym_name = "zkl_030ec014d62aacfcdf410a9867a0d256777f66bbad418c7438d2d11c402b4918", sym_visibility = "private"}> ({
    ^bb0(%arg13: i1, %arg14: i1, %arg15: !algebra.field<"koala-bear">, %arg16: !algebra.field_vector<"koala-bear">):
      %11 = "arith.constant"() <{value = false}> : () -> i1
      %12 = "arith.cmpi"(%arg14, %11) <{predicate = 0 : i64}> : (i1, i1) -> i1
      %13 = "func.call"(%arg16, %arg15) <{callee = @zkl_d4b93c8f46d7244a48506831b7018ce4a6c0c55f2b051afd84ed04935b4accfe}> : (!algebra.field_vector<"koala-bear">, !algebra.field<"koala-bear">) -> i1
      %14 = "arith.ori"(%12, %13) : (i1, i1) -> i1
      %15 = "arith.andi"(%arg13, %14) : (i1, i1) -> i1
      "func.return"(%15) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"koala-bear">, !algebra.field<"koala-bear">) -> i1, sym_name = "zkl_d4b93c8f46d7244a48506831b7018ce4a6c0c55f2b051afd84ed04935b4accfe", sym_visibility = "private"}> ({
    ^bb0(%arg11: !algebra.field_vector<"koala-bear">, %arg12: !algebra.field<"koala-bear">):
      %9 = "arith.constant"() <{value = false}> : () -> i1
      %10 = "algebra.finite_fold"(%arg11, %9, %arg12) <{domain = @finite_zkl_d4b93c8f46d7244a48506831b7018ce4a6c0c55f2b051afd84ed04935b4accfe_s2_domain, step = @finite_zkl_d4b93c8f46d7244a48506831b7018ce4a6c0c55f2b051afd84ed04935b4accfe_s2_body}> : (!algebra.field_vector<"koala-bear">, i1, !algebra.field<"koala-bear">) -> i1
      "func.return"(%10) : (i1) -> ()
    }) : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"koala-bear">) -> !data.domain<!algebra.field<"koala-bear">>, sym_name = "finite_zkl_d4b93c8f46d7244a48506831b7018ce4a6c0c55f2b051afd84ed04935b4accfe_s2_domain", sym_visibility = "private"}> ({
    ^bb0(%arg10: !algebra.field_vector<"koala-bear">):
      %8 = "data.domain_elements"(%arg10) : (!algebra.field_vector<"koala-bear">) -> !data.domain<!algebra.field<"koala-bear">>
      "data.domain_yield"(%8) : (!data.domain<!algebra.field<"koala-bear">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (i1, !algebra.field<"koala-bear">, !algebra.field_vector<"koala-bear">, !algebra.field<"koala-bear">) -> i1, sym_name = "finite_zkl_d4b93c8f46d7244a48506831b7018ce4a6c0c55f2b051afd84ed04935b4accfe_s2_body", sym_visibility = "private"}> ({
    ^bb0(%arg6: i1, %arg7: !algebra.field<"koala-bear">, %arg8: !algebra.field_vector<"koala-bear">, %arg9: !algebra.field<"koala-bear">):
      %7 = "func.call"(%arg6, %arg7, %arg9) <{callee = @zkl_eac5bb453765e151a156f69f4baa9e6bcf2f4bd5795339381998b1dec7955769}> : (i1, !algebra.field<"koala-bear">, !algebra.field<"koala-bear">) -> i1
      "func.return"(%7) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (i1, !algebra.field<"koala-bear">, !algebra.field<"koala-bear">) -> i1, sym_name = "zkl_eac5bb453765e151a156f69f4baa9e6bcf2f4bd5795339381998b1dec7955769", sym_visibility = "private"}> ({
    ^bb0(%arg3: i1, %arg4: !algebra.field<"koala-bear">, %arg5: !algebra.field<"koala-bear">):
      %5 = "algebra.field_equal"(%arg4, %arg5) : (!algebra.field<"koala-bear">, !algebra.field<"koala-bear">) -> i1
      %6 = "arith.ori"(%arg3, %5) : (i1, i1) -> i1
      "func.return"(%6) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"koala-bear">, !data.sequence<!data.variant<<["tuple", [["atom", "zkc.language.pack"], ["atom", "373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a"]]]>, [<"case00000000", [i1, !algebra.field<"koala-bear">]>]>>) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_f18bdcf572d9314cf4dc17c3f79aac407e5b361f6c3a3358e8555754cc1af470", sym_visibility = "private"}> ({
    ^bb0(%arg0: !runtime.scope, %arg1: !algebra.field_vector<"koala-bear">, %arg2: !data.sequence<!data.variant<<["tuple", [["atom", "zkc.language.pack"], ["atom", "373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a"]]]>, [<"case00000000", [i1, !algebra.field<"koala-bear">]>]>>):
      %0 = "exec.compute"(%arg0, %arg1, %arg2) <{callee = @zkl_7c501270678eb45dbc3cb957141b65bbf2789c13f88546f5cc825219f80b9d98, site = "s0"}> : (!runtime.scope, !algebra.field_vector<"koala-bear">, !data.sequence<!data.variant<<["tuple", [["atom", "zkc.language.pack"], ["atom", "373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a"]]]>, [<"case00000000", [i1, !algebra.field<"koala-bear">]>]>>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%0)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1: i1):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%2) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%4) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.origin = ["s14h7461626c655f72656c6174696f6e16h636865636b5f6d656d62657273686970", []]} : () -> ()
    "relation.declare"() <{formula = @zkf_39125dccf0dcbcb245fd5a5617424f01d0123f2a50f923aaf33eafa5487b4955, key = "zkl_aa6cad78c79deb547564210553621dc9541842525ea5d4e499acd16c8895174a", kind = "zkc.language.formula/0", purposes = ["parameter", "statement"], revision = "dba289b723960bfd652331e56311909145a6f304eb522d7b1bed1bfe2ec730a9", signature = (!algebra.field_vector<"koala-bear">, !data.sequence<!data.variant<<["tuple", [["atom", "zkc.language.pack"], ["atom", "373a303a32313a7461626c655f72656c6174696f6e3a3a5175657279313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a"]]]>, [<"case00000000", [i1, !algebra.field<"koala-bear">]>]>>) -> i1, static_arguments = [], sym_name = "zkl_aa6cad78c79deb547564210553621dc9541842525ea5d4e499acd16c8895174a"}> : () -> ()
  }) : () -> ()
}) : () -> ()

