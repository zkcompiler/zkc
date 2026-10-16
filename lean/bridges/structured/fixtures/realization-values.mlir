"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "local.realize"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">, helper = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33, sym_name = "zkl_realization_0ce8d1f6fa18ecea2634e8a590d8d4d67ef3b2266fc521419daa7adb682a678a"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.mul", implementation = "", sym_name = "zkl_binding_6"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.less", implementation = "", sym_name = "zkl_binding_5"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.div", implementation = "", sym_name = "zkl_binding_4"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.equal", implementation = "", sym_name = "zkl_binding_3"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.mod", implementation = "", sym_name = "zkl_binding_2"}> : () -> ()
    "local.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.length", implementation = "", sym_name = "zkl_binding_1"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.constant", implementation = "", sym_name = "zkl_binding_0"}> : () -> ()
    "protocol.func"() <{contracts = [], function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">, input_roles = [["role00000000"], ["role00000000"], ["role00000000"]], output_roles = [["role00000000"]], roles = ["role00000000"], sym_name = "s12h6d61705f6578616d706c657313h5265616c697a6556616c756573"}> ({
    ^bb0(%arg29: !algebra.field_vector<"bls12-381.fr">, %arg30: ui64, %arg31: ui64):
      %28:3 = "protocol.local_call"(%arg29, %arg30, %arg31) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a, role = "role00000000", site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      %29 = "protocol.local_call"(%28#0, %28#1, %28#2) <{callee = @s12h6d61705f6578616d706c657314h7265616c697a655f76616c756573, role = "role00000000", site = "s2"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">
      "protocol.return"(%29) : (!algebra.field_vector<"bls12-381.fr">) -> ()
    }) : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), sym_name = "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a"}> ({
    ^bb0(%arg26: !algebra.field_vector<"bls12-381.fr">, %arg27: ui64, %arg28: ui64):
      %27 = "local.apply"(%arg26, %arg27, %arg28) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655, site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1
      "local.if"(%27) <{site = "s1"}> ({
        "local.yield"() : () -> ()
      }, {
        "local.stop"() <{reason = "reject", site = "s1_reject"}> : () -> ()
      }) : (i1) -> ()
      "local.return"(%arg26, %arg27, %arg28) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561725h7461626c65", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1, sym_name = "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655"}> ({
    ^bb0(%arg11: !algebra.field_vector<"bls12-381.fr">, %arg12: ui64, %arg13: ui64):
      %9 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["0"], site = "s0"}> : () -> ui64
      %10 = "local.apply"(%9, %arg13) <{callee = @s3h7a6b637h696e64696365734h6c657373, site = "s1"}> : (ui64, ui64) -> i1
      %11 = "local.if"(%10, %arg12) <{site = "s3"}> ({
      ^bb0(%arg25: ui64):
        %25 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["64"], site = "s4"}> : () -> ui64
        %26 = "local.apply"(%arg25, %25) <{callee = @s3h7a6b637h696e64696365734h6c657373, site = "s5"}> : (ui64, ui64) -> i1
        "local.yield"(%26) : (i1) -> ()
      }, {
      ^bb0(%arg24: ui64):
        %24 = "local.bool_constant"() <{site = "s7", value = false}> : () -> i1
        "local.yield"(%24) : (i1) -> ()
      }) : (i1, ui64) -> i1
      %12 = "local.if"(%11, %arg11, %arg13) <{site = "s11"}> ({
      ^bb0(%arg22: !algebra.field_vector<"bls12-381.fr">, %arg23: ui64):
        %20 = "algebra.exec.vector_length"(%arg22) <{binding = @zkl_binding_1, parameters = [], site = "s12"}> : (!algebra.field_vector<"bls12-381.fr">) -> ui64
        %21 = "algebra.exec.index_mod"(%20, %arg23) <{binding = @zkl_binding_2, parameters = [], site = "s13"}> : (ui64, ui64) -> ui64
        %22 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["0"], site = "s14"}> : () -> ui64
        %23 = "algebra.exec.index_equal"(%21, %22) <{binding = @zkl_binding_3, parameters = [], site = "s15"}> : (ui64, ui64) -> i1
        "local.yield"(%23) : (i1) -> ()
      }, {
      ^bb0(%arg20: !algebra.field_vector<"bls12-381.fr">, %arg21: ui64):
        %19 = "local.bool_constant"() <{site = "s17", value = false}> : () -> i1
        "local.yield"(%19) : (i1) -> ()
      }) : (i1, !algebra.field_vector<"bls12-381.fr">, ui64) -> i1
      %13 = "local.if"(%12, %arg11, %arg12, %arg13) <{site = "s22"}> ({
      ^bb0(%arg17: !algebra.field_vector<"bls12-381.fr">, %arg18: ui64, %arg19: ui64):
        %15 = "algebra.exec.vector_length"(%arg17) <{binding = @zkl_binding_1, parameters = [], site = "s23"}> : (!algebra.field_vector<"bls12-381.fr">) -> ui64
        %16 = "algebra.exec.index_div"(%15, %arg19) <{binding = @zkl_binding_4, parameters = [], site = "s24"}> : (ui64, ui64) -> ui64
        %17 = "local.apply"(%arg18) <{callee = @s3h7a6b6311h6d756c74696c696e6561724h726f7773, site = "s25"}> : (ui64) -> ui64
        %18 = "algebra.exec.index_equal"(%16, %17) <{binding = @zkl_binding_3, parameters = [], site = "s26"}> : (ui64, ui64) -> i1
        "local.yield"(%18) : (i1) -> ()
      }, {
      ^bb0(%arg14: !algebra.field_vector<"bls12-381.fr">, %arg15: ui64, %arg16: ui64):
        %14 = "local.bool_constant"() <{site = "s28", value = false}> : () -> i1
        "local.yield"(%14) : (i1) -> ()
      }) : (i1, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1
      "local.return"(%13) : (i1) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065", []]} : () -> ()
    "local.func"() <{function_type = (ui64, ui64) -> i1, sym_name = "s3h7a6b637h696e64696365734h6c657373"}> ({
    ^bb0(%arg9: ui64, %arg10: ui64):
      %8 = "algebra.exec.index_less"(%arg9, %arg10) <{binding = @zkl_binding_5, parameters = [], site = "s0"}> : (ui64, ui64) -> i1
      "local.return"(%8) : (i1) -> ()
    }) {logical_origin = ["s3h7a6b637h696e64696365734h6c657373", []]} : () -> ()
    "local.func"() <{function_type = (ui64) -> ui64, sym_name = "s3h7a6b6311h6d756c74696c696e6561724h726f7773"}> ({
    ^bb0(%arg6: ui64):
      %1 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["64"], site = "s0"}> : () -> ui64
      %2 = "local.apply"(%arg6, %1) <{callee = @s3h7a6b637h696e64696365734h6c657373, site = "s1"}> : (ui64, ui64) -> i1
      "local.if"(%2) <{site = "s2"}> ({
        "local.yield"() : () -> ()
      }, {
        "local.stop"() <{reason = "reject", site = "s2_reject"}> : () -> ()
      }) : (i1) -> ()
      %3 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["1"], site = "s3"}> : () -> ui64
      %4 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["0"], site = "s5"}> : () -> ui64
      %5 = "local.for"(%4, %arg6, %3) <{site = "s6"}> ({
      ^bb0(%arg7: ui64, %arg8: ui64):
        %6 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["2"], site = "s7"}> : () -> ui64
        %7 = "algebra.exec.index_mul"(%arg8, %6) <{binding = @zkl_binding_6, parameters = [], site = "s8"}> : (ui64, ui64) -> ui64
        "local.yield"(%7) : (ui64) -> ()
      }) : (ui64, ui64, ui64) -> ui64
      "local.return"(%5) : (ui64) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561724h726f7773", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">, sym_name = "s12h6d61705f6578616d706c657314h7265616c697a655f76616c756573"}> ({
    ^bb0(%arg3: !algebra.field_vector<"bls12-381.fr">, %arg4: ui64, %arg5: ui64):
      %0 = "local.apply"(%arg3, %arg4, %arg5) <{callee = @zkl_realization_0ce8d1f6fa18ecea2634e8a590d8d4d67ef3b2266fc521419daa7adb682a678a, site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">
      "local.return"(%0) : (!algebra.field_vector<"bls12-381.fr">) -> ()
    }) {logical_origin = ["s12h6d61705f6578616d706c657314h7265616c697a655f76616c756573", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">, sym_name = "zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", sym_visibility = "private"}> ({
    ^bb0(%arg0: !algebra.field_vector<"bls12-381.fr">, %arg1: ui64, %arg2: ui64):
      "func.return"(%arg0) : (!algebra.field_vector<"bls12-381.fr">) -> ()
    }) : () -> ()
  }) : () -> ()
}) : () -> ()

