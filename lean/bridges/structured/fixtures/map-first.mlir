"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "local.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.split", implementation = "", sym_name = "zkl_binding_8"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.sub", implementation = "", sym_name = "zkl_binding_7"}> : () -> ()
    "algebra.map_realize"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">, helper = @zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5, rowwise = array<i1: true, true, false>, sym_name = "zkl_map_7aa10c0d106e0082840e035854d97e34de85744d05e64191205f7ada5a3efd95"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.mul", implementation = "", sym_name = "zkl_binding_6"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.less", implementation = "", sym_name = "zkl_binding_5"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.div", implementation = "", sym_name = "zkl_binding_4"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.equal", implementation = "", sym_name = "zkl_binding_3"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.mod", implementation = "", sym_name = "zkl_binding_2"}> : () -> ()
    "local.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.length", implementation = "", sym_name = "zkl_binding_1"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.constant", implementation = "", sym_name = "zkl_binding_0"}> : () -> ()
    "local.realize"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64, helper = @zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275, sym_name = "zkl_realization_352d4a716b9eb002cfd13aef32bcb44994807d26b9eac630bc5dad5941c4b454"}> : () -> ()
    "local.realize"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64, helper = @zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94, sym_name = "zkl_realization_cad7f4977a915cd19d3dc36089d25e60e203c526606ddf8f3c23bcb7a0610dc3"}> : () -> ()
    "local.realize"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">, helper = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33, sym_name = "zkl_realization_0ce8d1f6fa18ecea2634e8a590d8d4d67ef3b2266fc521419daa7adb682a678a"}> : () -> ()
    "protocol.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), input_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"]], output_roles = [["role00000000"], ["role00000000"], ["role00000000"]], roles = ["role00000000"], sym_name = "s12h6d61705f6578616d706c65735h4669727374"}> ({
    ^bb0(%arg46: !algebra.field_vector<"bls12-381.fr">, %arg47: ui64, %arg48: ui64, %arg49: !algebra.field<"bls12-381.fr">):
      %42:3 = "protocol.local_call"(%arg46, %arg47, %arg48, %arg49) <{callee = @s12h6d61705f6578616d706c65735h6669727374, role = "role00000000", site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      "protocol.return"(%42#0, %42#1, %42#2) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ()
    }) : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), sym_name = "s12h6d61705f6578616d706c65735h6669727374"}> ({
    ^bb0(%arg42: !algebra.field_vector<"bls12-381.fr">, %arg43: ui64, %arg44: ui64, %arg45: !algebra.field<"bls12-381.fr">):
      %37:3 = "local.apply"(%arg42, %arg43, %arg44) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a, site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      %38:3 = "local.apply"(%37#0, %37#1, %37#2, %arg45) <{callee = @zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d, site = "s1"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      %39 = "local.apply"(%38#0, %38#1, %38#2) <{callee = @zkl_realization_0ce8d1f6fa18ecea2634e8a590d8d4d67ef3b2266fc521419daa7adb682a678a, site = "s3"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">
      %40 = "local.apply"(%38#0, %38#1, %38#2) <{callee = @zkl_realization_cad7f4977a915cd19d3dc36089d25e60e203c526606ddf8f3c23bcb7a0610dc3, site = "s4"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %41 = "local.apply"(%38#0, %38#1, %38#2) <{callee = @zkl_realization_352d4a716b9eb002cfd13aef32bcb44994807d26b9eac630bc5dad5941c4b454, site = "s5"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      "local.return"(%39, %40, %41) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ()
    }) {logical_origin = ["s12h6d61705f6578616d706c65735h6669727374", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), sym_name = "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a"}> ({
    ^bb0(%arg39: !algebra.field_vector<"bls12-381.fr">, %arg40: ui64, %arg41: ui64):
      %36 = "local.apply"(%arg39, %arg40, %arg41) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655, site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1
      "local.if"(%36) <{site = "s1"}> ({
        "local.yield"() : () -> ()
      }, {
        "local.stop"() <{reason = "reject", site = "s1_reject"}> : () -> ()
      }) : (i1) -> ()
      "local.return"(%arg39, %arg40, %arg41) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561725h7461626c65", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1, sym_name = "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655"}> ({
    ^bb0(%arg24: !algebra.field_vector<"bls12-381.fr">, %arg25: ui64, %arg26: ui64):
      %18 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["0"], site = "s0"}> : () -> ui64
      %19 = "local.apply"(%18, %arg26) <{callee = @s3h7a6b637h696e64696365734h6c657373, site = "s1"}> : (ui64, ui64) -> i1
      %20 = "local.if"(%19, %arg25) <{site = "s3"}> ({
      ^bb0(%arg38: ui64):
        %34 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["64"], site = "s4"}> : () -> ui64
        %35 = "local.apply"(%arg38, %34) <{callee = @s3h7a6b637h696e64696365734h6c657373, site = "s5"}> : (ui64, ui64) -> i1
        "local.yield"(%35) : (i1) -> ()
      }, {
      ^bb0(%arg37: ui64):
        %33 = "local.bool_constant"() <{site = "s7", value = false}> : () -> i1
        "local.yield"(%33) : (i1) -> ()
      }) : (i1, ui64) -> i1
      %21 = "local.if"(%20, %arg24, %arg26) <{site = "s11"}> ({
      ^bb0(%arg35: !algebra.field_vector<"bls12-381.fr">, %arg36: ui64):
        %29 = "algebra.exec.vector_length"(%arg35) <{binding = @zkl_binding_1, parameters = [], site = "s12"}> : (!algebra.field_vector<"bls12-381.fr">) -> ui64
        %30 = "algebra.exec.index_mod"(%29, %arg36) <{binding = @zkl_binding_2, parameters = [], site = "s13"}> : (ui64, ui64) -> ui64
        %31 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["0"], site = "s14"}> : () -> ui64
        %32 = "algebra.exec.index_equal"(%30, %31) <{binding = @zkl_binding_3, parameters = [], site = "s15"}> : (ui64, ui64) -> i1
        "local.yield"(%32) : (i1) -> ()
      }, {
      ^bb0(%arg33: !algebra.field_vector<"bls12-381.fr">, %arg34: ui64):
        %28 = "local.bool_constant"() <{site = "s17", value = false}> : () -> i1
        "local.yield"(%28) : (i1) -> ()
      }) : (i1, !algebra.field_vector<"bls12-381.fr">, ui64) -> i1
      %22 = "local.if"(%21, %arg24, %arg25, %arg26) <{site = "s22"}> ({
      ^bb0(%arg30: !algebra.field_vector<"bls12-381.fr">, %arg31: ui64, %arg32: ui64):
        %24 = "algebra.exec.vector_length"(%arg30) <{binding = @zkl_binding_1, parameters = [], site = "s23"}> : (!algebra.field_vector<"bls12-381.fr">) -> ui64
        %25 = "algebra.exec.index_div"(%24, %arg32) <{binding = @zkl_binding_4, parameters = [], site = "s24"}> : (ui64, ui64) -> ui64
        %26 = "local.apply"(%arg31) <{callee = @s3h7a6b6311h6d756c74696c696e6561724h726f7773, site = "s25"}> : (ui64) -> ui64
        %27 = "algebra.exec.index_equal"(%25, %26) <{binding = @zkl_binding_3, parameters = [], site = "s26"}> : (ui64, ui64) -> i1
        "local.yield"(%27) : (i1) -> ()
      }, {
      ^bb0(%arg27: !algebra.field_vector<"bls12-381.fr">, %arg28: ui64, %arg29: ui64):
        %23 = "local.bool_constant"() <{site = "s28", value = false}> : () -> i1
        "local.yield"(%23) : (i1) -> ()
      }) : (i1, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1
      "local.return"(%22) : (i1) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065", []]} : () -> ()
    "local.func"() <{function_type = (ui64, ui64) -> i1, sym_name = "s3h7a6b637h696e64696365734h6c657373"}> ({
    ^bb0(%arg22: ui64, %arg23: ui64):
      %17 = "algebra.exec.index_less"(%arg22, %arg23) <{binding = @zkl_binding_5, parameters = [], site = "s0"}> : (ui64, ui64) -> i1
      "local.return"(%17) : (i1) -> ()
    }) {logical_origin = ["s3h7a6b637h696e64696365734h6c657373", []]} : () -> ()
    "local.func"() <{function_type = (ui64) -> ui64, sym_name = "s3h7a6b6311h6d756c74696c696e6561724h726f7773"}> ({
    ^bb0(%arg19: ui64):
      %10 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["64"], site = "s0"}> : () -> ui64
      %11 = "local.apply"(%arg19, %10) <{callee = @s3h7a6b637h696e64696365734h6c657373, site = "s1"}> : (ui64, ui64) -> i1
      "local.if"(%11) <{site = "s2"}> ({
        "local.yield"() : () -> ()
      }, {
        "local.stop"() <{reason = "reject", site = "s2_reject"}> : () -> ()
      }) : (i1) -> ()
      %12 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["1"], site = "s3"}> : () -> ui64
      %13 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["0"], site = "s5"}> : () -> ui64
      %14 = "local.for"(%13, %arg19, %12) <{site = "s6"}> ({
      ^bb0(%arg20: ui64, %arg21: ui64):
        %15 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["2"], site = "s7"}> : () -> ui64
        %16 = "algebra.exec.index_mul"(%arg21, %15) <{binding = @zkl_binding_6, parameters = [], site = "s8"}> : (ui64, ui64) -> ui64
        "local.yield"(%16) : (ui64) -> ()
      }) : (ui64, ui64, ui64) -> ui64
      "local.return"(%14) : (ui64) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561724h726f7773", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), sym_name = "zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d"}> ({
    ^bb0(%arg15: !algebra.field_vector<"bls12-381.fr">, %arg16: ui64, %arg17: ui64, %arg18: !algebra.field<"bls12-381.fr">):
      %6:2 = "local.apply"(%arg15, %arg16, %arg17) <{callee = @zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087, site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)
      %7 = "local.apply"(%6#0, %6#1, %arg18) <{callee = @zkl_map_7aa10c0d106e0082840e035854d97e34de85744d05e64191205f7ada5a3efd95, site = "s4"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
      %8 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["1"], site = "s7"}> : () -> ui64
      %9 = "algebra.exec.index_sub"(%arg16, %8) <{binding = @zkl_binding_7, parameters = [], site = "s8"}> : (ui64, ui64) -> ui64
      "local.return"(%7, %9, %arg17) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561729h6669785f6669727374", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">), sym_name = "zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087"}> ({
    ^bb0(%arg12: !algebra.field_vector<"bls12-381.fr">, %arg13: ui64, %arg14: ui64):
      %3 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["0"], site = "s0"}> : () -> ui64
      %4 = "local.apply"(%3, %arg13) <{callee = @s3h7a6b637h696e64696365734h6c657373, site = "s2"}> : (ui64, ui64) -> i1
      "local.if"(%4) <{site = "s3"}> ({
        "local.yield"() : () -> ()
      }, {
        "local.stop"() <{reason = "reject", site = "s3_reject"}> : () -> ()
      }) : (i1) -> ()
      %5:2 = "algebra.exec.vector_split"(%arg12) <{binding = @zkl_binding_8, parameters = [], site = "s5"}> : (!algebra.field_vector<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)
      "local.return"(%5#0, %5#1) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561726h68616c766573", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5", sym_visibility = "private"}> ({
    ^bb0(%arg9: !algebra.field<"bls12-381.fr">, %arg10: !algebra.field<"bls12-381.fr">, %arg11: !algebra.field<"bls12-381.fr">):
      %0 = "algebra.field_subtract"(%arg10, %arg9) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %1 = "algebra.field_multiply"(%0, %arg11) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %2 = "algebra.field_add"(%arg9, %1) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%2) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">, sym_name = "zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", sym_visibility = "private"}> ({
    ^bb0(%arg6: !algebra.field_vector<"bls12-381.fr">, %arg7: ui64, %arg8: ui64):
      "func.return"(%arg6) : (!algebra.field_vector<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64, sym_name = "zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94", sym_visibility = "private"}> ({
    ^bb0(%arg3: !algebra.field_vector<"bls12-381.fr">, %arg4: ui64, %arg5: ui64):
      "func.return"(%arg4) : (ui64) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64, sym_name = "zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275", sym_visibility = "private"}> ({
    ^bb0(%arg0: !algebra.field_vector<"bls12-381.fr">, %arg1: ui64, %arg2: ui64):
      "func.return"(%arg2) : (ui64) -> ()
    }) : () -> ()
  }) : () -> ()
}) : () -> ()

