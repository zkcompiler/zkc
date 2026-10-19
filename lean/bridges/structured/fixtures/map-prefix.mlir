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
    "protocol.func"() <{contracts = [], function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), input_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"]], output_roles = [["role00000000"], ["role00000000"], ["role00000000"]], roles = ["role00000000"], sym_name = "s12h6d61705f6578616d706c65736h507265666978"}> ({
    ^bb0(%arg64: !algebra.field_vector<"bls12-381.fr">, %arg65: ui64, %arg66: ui64, %arg67: !algebra.field_vector<"bls12-381.fr">):
      %47:3 = "protocol.local_call"(%arg64, %arg65, %arg66, %arg67) <{callee = @s12h6d61705f6578616d706c65736h707265666978, role = "role00000000", site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      "protocol.return"(%47#0, %47#1, %47#2) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ()
    }) : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), sym_name = "s12h6d61705f6578616d706c65736h707265666978"}> ({
    ^bb0(%arg60: !algebra.field_vector<"bls12-381.fr">, %arg61: ui64, %arg62: ui64, %arg63: !algebra.field_vector<"bls12-381.fr">):
      %42:3 = "local.apply"(%arg60, %arg61, %arg62) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a, site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      %43:3 = "local.apply"(%42#0, %42#1, %42#2, %arg63) <{callee = @zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be, site = "s1"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      %44 = "local.apply"(%43#0, %43#1, %43#2) <{callee = @zkl_realization_0ce8d1f6fa18ecea2634e8a590d8d4d67ef3b2266fc521419daa7adb682a678a, site = "s3"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">
      %45 = "local.apply"(%43#0, %43#1, %43#2) <{callee = @zkl_realization_cad7f4977a915cd19d3dc36089d25e60e203c526606ddf8f3c23bcb7a0610dc3, site = "s4"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %46 = "local.apply"(%43#0, %43#1, %43#2) <{callee = @zkl_realization_352d4a716b9eb002cfd13aef32bcb44994807d26b9eac630bc5dad5941c4b454, site = "s5"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      "local.return"(%44, %45, %46) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ()
    }) {logical_origin = ["s12h6d61705f6578616d706c65736h707265666978", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), sym_name = "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a"}> ({
    ^bb0(%arg57: !algebra.field_vector<"bls12-381.fr">, %arg58: ui64, %arg59: ui64):
      %41 = "local.apply"(%arg57, %arg58, %arg59) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655, site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1
      "local.if"(%41) <{site = "s1"}> ({
        "local.yield"() : () -> ()
      }, {
        "local.stop"() <{reason = "reject", site = "s1_reject"}> : () -> ()
      }) : (i1) -> ()
      "local.return"(%arg57, %arg58, %arg59) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561725h7461626c65", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1, sym_name = "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655"}> ({
    ^bb0(%arg42: !algebra.field_vector<"bls12-381.fr">, %arg43: ui64, %arg44: ui64):
      %23 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["0"], site = "s0"}> : () -> ui64
      %24 = "local.apply"(%23, %arg44) <{callee = @s3h7a6b637h696e64696365734h6c657373, site = "s1"}> : (ui64, ui64) -> i1
      %25 = "local.if"(%24, %arg43) <{site = "s3"}> ({
      ^bb0(%arg56: ui64):
        %39 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["64"], site = "s4"}> : () -> ui64
        %40 = "local.apply"(%arg56, %39) <{callee = @s3h7a6b637h696e64696365734h6c657373, site = "s5"}> : (ui64, ui64) -> i1
        "local.yield"(%40) : (i1) -> ()
      }, {
      ^bb0(%arg55: ui64):
        %38 = "local.bool_constant"() <{site = "s7", value = false}> : () -> i1
        "local.yield"(%38) : (i1) -> ()
      }) : (i1, ui64) -> i1
      %26 = "local.if"(%25, %arg42, %arg44) <{site = "s11"}> ({
      ^bb0(%arg53: !algebra.field_vector<"bls12-381.fr">, %arg54: ui64):
        %34 = "algebra.exec.vector_length"(%arg53) <{binding = @zkl_binding_1, parameters = [], site = "s12"}> : (!algebra.field_vector<"bls12-381.fr">) -> ui64
        %35 = "algebra.exec.index_mod"(%34, %arg54) <{binding = @zkl_binding_2, parameters = [], site = "s13"}> : (ui64, ui64) -> ui64
        %36 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["0"], site = "s14"}> : () -> ui64
        %37 = "algebra.exec.index_equal"(%35, %36) <{binding = @zkl_binding_3, parameters = [], site = "s15"}> : (ui64, ui64) -> i1
        "local.yield"(%37) : (i1) -> ()
      }, {
      ^bb0(%arg51: !algebra.field_vector<"bls12-381.fr">, %arg52: ui64):
        %33 = "local.bool_constant"() <{site = "s17", value = false}> : () -> i1
        "local.yield"(%33) : (i1) -> ()
      }) : (i1, !algebra.field_vector<"bls12-381.fr">, ui64) -> i1
      %27 = "local.if"(%26, %arg42, %arg43, %arg44) <{site = "s22"}> ({
      ^bb0(%arg48: !algebra.field_vector<"bls12-381.fr">, %arg49: ui64, %arg50: ui64):
        %29 = "algebra.exec.vector_length"(%arg48) <{binding = @zkl_binding_1, parameters = [], site = "s23"}> : (!algebra.field_vector<"bls12-381.fr">) -> ui64
        %30 = "algebra.exec.index_div"(%29, %arg50) <{binding = @zkl_binding_4, parameters = [], site = "s24"}> : (ui64, ui64) -> ui64
        %31 = "local.apply"(%arg49) <{callee = @s3h7a6b6311h6d756c74696c696e6561724h726f7773, site = "s25"}> : (ui64) -> ui64
        %32 = "algebra.exec.index_equal"(%30, %31) <{binding = @zkl_binding_3, parameters = [], site = "s26"}> : (ui64, ui64) -> i1
        "local.yield"(%32) : (i1) -> ()
      }, {
      ^bb0(%arg45: !algebra.field_vector<"bls12-381.fr">, %arg46: ui64, %arg47: ui64):
        %28 = "local.bool_constant"() <{site = "s28", value = false}> : () -> i1
        "local.yield"(%28) : (i1) -> ()
      }) : (i1, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1
      "local.return"(%27) : (i1) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065", []]} : () -> ()
    "local.func"() <{function_type = (ui64, ui64) -> i1, sym_name = "s3h7a6b637h696e64696365734h6c657373"}> ({
    ^bb0(%arg40: ui64, %arg41: ui64):
      %22 = "algebra.exec.index_less"(%arg40, %arg41) <{binding = @zkl_binding_5, parameters = [], site = "s0"}> : (ui64, ui64) -> i1
      "local.return"(%22) : (i1) -> ()
    }) {logical_origin = ["s3h7a6b637h696e64696365734h6c657373", []]} : () -> ()
    "local.func"() <{function_type = (ui64) -> ui64, sym_name = "s3h7a6b6311h6d756c74696c696e6561724h726f7773"}> ({
    ^bb0(%arg37: ui64):
      %15 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["64"], site = "s0"}> : () -> ui64
      %16 = "local.apply"(%arg37, %15) <{callee = @s3h7a6b637h696e64696365734h6c657373, site = "s1"}> : (ui64, ui64) -> i1
      "local.if"(%16) <{site = "s2"}> ({
        "local.yield"() : () -> ()
      }, {
        "local.stop"() <{reason = "reject", site = "s2_reject"}> : () -> ()
      }) : (i1) -> ()
      %17 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["1"], site = "s3"}> : () -> ui64
      %18 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["0"], site = "s5"}> : () -> ui64
      %19 = "local.for"(%18, %arg37, %17) <{site = "s6"}> ({
      ^bb0(%arg38: ui64, %arg39: ui64):
        %20 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["2"], site = "s7"}> : () -> ui64
        %21 = "algebra.exec.index_mul"(%arg39, %20) <{binding = @zkl_binding_6, parameters = [], site = "s8"}> : (ui64, ui64) -> ui64
        "local.yield"(%21) : (ui64) -> ()
      }) : (ui64, ui64, ui64) -> ui64
      "local.return"(%19) : (ui64) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561724h726f7773", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), sym_name = "zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be"}> ({
    ^bb0(%arg33: !algebra.field_vector<"bls12-381.fr">, %arg34: ui64, %arg35: ui64, %arg36: !algebra.field_vector<"bls12-381.fr">):
      %14:3 = "local.apply"(%arg33, %arg34, %arg35, %arg36) <{callee = @zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2, site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      "local.return"(%14#0, %14#1, %14#2) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e65617210h6669785f707265666978", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), sym_name = "zkl_195a79478f48dffc2a6917273d8317df0fabae786920a46fa2ac6b2737144299"}> ({
    ^bb0(%arg29: !algebra.field_vector<"bls12-381.fr">, %arg30: ui64, %arg31: ui64, %arg32: !algebra.field<"bls12-381.fr">):
      %13:3 = "local.apply"(%arg29, %arg30, %arg31, %arg32) <{callee = @zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d, site = "s2"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      "local.return"(%13#0, %13#1, %13#2) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ()
    }) {logical_origin = ["zks_50b2228592370f9a2bce2e71277fbb9bf36d691d6ece4416923708e3a0c063ae", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), sym_name = "zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d"}> ({
    ^bb0(%arg25: !algebra.field_vector<"bls12-381.fr">, %arg26: ui64, %arg27: ui64, %arg28: !algebra.field<"bls12-381.fr">):
      %9:2 = "local.apply"(%arg25, %arg26, %arg27) <{callee = @zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087, site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)
      %10 = "local.apply"(%9#0, %9#1, %arg28) <{callee = @zkl_map_7aa10c0d106e0082840e035854d97e34de85744d05e64191205f7ada5a3efd95, site = "s4"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
      %11 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["1"], site = "s7"}> : () -> ui64
      %12 = "algebra.exec.index_sub"(%arg26, %11) <{binding = @zkl_binding_7, parameters = [], site = "s8"}> : (ui64, ui64) -> ui64
      "local.return"(%10, %12, %arg27) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561729h6669785f6669727374", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">), sym_name = "zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087"}> ({
    ^bb0(%arg22: !algebra.field_vector<"bls12-381.fr">, %arg23: ui64, %arg24: ui64):
      %6 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["0"], site = "s0"}> : () -> ui64
      %7 = "local.apply"(%6, %arg23) <{callee = @s3h7a6b637h696e64696365734h6c657373, site = "s2"}> : (ui64, ui64) -> i1
      "local.if"(%7) <{site = "s3"}> ({
        "local.yield"() : () -> ()
      }, {
        "local.stop"() <{reason = "reject", site = "s3_reject"}> : () -> ()
      }) : (i1) -> ()
      %8:2 = "algebra.exec.vector_split"(%arg22) <{binding = @zkl_binding_8, parameters = [], site = "s5"}> : (!algebra.field_vector<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)
      "local.return"(%8#0, %8#1) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561726h68616c766573", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5", sym_visibility = "private"}> ({
    ^bb0(%arg19: !algebra.field<"bls12-381.fr">, %arg20: !algebra.field<"bls12-381.fr">, %arg21: !algebra.field<"bls12-381.fr">):
      %3 = "algebra.field_subtract"(%arg20, %arg19) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %4 = "algebra.field_multiply"(%3, %arg21) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %5 = "algebra.field_add"(%arg19, %4) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%5) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), sym_name = "zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2"}> ({
    ^bb0(%arg15: !algebra.field_vector<"bls12-381.fr">, %arg16: ui64, %arg17: ui64, %arg18: !algebra.field_vector<"bls12-381.fr">):
      %2:3 = "local.apply"(%arg18, %arg15, %arg16, %arg17) <{callee = @finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0, site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      "local.return"(%2#0, %2#1, %2#2) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ()
    }) {logical_origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg14: !algebra.field_vector<"bls12-381.fr">):
      %1 = "data.domain_elements"(%arg14) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%1) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), sym_name = "finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg9: !algebra.field_vector<"bls12-381.fr">, %arg10: ui64, %arg11: ui64, %arg12: !algebra.field<"bls12-381.fr">, %arg13: !algebra.field_vector<"bls12-381.fr">):
      %0:3 = "local.apply"(%arg9, %arg10, %arg11, %arg12) <{callee = @zkl_195a79478f48dffc2a6917273d8317df0fabae786920a46fa2ac6b2737144299, site = "body"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      "local.return"(%0#0, %0#1, %0#2) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ()
    }) {logical_origin = ["finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body", []]} : () -> ()
    "local.finite_fold"() <{domain = @finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_domain, function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), step = @finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body, sym_name = "finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0"}> : () -> ()
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

