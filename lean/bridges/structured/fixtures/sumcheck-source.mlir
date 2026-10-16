"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "local.binding"() <{arguments = ["bls12-381.fr"], contract = "field.equal", implementation = "", sym_name = "zkl_binding_12"}> : () -> ()
    "local.realize"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">, helper = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33, sym_name = "zkl_realization_0ce8d1f6fa18ecea2634e8a590d8d4d67ef3b2266fc521419daa7adb682a678a"}> : () -> ()
    "local.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.append", implementation = "", sym_name = "zkl_binding_11"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.sub", implementation = "", sym_name = "zkl_binding_10"}> : () -> ()
    "algebra.map_realize"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">, helper = @zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5, rowwise = array<i1: true, true, false>, sym_name = "zkl_map_7aa10c0d106e0082840e035854d97e34de85744d05e64191205f7ada5a3efd95"}> : () -> ()
    "local.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.split", implementation = "", sym_name = "zkl_binding_9"}> : () -> ()
    "local.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.sum", implementation = "", sym_name = "zkl_binding_8"}> : () -> ()
    "local.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.empty", implementation = "", sym_name = "zkl_binding_7"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.mul", implementation = "", sym_name = "zkl_binding_6"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.less", implementation = "", sym_name = "zkl_binding_5"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.div", implementation = "", sym_name = "zkl_binding_4"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.equal", implementation = "", sym_name = "zkl_binding_3"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.mod", implementation = "", sym_name = "zkl_binding_2"}> : () -> ()
    "local.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.length", implementation = "", sym_name = "zkl_binding_1"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.constant", implementation = "", sym_name = "zkl_binding_0"}> : () -> ()
    "protocol.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> i1, input_roles = [["role00000000", "role00000001"], ["role00000001"], ["role00000000", "role00000001"], ["role00000001"]], output_roles = [["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071"}> ({
    ^bb0(%arg91: !algebra.field_vector<"bls12-381.fr">, %arg92: !algebra.field<"bls12-381.fr">, %arg93: ui64, %arg94: !protocol.service_ref<"random.bls12-381.fr/0">):
      %88 = "data.index"() <{value = "1"}> : () -> ui64
      %89:3 = "protocol.local_call"(%arg91, %arg93, %88) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a, role = "role00000000", site = "s1"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      %90:6 = "protocol.apply"(%89#0, %89#1, %89#2, %arg92, %arg93, %arg94) <{callee = @zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5, roles = ["role00000000", "role00000001"], site = "label_726564756365"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %91 = "protocol.local_call"(%arg91, %90#4, %90#5) <{callee = @zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc, role = "role00000001", site = "s7"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "protocol.return"(%91) : (i1) -> ()
    }) : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), sym_name = "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a"}> ({
    ^bb0(%arg88: !algebra.field_vector<"bls12-381.fr">, %arg89: ui64, %arg90: ui64):
      %87 = "local.apply"(%arg88, %arg89, %arg90) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655, site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1
      "local.if"(%87) <{site = "s1"}> ({
        "local.yield"() : () -> ()
      }, {
        "local.stop"() <{reason = "reject", site = "s1_reject"}> : () -> ()
      }) : (i1) -> ()
      "local.return"(%arg88, %arg89, %arg90) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561725h7461626c65", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1, sym_name = "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655"}> ({
    ^bb0(%arg73: !algebra.field_vector<"bls12-381.fr">, %arg74: ui64, %arg75: ui64):
      %69 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["0"], site = "s0"}> : () -> ui64
      %70 = "local.apply"(%69, %arg75) <{callee = @s3h7a6b637h696e64696365734h6c657373, site = "s1"}> : (ui64, ui64) -> i1
      %71 = "local.if"(%70, %arg74) <{site = "s3"}> ({
      ^bb0(%arg87: ui64):
        %85 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["64"], site = "s4"}> : () -> ui64
        %86 = "local.apply"(%arg87, %85) <{callee = @s3h7a6b637h696e64696365734h6c657373, site = "s5"}> : (ui64, ui64) -> i1
        "local.yield"(%86) : (i1) -> ()
      }, {
      ^bb0(%arg86: ui64):
        %84 = "local.bool_constant"() <{site = "s7", value = false}> : () -> i1
        "local.yield"(%84) : (i1) -> ()
      }) : (i1, ui64) -> i1
      %72 = "local.if"(%71, %arg73, %arg75) <{site = "s11"}> ({
      ^bb0(%arg84: !algebra.field_vector<"bls12-381.fr">, %arg85: ui64):
        %80 = "algebra.exec.vector_length"(%arg84) <{binding = @zkl_binding_1, parameters = [], site = "s12"}> : (!algebra.field_vector<"bls12-381.fr">) -> ui64
        %81 = "algebra.exec.index_mod"(%80, %arg85) <{binding = @zkl_binding_2, parameters = [], site = "s13"}> : (ui64, ui64) -> ui64
        %82 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["0"], site = "s14"}> : () -> ui64
        %83 = "algebra.exec.index_equal"(%81, %82) <{binding = @zkl_binding_3, parameters = [], site = "s15"}> : (ui64, ui64) -> i1
        "local.yield"(%83) : (i1) -> ()
      }, {
      ^bb0(%arg82: !algebra.field_vector<"bls12-381.fr">, %arg83: ui64):
        %79 = "local.bool_constant"() <{site = "s17", value = false}> : () -> i1
        "local.yield"(%79) : (i1) -> ()
      }) : (i1, !algebra.field_vector<"bls12-381.fr">, ui64) -> i1
      %73 = "local.if"(%72, %arg73, %arg74, %arg75) <{site = "s22"}> ({
      ^bb0(%arg79: !algebra.field_vector<"bls12-381.fr">, %arg80: ui64, %arg81: ui64):
        %75 = "algebra.exec.vector_length"(%arg79) <{binding = @zkl_binding_1, parameters = [], site = "s23"}> : (!algebra.field_vector<"bls12-381.fr">) -> ui64
        %76 = "algebra.exec.index_div"(%75, %arg81) <{binding = @zkl_binding_4, parameters = [], site = "s24"}> : (ui64, ui64) -> ui64
        %77 = "local.apply"(%arg80) <{callee = @s3h7a6b6311h6d756c74696c696e6561724h726f7773, site = "s25"}> : (ui64) -> ui64
        %78 = "algebra.exec.index_equal"(%76, %77) <{binding = @zkl_binding_3, parameters = [], site = "s26"}> : (ui64, ui64) -> i1
        "local.yield"(%78) : (i1) -> ()
      }, {
      ^bb0(%arg76: !algebra.field_vector<"bls12-381.fr">, %arg77: ui64, %arg78: ui64):
        %74 = "local.bool_constant"() <{site = "s28", value = false}> : () -> i1
        "local.yield"(%74) : (i1) -> ()
      }) : (i1, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1
      "local.return"(%73) : (i1) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065", []]} : () -> ()
    "local.func"() <{function_type = (ui64, ui64) -> i1, sym_name = "s3h7a6b637h696e64696365734h6c657373"}> ({
    ^bb0(%arg71: ui64, %arg72: ui64):
      %68 = "algebra.exec.index_less"(%arg71, %arg72) <{binding = @zkl_binding_5, parameters = [], site = "s0"}> : (ui64, ui64) -> i1
      "local.return"(%68) : (i1) -> ()
    }) {logical_origin = ["s3h7a6b637h696e64696365734h6c657373", []]} : () -> ()
    "local.func"() <{function_type = (ui64) -> ui64, sym_name = "s3h7a6b6311h6d756c74696c696e6561724h726f7773"}> ({
    ^bb0(%arg68: ui64):
      %61 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["64"], site = "s0"}> : () -> ui64
      %62 = "local.apply"(%arg68, %61) <{callee = @s3h7a6b637h696e64696365734h6c657373, site = "s1"}> : (ui64, ui64) -> i1
      "local.if"(%62) <{site = "s2"}> ({
        "local.yield"() : () -> ()
      }, {
        "local.stop"() <{reason = "reject", site = "s2_reject"}> : () -> ()
      }) : (i1) -> ()
      %63 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["1"], site = "s3"}> : () -> ui64
      %64 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["0"], site = "s5"}> : () -> ui64
      %65 = "local.for"(%64, %arg68, %63) <{site = "s6"}> ({
      ^bb0(%arg69: ui64, %arg70: ui64):
        %66 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["2"], site = "s7"}> : () -> ui64
        %67 = "algebra.exec.index_mul"(%arg70, %66) <{binding = @zkl_binding_6, parameters = [], site = "s8"}> : (ui64, ui64) -> ui64
        "local.yield"(%67) : (ui64) -> ()
      }) : (ui64, ui64, ui64) -> ui64
      "local.return"(%65) : (ui64) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561724h726f7773", []]} : () -> ()
    "protocol.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), input_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000000", "role00000001"], ["role00000001"]], output_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5"}> ({
    ^bb0(%arg54: !algebra.field_vector<"bls12-381.fr">, %arg55: ui64, %arg56: ui64, %arg57: !algebra.field<"bls12-381.fr">, %arg58: ui64, %arg59: !protocol.service_ref<"random.bls12-381.fr/0">):
      %33 = "func.call"(%arg54, %arg55, %arg56) <{callee = @zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %34 = "data.index"() <{value = "1"}> : () -> ui64
      %35 = "data.index_equal"(%33, %34) : (ui64, ui64) -> i1
      "protocol.guard"(%35) <{owner = "role00000000", site = "s3"}> : (i1) -> ()
      %36 = "func.call"(%arg54, %arg55, %arg56) <{callee = @zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %37 = "protocol.local_call"(%36, %arg58) <{callee = @s3h7a6b637h696e64696365734h6c657373, role = "role00000000", site = "s5"}> : (ui64, ui64) -> i1
      %38 = "arith.constant"() <{value = false}> : () -> i1
      %39 = "arith.cmpi"(%37, %38) <{predicate = 0 : i64}> : (i1, i1) -> i1
      "protocol.guard"(%39) <{owner = "role00000000", site = "s8"}> : (i1) -> ()
      %40 = "protocol.local_call"() <{callee = @zkl_411728361dd91cce996681067ff835983db4b50a2c76153019bcfb3dff123b46, role = "role00000000", site = "s10"}> : () -> !algebra.field_vector<"bls12-381.fr">
      %41 = "protocol.local_call"() <{callee = @zkl_411728361dd91cce996681067ff835983db4b50a2c76153019bcfb3dff123b46, role = "role00000001", site = "s12"}> : () -> !algebra.field_vector<"bls12-381.fr">
      %42:6 = "protocol.repeat"(%arg58, %arg54, %arg55, %arg56, %40, %41, %arg57, %arg59) <{carried = 6 : i64, carried_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"]], maximum = 2 : i64, roles = ["role00000000", "role00000001"], site = "s15"}> ({
      ^bb0(%arg60: ui64, %arg61: !algebra.field_vector<"bls12-381.fr">, %arg62: ui64, %arg63: ui64, %arg64: !algebra.field_vector<"bls12-381.fr">, %arg65: !algebra.field_vector<"bls12-381.fr">, %arg66: !algebra.field<"bls12-381.fr">, %arg67: !protocol.service_ref<"random.bls12-381.fr/0">):
        %43:2 = "protocol.local_call"(%arg61, %arg62, %arg63) <{callee = @zkl_532a609cf36a935835501ca51308940142121e647ca360843a880bf231f04aa6, role = "role00000000", site = "s16"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %44 = "protocol.exchange"(%43#0) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %45 = "protocol.restrict_roles"(%44) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %46 = "protocol.exchange"(%43#1) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_1"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %47 = "protocol.restrict_roles"(%46) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %48 = "algebra.field_add"(%45, %47) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %49 = "algebra.field_equal"(%arg66, %48) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
        "protocol.guard"(%49) <{owner = "role00000001", site = "s24"}> : (i1) -> ()
        %50 = "protocol.query"(%arg67) <{method = "draw", owner = "role00000001", site = "label_6368616c6c656e6765"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
        %51 = "protocol.exchange"(%50) <{receiver = "role00000000", sender = "role00000001", site = "label_64656c6976657279_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %52 = "protocol.restrict_roles"(%51) <{roles = ["role00000000"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %53:3 = "protocol.local_call"(%arg61, %arg62, %arg63, %52) <{callee = @zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d, role = "role00000000", site = "s29"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
        %54 = "protocol.local_call"(%arg64, %52) <{callee = @zkl_e9d4e02b4f3bba21b953f31470da5acb0cd796fdc4c7898da74fbc3f5af04e58, role = "role00000000", site = "s31"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
        %55 = "protocol.local_call"(%arg65, %50) <{callee = @zkl_e9d4e02b4f3bba21b953f31470da5acb0cd796fdc4c7898da74fbc3f5af04e58, role = "role00000001", site = "s33"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
        %56 = "algebra.constant"() <{value = "1"}> : () -> !algebra.field<"bls12-381.fr">
        %57 = "algebra.field_subtract"(%56, %50) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %58 = "algebra.field_multiply"(%57, %45) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %59 = "algebra.field_multiply"(%50, %47) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %60 = "algebra.field_add"(%58, %59) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        "protocol.yield"(%53#0, %53#1, %53#2, %54, %55, %60) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
      }) : (ui64, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      "protocol.return"(%42#3, %42#0, %42#1, %42#2, %42#4, %42#5) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64, sym_name = "zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275", sym_visibility = "private"}> ({
    ^bb0(%arg51: !algebra.field_vector<"bls12-381.fr">, %arg52: ui64, %arg53: ui64):
      "func.return"(%arg53) : (ui64) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64, sym_name = "zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94", sym_visibility = "private"}> ({
    ^bb0(%arg48: !algebra.field_vector<"bls12-381.fr">, %arg49: ui64, %arg50: ui64):
      "func.return"(%arg49) : (ui64) -> ()
    }) : () -> ()
    "local.func"() <{function_type = () -> !algebra.field_vector<"bls12-381.fr">, sym_name = "zkl_411728361dd91cce996681067ff835983db4b50a2c76153019bcfb3dff123b46"}> ({
      %32 = "algebra.exec.vector_empty"() <{binding = @zkl_binding_7, parameters = [], site = "s0"}> : () -> !algebra.field_vector<"bls12-381.fr">
      "local.return"(%32) : (!algebra.field_vector<"bls12-381.fr">) -> ()
    }) {logical_origin = ["s3h7a6b636h766563746f725h656d707479", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), sym_name = "zkl_532a609cf36a935835501ca51308940142121e647ca360843a880bf231f04aa6"}> ({
    ^bb0(%arg45: !algebra.field_vector<"bls12-381.fr">, %arg46: ui64, %arg47: ui64):
      %29:2 = "local.apply"(%arg45, %arg46, %arg47) <{callee = @zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087, site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)
      %30 = "algebra.exec.vector_sum"(%29#0) <{binding = @zkl_binding_8, parameters = [], site = "s3"}> : (!algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %31 = "algebra.exec.vector_sum"(%29#1) <{binding = @zkl_binding_8, parameters = [], site = "s5"}> : (!algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "local.return"(%30, %31) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) {logical_origin = ["s8h73756d636865636b4h73756d73", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">), sym_name = "zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087"}> ({
    ^bb0(%arg42: !algebra.field_vector<"bls12-381.fr">, %arg43: ui64, %arg44: ui64):
      %26 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["0"], site = "s0"}> : () -> ui64
      %27 = "local.apply"(%26, %arg43) <{callee = @s3h7a6b637h696e64696365734h6c657373, site = "s2"}> : (ui64, ui64) -> i1
      "local.if"(%27) <{site = "s3"}> ({
        "local.yield"() : () -> ()
      }, {
        "local.stop"() <{reason = "reject", site = "s3_reject"}> : () -> ()
      }) : (i1) -> ()
      %28:2 = "algebra.exec.vector_split"(%arg42) <{binding = @zkl_binding_9, parameters = [], site = "s5"}> : (!algebra.field_vector<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)
      "local.return"(%28#0, %28#1) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561726h68616c766573", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), sym_name = "zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d"}> ({
    ^bb0(%arg38: !algebra.field_vector<"bls12-381.fr">, %arg39: ui64, %arg40: ui64, %arg41: !algebra.field<"bls12-381.fr">):
      %22:2 = "local.apply"(%arg38, %arg39, %arg40) <{callee = @zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087, site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)
      %23 = "local.apply"(%22#0, %22#1, %arg41) <{callee = @zkl_map_7aa10c0d106e0082840e035854d97e34de85744d05e64191205f7ada5a3efd95, site = "s4"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
      %24 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["1"], site = "s7"}> : () -> ui64
      %25 = "algebra.exec.index_sub"(%arg39, %24) <{binding = @zkl_binding_10, parameters = [], site = "s8"}> : (ui64, ui64) -> ui64
      "local.return"(%23, %25, %arg40) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561729h6669785f6669727374", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5", sym_visibility = "private"}> ({
    ^bb0(%arg35: !algebra.field<"bls12-381.fr">, %arg36: !algebra.field<"bls12-381.fr">, %arg37: !algebra.field<"bls12-381.fr">):
      %19 = "algebra.field_subtract"(%arg36, %arg35) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %20 = "algebra.field_multiply"(%19, %arg37) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %21 = "algebra.field_add"(%arg35, %20) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%21) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">, sym_name = "zkl_e9d4e02b4f3bba21b953f31470da5acb0cd796fdc4c7898da74fbc3f5af04e58"}> ({
    ^bb0(%arg33: !algebra.field_vector<"bls12-381.fr">, %arg34: !algebra.field<"bls12-381.fr">):
      %18 = "algebra.exec.vector_append"(%arg33, %arg34) <{binding = @zkl_binding_11, parameters = [], site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
      "local.return"(%18) : (!algebra.field_vector<"bls12-381.fr">) -> ()
    }) {logical_origin = ["s3h7a6b636h766563746f726h617070656e64", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc"}> ({
    ^bb0(%arg24: !algebra.field_vector<"bls12-381.fr">, %arg25: !algebra.field_vector<"bls12-381.fr">, %arg26: !algebra.field<"bls12-381.fr">):
      %12 = "algebra.exec.vector_length"(%arg25) <{binding = @zkl_binding_1, parameters = [], site = "s1"}> : (!algebra.field_vector<"bls12-381.fr">) -> ui64
      %13 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["1"], site = "s2"}> : () -> ui64
      %14 = "local.apply"(%arg24, %12, %13) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655, site = "s3"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1
      %15 = "local.if"(%14, %arg24, %arg25, %arg26) <{site = "s6"}> ({
      ^bb0(%arg30: !algebra.field_vector<"bls12-381.fr">, %arg31: !algebra.field_vector<"bls12-381.fr">, %arg32: !algebra.field<"bls12-381.fr">):
        %17 = "local.apply"(%arg30, %arg31, %arg32) <{callee = @zkl_3b67bb5451d0deeed7ab9379c12e7c154a5c16946b7db9b65bc0d4be6b613f1d, site = "s7"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
        "local.yield"(%17) : (i1) -> ()
      }, {
      ^bb0(%arg27: !algebra.field_vector<"bls12-381.fr">, %arg28: !algebra.field_vector<"bls12-381.fr">, %arg29: !algebra.field<"bls12-381.fr">):
        %16 = "local.bool_constant"() <{site = "s9", value = false}> : () -> i1
        "local.yield"(%16) : (i1) -> ()
      }) : (i1, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "local.return"(%15) : (i1) -> ()
    }) {logical_origin = ["s8h73756d636865636b5h636865636b", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "zkl_3b67bb5451d0deeed7ab9379c12e7c154a5c16946b7db9b65bc0d4be6b613f1d"}> ({
    ^bb0(%arg21: !algebra.field_vector<"bls12-381.fr">, %arg22: !algebra.field_vector<"bls12-381.fr">, %arg23: !algebra.field<"bls12-381.fr">):
      %5 = "algebra.exec.vector_length"(%arg22) <{binding = @zkl_binding_1, parameters = [], site = "s1"}> : (!algebra.field_vector<"bls12-381.fr">) -> ui64
      %6 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["1"], site = "s2"}> : () -> ui64
      %7:3 = "local.apply"(%arg21, %5, %6) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a, site = "s3"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      %8:3 = "local.apply"(%7#0, %7#1, %7#2, %arg22) <{callee = @zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be, site = "s6"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      %9 = "local.apply"(%8#0, %8#1, %8#2) <{callee = @zkl_realization_0ce8d1f6fa18ecea2634e8a590d8d4d67ef3b2266fc521419daa7adb682a678a, site = "s8"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">
      %10 = "algebra.exec.vector_sum"(%9) <{binding = @zkl_binding_8, parameters = [], site = "s9"}> : (!algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %11 = "algebra.exec.field_equal"(%10, %arg23) <{binding = @zkl_binding_12, parameters = [], site = "s11"}> : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "local.return"(%11) : (i1) -> ()
    }) {logical_origin = ["s8h73756d636865636b11h636865636b5f7461626c65", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), sym_name = "zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be"}> ({
    ^bb0(%arg17: !algebra.field_vector<"bls12-381.fr">, %arg18: ui64, %arg19: ui64, %arg20: !algebra.field_vector<"bls12-381.fr">):
      %4:3 = "local.apply"(%arg17, %arg18, %arg19, %arg20) <{callee = @zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2, site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      "local.return"(%4#0, %4#1, %4#2) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e65617210h6669785f707265666978", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), sym_name = "zkl_195a79478f48dffc2a6917273d8317df0fabae786920a46fa2ac6b2737144299"}> ({
    ^bb0(%arg13: !algebra.field_vector<"bls12-381.fr">, %arg14: ui64, %arg15: ui64, %arg16: !algebra.field<"bls12-381.fr">):
      %3:3 = "local.apply"(%arg13, %arg14, %arg15, %arg16) <{callee = @zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d, site = "s2"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      "local.return"(%3#0, %3#1, %3#2) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ()
    }) {logical_origin = ["zks_50b2228592370f9a2bce2e71277fbb9bf36d691d6ece4416923708e3a0c063ae", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), sym_name = "zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2"}> ({
    ^bb0(%arg9: !algebra.field_vector<"bls12-381.fr">, %arg10: ui64, %arg11: ui64, %arg12: !algebra.field_vector<"bls12-381.fr">):
      %2:3 = "local.apply"(%arg12, %arg9, %arg10, %arg11) <{callee = @finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0, site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      "local.return"(%2#0, %2#1, %2#2) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ()
    }) {logical_origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg8: !algebra.field_vector<"bls12-381.fr">):
      %1 = "data.domain_elements"(%arg8) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%1) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), sym_name = "finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg3: !algebra.field_vector<"bls12-381.fr">, %arg4: ui64, %arg5: ui64, %arg6: !algebra.field<"bls12-381.fr">, %arg7: !algebra.field_vector<"bls12-381.fr">):
      %0:3 = "local.apply"(%arg3, %arg4, %arg5, %arg6) <{callee = @zkl_195a79478f48dffc2a6917273d8317df0fabae786920a46fa2ac6b2737144299, site = "body"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      "local.return"(%0#0, %0#1, %0#2) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ()
    }) {logical_origin = ["finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body", []]} : () -> ()
    "local.finite_fold"() <{domain = @finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_domain, function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), step = @finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body, sym_name = "finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0"}> : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">, sym_name = "zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", sym_visibility = "private"}> ({
    ^bb0(%arg0: !algebra.field_vector<"bls12-381.fr">, %arg1: ui64, %arg2: ui64):
      "func.return"(%arg0) : (!algebra.field_vector<"bls12-381.fr">) -> ()
    }) : () -> ()
  }) : () -> ()
}) : () -> ()

