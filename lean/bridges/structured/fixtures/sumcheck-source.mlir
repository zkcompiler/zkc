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
    "protocol.func"() <{contracts = [["input", "shape", [@zkl_733a9984be750c90a7e40f8fc81c10a284cb9ecaf745c62024f07f1a3806a10c, [["input", 0, "role00000001"], ["input", 2, "role00000001"]]], unit, unit], ["target", "public_sum", [@zkl_1c2e12f894c2f4b39d38adc87f1dedbaf7856eb6985dba89eb2261c88030aef2, [["input", 0, "role00000001"], ["input", 1, "role00000001"]]], unit, ["output", 0, "role00000001"]]], function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> i1, input_roles = [["role00000000", "role00000001"], ["role00000001"], ["role00000000", "role00000001"], ["role00000001"]], origin = ["sumcheck::Sumcheck", [["F", ["field", "bls12-381.fr"]], ["Max", ["nat", "2"]]]], output_roles = [["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071"}> ({
    ^bb0(%arg106: !algebra.field_vector<"bls12-381.fr">, %arg107: !algebra.field<"bls12-381.fr">, %arg108: ui64, %arg109: !protocol.service_ref<"random.bls12-381.fr/0">):
      %105 = "data.index"() <{value = "1"}> : () -> ui64
      %106:3 = "protocol.local_call"(%arg106, %arg108, %105) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a, role = "role00000000", site = "s1"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      %107:6 = "protocol.apply"(%106#0, %106#1, %106#2, %arg107, %arg108, %arg109) <{callee = @zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5, roles = ["role00000000", "role00000001"], site = "label_726564756365"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %108 = "protocol.local_call"(%arg106, %107#4, %107#5) <{callee = @zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc, role = "role00000001", site = "s7"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "protocol.return"(%108) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64) -> i1, sym_name = "zkf_9ca6c98faa0d00ed80eb608a89db1544ad71443a8944af6ac99e6fd78cb3660b", sym_visibility = "private"}> ({
    ^bb0(%arg104: !algebra.field_vector<"bls12-381.fr">, %arg105: ui64):
      %98 = "data.dim"(%arg104) <{axis = 0 : i64}> : (!algebra.field_vector<"bls12-381.fr">) -> ui64
      %99 = "data.index_power_of_two"(%98, %arg105) : (ui64, ui64) -> i1
      %100 = "data.index"() <{value = "2"}> : () -> ui64
      %101 = "data.index_less"(%100, %arg105) : (ui64, ui64) -> i1
      %102 = "arith.constant"() <{value = false}> : () -> i1
      %103 = "arith.cmpi"(%101, %102) <{predicate = 0 : i64}> : (i1, i1) -> i1
      %104 = "arith.andi"(%99, %103) : (i1, i1) -> i1
      "func.return"(%104) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "zkf_116f3285742dd1275b8149c69b78a6713cd6256a8af715be7c346da1c793a766", sym_visibility = "private"}> ({
    ^bb0(%arg102: !algebra.field_vector<"bls12-381.fr">, %arg103: !algebra.field<"bls12-381.fr">):
      %96 = "func.call"(%arg102) <{callee = @zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e}> : (!algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %97 = "algebra.field_equal"(%arg103, %96) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "func.return"(%97) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e", sym_visibility = "private"}> ({
    ^bb0(%arg101: !algebra.field_vector<"bls12-381.fr">):
      %94 = "algebra.constant"() <{value = "0"}> : () -> !algebra.field<"bls12-381.fr">
      %95 = "algebra.finite_fold"(%arg101, %94) <{domain = @finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_domain, step = @finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_body}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%95) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_domain", sym_visibility = "private"}> ({
    ^bb0(%arg100: !algebra.field_vector<"bls12-381.fr">):
      %93 = "data.domain_elements"(%arg100) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%93) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_body", sym_visibility = "private"}> ({
    ^bb0(%arg97: !algebra.field<"bls12-381.fr">, %arg98: !algebra.field<"bls12-381.fr">, %arg99: !algebra.field_vector<"bls12-381.fr">):
      %92 = "func.call"(%arg97, %arg98) <{callee = @zkl_3fc17a64a5bb6e75192d0a1362e9954f0d434a10d0f93e319db6b516835a1005}> : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%92) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_3fc17a64a5bb6e75192d0a1362e9954f0d434a10d0f93e319db6b516835a1005", sym_visibility = "private"}> ({
    ^bb0(%arg95: !algebra.field<"bls12-381.fr">, %arg96: !algebra.field<"bls12-381.fr">):
      %91 = "algebra.field_add"(%arg95, %arg96) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%91) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), sym_name = "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a"}> ({
    ^bb0(%arg92: !algebra.field_vector<"bls12-381.fr">, %arg93: ui64, %arg94: ui64):
      %90 = "local.apply"(%arg92, %arg93, %arg94) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655, site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1
      "local.if"(%90) <{site = "s1"}> ({
        "local.yield"() : () -> ()
      }, {
        "local.stop"() <{reason = "reject", site = "s1_reject"}> : () -> ()
      }) : (i1) -> ()
      "local.return"(%arg92, %arg93, %arg94) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561725h7461626c65", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1, sym_name = "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655"}> ({
    ^bb0(%arg77: !algebra.field_vector<"bls12-381.fr">, %arg78: ui64, %arg79: ui64):
      %72 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["0"], site = "s0"}> : () -> ui64
      %73 = "local.apply"(%72, %arg79) <{callee = @s3h7a6b637h696e64696365734h6c657373, site = "s1"}> : (ui64, ui64) -> i1
      %74 = "local.if"(%73, %arg78) <{site = "s3"}> ({
      ^bb0(%arg91: ui64):
        %88 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["64"], site = "s4"}> : () -> ui64
        %89 = "local.apply"(%arg91, %88) <{callee = @s3h7a6b637h696e64696365734h6c657373, site = "s5"}> : (ui64, ui64) -> i1
        "local.yield"(%89) : (i1) -> ()
      }, {
      ^bb0(%arg90: ui64):
        %87 = "local.bool_constant"() <{site = "s7", value = false}> : () -> i1
        "local.yield"(%87) : (i1) -> ()
      }) : (i1, ui64) -> i1
      %75 = "local.if"(%74, %arg77, %arg79) <{site = "s11"}> ({
      ^bb0(%arg88: !algebra.field_vector<"bls12-381.fr">, %arg89: ui64):
        %83 = "algebra.exec.vector_length"(%arg88) <{binding = @zkl_binding_1, parameters = [], site = "s12"}> : (!algebra.field_vector<"bls12-381.fr">) -> ui64
        %84 = "algebra.exec.index_mod"(%83, %arg89) <{binding = @zkl_binding_2, parameters = [], site = "s13"}> : (ui64, ui64) -> ui64
        %85 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["0"], site = "s14"}> : () -> ui64
        %86 = "algebra.exec.index_equal"(%84, %85) <{binding = @zkl_binding_3, parameters = [], site = "s15"}> : (ui64, ui64) -> i1
        "local.yield"(%86) : (i1) -> ()
      }, {
      ^bb0(%arg86: !algebra.field_vector<"bls12-381.fr">, %arg87: ui64):
        %82 = "local.bool_constant"() <{site = "s17", value = false}> : () -> i1
        "local.yield"(%82) : (i1) -> ()
      }) : (i1, !algebra.field_vector<"bls12-381.fr">, ui64) -> i1
      %76 = "local.if"(%75, %arg77, %arg78, %arg79) <{site = "s22"}> ({
      ^bb0(%arg83: !algebra.field_vector<"bls12-381.fr">, %arg84: ui64, %arg85: ui64):
        %78 = "algebra.exec.vector_length"(%arg83) <{binding = @zkl_binding_1, parameters = [], site = "s23"}> : (!algebra.field_vector<"bls12-381.fr">) -> ui64
        %79 = "algebra.exec.index_div"(%78, %arg85) <{binding = @zkl_binding_4, parameters = [], site = "s24"}> : (ui64, ui64) -> ui64
        %80 = "local.apply"(%arg84) <{callee = @s3h7a6b6311h6d756c74696c696e6561724h726f7773, site = "s25"}> : (ui64) -> ui64
        %81 = "algebra.exec.index_equal"(%79, %80) <{binding = @zkl_binding_3, parameters = [], site = "s26"}> : (ui64, ui64) -> i1
        "local.yield"(%81) : (i1) -> ()
      }, {
      ^bb0(%arg80: !algebra.field_vector<"bls12-381.fr">, %arg81: ui64, %arg82: ui64):
        %77 = "local.bool_constant"() <{site = "s28", value = false}> : () -> i1
        "local.yield"(%77) : (i1) -> ()
      }) : (i1, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1
      "local.return"(%76) : (i1) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065", []]} : () -> ()
    "local.func"() <{function_type = (ui64, ui64) -> i1, sym_name = "s3h7a6b637h696e64696365734h6c657373"}> ({
    ^bb0(%arg75: ui64, %arg76: ui64):
      %71 = "algebra.exec.index_less"(%arg75, %arg76) <{binding = @zkl_binding_5, parameters = [], site = "s0"}> : (ui64, ui64) -> i1
      "local.return"(%71) : (i1) -> ()
    }) {logical_origin = ["s3h7a6b637h696e64696365734h6c657373", []]} : () -> ()
    "local.func"() <{function_type = (ui64) -> ui64, sym_name = "s3h7a6b6311h6d756c74696c696e6561724h726f7773"}> ({
    ^bb0(%arg72: ui64):
      %64 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["64"], site = "s0"}> : () -> ui64
      %65 = "local.apply"(%arg72, %64) <{callee = @s3h7a6b637h696e64696365734h6c657373, site = "s1"}> : (ui64, ui64) -> i1
      "local.if"(%65) <{site = "s2"}> ({
        "local.yield"() : () -> ()
      }, {
        "local.stop"() <{reason = "reject", site = "s2_reject"}> : () -> ()
      }) : (i1) -> ()
      %66 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["1"], site = "s3"}> : () -> ui64
      %67 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["0"], site = "s5"}> : () -> ui64
      %68 = "local.for"(%67, %arg72, %66) <{site = "s6"}> ({
      ^bb0(%arg73: ui64, %arg74: ui64):
        %69 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["2"], site = "s7"}> : () -> ui64
        %70 = "algebra.exec.index_mul"(%arg74, %69) <{binding = @zkl_binding_6, parameters = [], site = "s8"}> : (ui64, ui64) -> ui64
        "local.yield"(%70) : (ui64) -> ()
      }) : (ui64, ui64, ui64) -> ui64
      "local.return"(%68) : (ui64) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561724h726f7773", []]} : () -> ()
    "protocol.func"() <{contracts = [["input", "initial_sum", [@zkl_11c80248216cbe579879aabc5c6f64d5f465a4db68261d6da29eab7c94d7679c, [["input", 0, "role00000000"], ["input", 1, "role00000000"], ["input", 2, "role00000000"], ["input", 3, "role00000001"]]], unit, unit]], function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), input_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000000", "role00000001"], ["role00000001"]], origin = ["sumcheck::Reduce", [["F", ["field", "bls12-381.fr"]], ["Max", ["nat", "2"]]]], output_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5"}> ({
    ^bb0(%arg58: !algebra.field_vector<"bls12-381.fr">, %arg59: ui64, %arg60: ui64, %arg61: !algebra.field<"bls12-381.fr">, %arg62: ui64, %arg63: !protocol.service_ref<"random.bls12-381.fr/0">):
      %36 = "func.call"(%arg58, %arg59, %arg60) <{callee = @zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %37 = "data.index"() <{value = "1"}> : () -> ui64
      %38 = "data.index_equal"(%36, %37) : (ui64, ui64) -> i1
      "protocol.guard"(%38) <{owner = "role00000000", site = "s3"}> : (i1) -> ()
      %39 = "func.call"(%arg58, %arg59, %arg60) <{callee = @zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %40 = "protocol.local_call"(%39, %arg62) <{callee = @s3h7a6b637h696e64696365734h6c657373, role = "role00000000", site = "s5"}> : (ui64, ui64) -> i1
      %41 = "arith.constant"() <{value = false}> : () -> i1
      %42 = "arith.cmpi"(%40, %41) <{predicate = 0 : i64}> : (i1, i1) -> i1
      "protocol.guard"(%42) <{owner = "role00000000", site = "s8"}> : (i1) -> ()
      %43 = "protocol.local_call"() <{callee = @zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f, role = "role00000000", site = "s10"}> : () -> !algebra.field_vector<"bls12-381.fr">
      %44 = "protocol.local_call"() <{callee = @zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f, role = "role00000001", site = "s12"}> : () -> !algebra.field_vector<"bls12-381.fr">
      %45:6 = "protocol.repeat"(%arg62, %arg58, %arg59, %arg60, %43, %44, %arg61, %arg63) <{carried = 6 : i64, carried_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"]], maximum = 2 : i64, roles = ["role00000000", "role00000001"], site = "s15"}> ({
      ^bb0(%arg64: ui64, %arg65: !algebra.field_vector<"bls12-381.fr">, %arg66: ui64, %arg67: ui64, %arg68: !algebra.field_vector<"bls12-381.fr">, %arg69: !algebra.field_vector<"bls12-381.fr">, %arg70: !algebra.field<"bls12-381.fr">, %arg71: !protocol.service_ref<"random.bls12-381.fr/0">):
        %46:2 = "protocol.local_call"(%arg65, %arg66, %arg67) <{callee = @zkl_532a609cf36a935835501ca51308940142121e647ca360843a880bf231f04aa6, role = "role00000000", site = "s16"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %47 = "protocol.exchange"(%46#0) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %48 = "protocol.restrict_roles"(%47) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %49 = "protocol.exchange"(%46#1) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_1"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %50 = "protocol.restrict_roles"(%49) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %51 = "algebra.field_add"(%48, %50) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %52 = "algebra.field_equal"(%arg70, %51) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
        "protocol.guard"(%52) <{owner = "role00000001", site = "s24"}> : (i1) -> ()
        %53 = "protocol.query"(%arg71) <{method = "draw", owner = "role00000001", site = "label_6368616c6c656e6765"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
        %54 = "protocol.exchange"(%53) <{receiver = "role00000000", sender = "role00000001", site = "label_64656c6976657279_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %55 = "protocol.restrict_roles"(%54) <{roles = ["role00000000"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %56:3 = "protocol.local_call"(%arg65, %arg66, %arg67, %55) <{callee = @zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d, role = "role00000000", site = "s29"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
        %57 = "protocol.local_call"(%arg68, %55) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000000", site = "s31"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
        %58 = "protocol.local_call"(%arg69, %53) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000001", site = "s33"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
        %59 = "algebra.constant"() <{value = "1"}> : () -> !algebra.field<"bls12-381.fr">
        %60 = "algebra.field_subtract"(%59, %53) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %61 = "algebra.field_multiply"(%60, %48) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %62 = "algebra.field_multiply"(%53, %50) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %63 = "algebra.field_add"(%61, %62) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        "protocol.yield"(%56#0, %56#1, %56#2, %57, %58, %63) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
      }) : (ui64, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      "protocol.return"(%45#3, %45#0, %45#1, %45#2, %45#4, %45#5) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "zkf_654a0e58b11e83f398996b9e830df00890bec0f8dc08a65c5750d6d9c759b643", sym_visibility = "private"}> ({
    ^bb0(%arg54: !algebra.field_vector<"bls12-381.fr">, %arg55: ui64, %arg56: ui64, %arg57: !algebra.field<"bls12-381.fr">):
      %33 = "func.call"(%arg54, %arg55, %arg56) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">
      %34 = "func.call"(%33) <{callee = @zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e}> : (!algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %35 = "algebra.field_equal"(%arg57, %34) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "func.return"(%35) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">, sym_name = "zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", sym_visibility = "private"}> ({
    ^bb0(%arg51: !algebra.field_vector<"bls12-381.fr">, %arg52: ui64, %arg53: ui64):
      "func.return"(%arg51) : (!algebra.field_vector<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64, sym_name = "zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275", sym_visibility = "private"}> ({
    ^bb0(%arg48: !algebra.field_vector<"bls12-381.fr">, %arg49: ui64, %arg50: ui64):
      "func.return"(%arg50) : (ui64) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64, sym_name = "zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94", sym_visibility = "private"}> ({
    ^bb0(%arg45: !algebra.field_vector<"bls12-381.fr">, %arg46: ui64, %arg47: ui64):
      "func.return"(%arg46) : (ui64) -> ()
    }) : () -> ()
    "local.func"() <{function_type = () -> !algebra.field_vector<"bls12-381.fr">, sym_name = "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f"}> ({
      %32 = "algebra.exec.vector_empty"() <{binding = @zkl_binding_7, parameters = [], site = "s0"}> : () -> !algebra.field_vector<"bls12-381.fr">
      "local.return"(%32) : (!algebra.field_vector<"bls12-381.fr">) -> ()
    }) {logical_origin = ["s3h7a6b6310h7072696d6974697665736h766563746f725h656d707479", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), sym_name = "zkl_532a609cf36a935835501ca51308940142121e647ca360843a880bf231f04aa6"}> ({
    ^bb0(%arg42: !algebra.field_vector<"bls12-381.fr">, %arg43: ui64, %arg44: ui64):
      %29:2 = "local.apply"(%arg42, %arg43, %arg44) <{callee = @zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087, site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)
      %30 = "algebra.exec.vector_sum"(%29#0) <{binding = @zkl_binding_8, parameters = [], site = "s3"}> : (!algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %31 = "algebra.exec.vector_sum"(%29#1) <{binding = @zkl_binding_8, parameters = [], site = "s5"}> : (!algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "local.return"(%30, %31) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) {logical_origin = ["s8h73756d636865636b4h73756d73", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">), sym_name = "zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087"}> ({
    ^bb0(%arg39: !algebra.field_vector<"bls12-381.fr">, %arg40: ui64, %arg41: ui64):
      %26 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["0"], site = "s0"}> : () -> ui64
      %27 = "local.apply"(%26, %arg40) <{callee = @s3h7a6b637h696e64696365734h6c657373, site = "s2"}> : (ui64, ui64) -> i1
      "local.if"(%27) <{site = "s3"}> ({
        "local.yield"() : () -> ()
      }, {
        "local.stop"() <{reason = "reject", site = "s3_reject"}> : () -> ()
      }) : (i1) -> ()
      %28:2 = "algebra.exec.vector_split"(%arg39) <{binding = @zkl_binding_9, parameters = [], site = "s5"}> : (!algebra.field_vector<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)
      "local.return"(%28#0, %28#1) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561726h68616c766573", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), sym_name = "zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d"}> ({
    ^bb0(%arg35: !algebra.field_vector<"bls12-381.fr">, %arg36: ui64, %arg37: ui64, %arg38: !algebra.field<"bls12-381.fr">):
      %22:2 = "local.apply"(%arg35, %arg36, %arg37) <{callee = @zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087, site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)
      %23 = "local.apply"(%22#0, %22#1, %arg38) <{callee = @zkl_map_7aa10c0d106e0082840e035854d97e34de85744d05e64191205f7ada5a3efd95, site = "s4"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
      %24 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["1"], site = "s7"}> : () -> ui64
      %25 = "algebra.exec.index_sub"(%arg36, %24) <{binding = @zkl_binding_10, parameters = [], site = "s8"}> : (ui64, ui64) -> ui64
      "local.return"(%23, %25, %arg37) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561729h6669785f6669727374", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5", sym_visibility = "private"}> ({
    ^bb0(%arg32: !algebra.field<"bls12-381.fr">, %arg33: !algebra.field<"bls12-381.fr">, %arg34: !algebra.field<"bls12-381.fr">):
      %19 = "algebra.field_subtract"(%arg33, %arg32) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %20 = "algebra.field_multiply"(%19, %arg34) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %21 = "algebra.field_add"(%arg32, %20) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%21) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">, sym_name = "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d"}> ({
    ^bb0(%arg30: !algebra.field_vector<"bls12-381.fr">, %arg31: !algebra.field<"bls12-381.fr">):
      %18 = "algebra.exec.vector_append"(%arg30, %arg31) <{binding = @zkl_binding_11, parameters = [], site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
      "local.return"(%18) : (!algebra.field_vector<"bls12-381.fr">) -> ()
    }) {logical_origin = ["s3h7a6b6310h7072696d6974697665736h766563746f726h617070656e64", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc"}> ({
    ^bb0(%arg21: !algebra.field_vector<"bls12-381.fr">, %arg22: !algebra.field_vector<"bls12-381.fr">, %arg23: !algebra.field<"bls12-381.fr">):
      %12 = "algebra.exec.vector_length"(%arg22) <{binding = @zkl_binding_1, parameters = [], site = "s1"}> : (!algebra.field_vector<"bls12-381.fr">) -> ui64
      %13 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["1"], site = "s2"}> : () -> ui64
      %14 = "local.apply"(%arg21, %12, %13) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655, site = "s3"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1
      %15 = "local.if"(%14, %arg21, %arg22, %arg23) <{site = "s6"}> ({
      ^bb0(%arg27: !algebra.field_vector<"bls12-381.fr">, %arg28: !algebra.field_vector<"bls12-381.fr">, %arg29: !algebra.field<"bls12-381.fr">):
        %17 = "local.apply"(%arg27, %arg28, %arg29) <{callee = @zkl_3b67bb5451d0deeed7ab9379c12e7c154a5c16946b7db9b65bc0d4be6b613f1d, site = "s7"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
        "local.yield"(%17) : (i1) -> ()
      }, {
      ^bb0(%arg24: !algebra.field_vector<"bls12-381.fr">, %arg25: !algebra.field_vector<"bls12-381.fr">, %arg26: !algebra.field<"bls12-381.fr">):
        %16 = "local.bool_constant"() <{site = "s9", value = false}> : () -> i1
        "local.yield"(%16) : (i1) -> ()
      }) : (i1, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "local.return"(%15) : (i1) -> ()
    }) {logical_origin = ["s8h73756d636865636b5h636865636b", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "zkl_3b67bb5451d0deeed7ab9379c12e7c154a5c16946b7db9b65bc0d4be6b613f1d"}> ({
    ^bb0(%arg18: !algebra.field_vector<"bls12-381.fr">, %arg19: !algebra.field_vector<"bls12-381.fr">, %arg20: !algebra.field<"bls12-381.fr">):
      %5 = "algebra.exec.vector_length"(%arg19) <{binding = @zkl_binding_1, parameters = [], site = "s1"}> : (!algebra.field_vector<"bls12-381.fr">) -> ui64
      %6 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["1"], site = "s2"}> : () -> ui64
      %7:3 = "local.apply"(%arg18, %5, %6) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a, site = "s3"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      %8:3 = "local.apply"(%7#0, %7#1, %7#2, %arg19) <{callee = @zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be, site = "s6"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      %9 = "local.apply"(%8#0, %8#1, %8#2) <{callee = @zkl_realization_0ce8d1f6fa18ecea2634e8a590d8d4d67ef3b2266fc521419daa7adb682a678a, site = "s8"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">
      %10 = "algebra.exec.vector_sum"(%9) <{binding = @zkl_binding_8, parameters = [], site = "s9"}> : (!algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %11 = "algebra.exec.field_equal"(%10, %arg20) <{binding = @zkl_binding_12, parameters = [], site = "s11"}> : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "local.return"(%11) : (i1) -> ()
    }) {logical_origin = ["s8h73756d636865636b11h636865636b5f7461626c65", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), sym_name = "zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be"}> ({
    ^bb0(%arg14: !algebra.field_vector<"bls12-381.fr">, %arg15: ui64, %arg16: ui64, %arg17: !algebra.field_vector<"bls12-381.fr">):
      %4:3 = "local.apply"(%arg14, %arg15, %arg16, %arg17) <{callee = @zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2, site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      "local.return"(%4#0, %4#1, %4#2) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e65617210h6669785f707265666978", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), sym_name = "zkl_195a79478f48dffc2a6917273d8317df0fabae786920a46fa2ac6b2737144299"}> ({
    ^bb0(%arg10: !algebra.field_vector<"bls12-381.fr">, %arg11: ui64, %arg12: ui64, %arg13: !algebra.field<"bls12-381.fr">):
      %3:3 = "local.apply"(%arg10, %arg11, %arg12, %arg13) <{callee = @zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d, site = "s2"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      "local.return"(%3#0, %3#1, %3#2) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ()
    }) {logical_origin = ["zks_50b2228592370f9a2bce2e71277fbb9bf36d691d6ece4416923708e3a0c063ae", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), sym_name = "zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2"}> ({
    ^bb0(%arg6: !algebra.field_vector<"bls12-381.fr">, %arg7: ui64, %arg8: ui64, %arg9: !algebra.field_vector<"bls12-381.fr">):
      %2:3 = "local.apply"(%arg9, %arg6, %arg7, %arg8) <{callee = @finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0, site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      "local.return"(%2#0, %2#1, %2#2) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ()
    }) {logical_origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg5: !algebra.field_vector<"bls12-381.fr">):
      %1 = "data.domain_elements"(%arg5) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%1) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), sym_name = "finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg0: !algebra.field_vector<"bls12-381.fr">, %arg1: ui64, %arg2: ui64, %arg3: !algebra.field<"bls12-381.fr">, %arg4: !algebra.field_vector<"bls12-381.fr">):
      %0:3 = "local.apply"(%arg0, %arg1, %arg2, %arg3) <{callee = @zkl_195a79478f48dffc2a6917273d8317df0fabae786920a46fa2ac6b2737144299, site = "body"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      "local.return"(%0#0, %0#1, %0#2) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ()
    }) {logical_origin = ["finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body", []]} : () -> ()
    "local.finite_fold"() <{domain = @finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_domain, function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), step = @finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body, sym_name = "finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0"}> : () -> ()
    "relation.declare"() <{formula = @zkf_9ca6c98faa0d00ed80eb608a89db1544ad71443a8944af6ac99e6fd78cb3660b, key = "zkl_733a9984be750c90a7e40f8fc81c10a284cb9ecaf745c62024f07f1a3806a10c", kind = "zkc.language.formula/0", purposes = ["parameter", "parameter"], revision = "fef4042b36eb69492320800630ec190760414ad82c4859a47d2aac19bf270e5c", signature = (!algebra.field_vector<"bls12-381.fr">, ui64) -> i1, sym_name = "zkl_733a9984be750c90a7e40f8fc81c10a284cb9ecaf745c62024f07f1a3806a10c"}> : () -> ()
    "relation.declare"() <{formula = @zkf_116f3285742dd1275b8149c69b78a6713cd6256a8af715be7c346da1c793a766, key = "zkl_1c2e12f894c2f4b39d38adc87f1dedbaf7856eb6985dba89eb2261c88030aef2", kind = "zkc.language.formula/0", purposes = ["parameter", "statement"], revision = "a60d910bb6e61b3f4d146e863f02155af13cfbdf8ddd5538ee0d89004c93bd71", signature = (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "zkl_1c2e12f894c2f4b39d38adc87f1dedbaf7856eb6985dba89eb2261c88030aef2"}> : () -> ()
    "relation.declare"() <{formula = @zkf_654a0e58b11e83f398996b9e830df00890bec0f8dc08a65c5750d6d9c759b643, key = "zkl_11c80248216cbe579879aabc5c6f64d5f465a4db68261d6da29eab7c94d7679c", kind = "zkc.language.formula/0", purposes = ["parameter", "parameter", "parameter", "statement"], revision = "2c4b933d7a6995f34b80f29d1478e98e81ee53f22c19789c1c06958fba515a0f", signature = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "zkl_11c80248216cbe579879aabc5c6f64d5f465a4db68261d6da29eab7c94d7679c"}> : () -> ()
  }) : () -> ()
}) : () -> ()

