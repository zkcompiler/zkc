"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.append", implementation = "", sym_name = "zkl_binding_11"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.sub", implementation = "", sym_name = "zkl_binding_10"}> : () -> ()
    "algebra.map_realize"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">, helper = @zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5, rowwise = array<i1: true, true, false>, sym_name = "zkl_map_7aa10c0d106e0082840e035854d97e34de85744d05e64191205f7ada5a3efd95"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.split", implementation = "", sym_name = "zkl_binding_9"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.sum", implementation = "", sym_name = "zkl_binding_8"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.empty", implementation = "", sym_name = "zkl_binding_7"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.mul", implementation = "", sym_name = "zkl_binding_6"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.less", implementation = "", sym_name = "zkl_binding_5"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.div", implementation = "", sym_name = "zkl_binding_4"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.equal", implementation = "", sym_name = "zkl_binding_3"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.mod", implementation = "", sym_name = "zkl_binding_2"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.length", implementation = "", sym_name = "zkl_binding_1"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.constant", implementation = "", sym_name = "zkl_binding_0"}> : () -> ()
    "protocol.func"() <{contracts = [], function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), input_roles = [["role00000000"], ["role00000000"], ["role00000001"], ["role00000000", "role00000001"], ["role00000001"]], origin = ["sums::Reduction", [["F", ["field", "bls12-381.fr"]], ["Max", ["nat", "4"]]]], output_roles = [["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_cf3586ba980b617860654dacf2506dd277a78d1dcf5b84bcc6376225e7fe4f45"}> ({
    ^bb0(%arg72: !algebra.field_vector<"bls12-381.fr">, %arg73: ui64, %arg74: !algebra.field<"bls12-381.fr">, %arg75: ui64, %arg76: !protocol.service_ref<"random.bls12-381.fr/0">):
      %78 = "data.index"() <{value = "1"}> : () -> ui64
      %79:3 = "protocol.local_call"(%arg72, %arg73, %78) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a, role = "role00000000", site = "s1"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      %80:6 = "protocol.apply"(%79#0, %79#1, %79#2, %arg74, %arg75, %arg76) <{callee = @zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d, roles = ["role00000000", "role00000001"], site = "s3"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %81 = "func.call"(%80#1, %80#2, %80#3) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">
      "protocol.return"(%80#0, %81, %80#4, %80#5) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), sym_name = "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a"}> ({
    ^bb0(%arg69: !algebra.field_vector<"bls12-381.fr">, %arg70: ui64, %arg71: ui64):
      %77 = "local.apply"(%arg69, %arg70, %arg71) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655, site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1
      "local.if"(%77) <{site = "s1"}> ({
        "local.yield"() : () -> ()
      }, {
        "local.stop"() <{reason = "reject", site = "s1_reject"}> : () -> ()
      }) : (i1) -> ()
      "local.return"(%arg69, %arg70, %arg71) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561725h7461626c65", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1, sym_name = "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655"}> ({
    ^bb0(%arg54: !algebra.field_vector<"bls12-381.fr">, %arg55: ui64, %arg56: ui64):
      %59 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["0"], site = "s0"}> : () -> ui64
      %60 = "local.apply"(%59, %arg56) <{callee = @s3h7a6b637h696e64696365734h6c657373, site = "s1"}> : (ui64, ui64) -> i1
      %61 = "local.if"(%60, %arg55) <{site = "s3"}> ({
      ^bb0(%arg68: ui64):
        %75 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["64"], site = "s4"}> : () -> ui64
        %76 = "local.apply"(%arg68, %75) <{callee = @s3h7a6b637h696e64696365734h6c657373, site = "s5"}> : (ui64, ui64) -> i1
        "local.yield"(%76) : (i1) -> ()
      }, {
      ^bb0(%arg67: ui64):
        %74 = "local.bool_constant"() <{site = "s7", value = false}> : () -> i1
        "local.yield"(%74) : (i1) -> ()
      }) : (i1, ui64) -> i1
      %62 = "local.if"(%61, %arg54, %arg56) <{site = "s11"}> ({
      ^bb0(%arg65: !algebra.field_vector<"bls12-381.fr">, %arg66: ui64):
        %70 = "algebra.exec.vector_length"(%arg65) <{binding = @zkl_binding_1, parameters = [], site = "s12"}> : (!algebra.field_vector<"bls12-381.fr">) -> ui64
        %71 = "algebra.exec.index_mod"(%70, %arg66) <{binding = @zkl_binding_2, parameters = [], site = "s13"}> : (ui64, ui64) -> ui64
        %72 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["0"], site = "s14"}> : () -> ui64
        %73 = "algebra.exec.index_equal"(%71, %72) <{binding = @zkl_binding_3, parameters = [], site = "s15"}> : (ui64, ui64) -> i1
        "local.yield"(%73) : (i1) -> ()
      }, {
      ^bb0(%arg63: !algebra.field_vector<"bls12-381.fr">, %arg64: ui64):
        %69 = "local.bool_constant"() <{site = "s17", value = false}> : () -> i1
        "local.yield"(%69) : (i1) -> ()
      }) : (i1, !algebra.field_vector<"bls12-381.fr">, ui64) -> i1
      %63 = "local.if"(%62, %arg54, %arg55, %arg56) <{site = "s22"}> ({
      ^bb0(%arg60: !algebra.field_vector<"bls12-381.fr">, %arg61: ui64, %arg62: ui64):
        %65 = "algebra.exec.vector_length"(%arg60) <{binding = @zkl_binding_1, parameters = [], site = "s23"}> : (!algebra.field_vector<"bls12-381.fr">) -> ui64
        %66 = "algebra.exec.index_div"(%65, %arg62) <{binding = @zkl_binding_4, parameters = [], site = "s24"}> : (ui64, ui64) -> ui64
        %67 = "local.apply"(%arg61) <{callee = @s3h7a6b6311h6d756c74696c696e6561724h726f7773, site = "s25"}> : (ui64) -> ui64
        %68 = "algebra.exec.index_equal"(%66, %67) <{binding = @zkl_binding_3, parameters = [], site = "s26"}> : (ui64, ui64) -> i1
        "local.yield"(%68) : (i1) -> ()
      }, {
      ^bb0(%arg57: !algebra.field_vector<"bls12-381.fr">, %arg58: ui64, %arg59: ui64):
        %64 = "local.bool_constant"() <{site = "s28", value = false}> : () -> i1
        "local.yield"(%64) : (i1) -> ()
      }) : (i1, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1
      "local.return"(%63) : (i1) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065", []]} : () -> ()
    "local.func"() <{function_type = (ui64, ui64) -> i1, sym_name = "s3h7a6b637h696e64696365734h6c657373"}> ({
    ^bb0(%arg52: ui64, %arg53: ui64):
      %58 = "algebra.exec.index_less"(%arg52, %arg53) <{binding = @zkl_binding_5, parameters = [], site = "s0"}> : (ui64, ui64) -> i1
      "local.return"(%58) : (i1) -> ()
    }) {logical_origin = ["s3h7a6b637h696e64696365734h6c657373", []]} : () -> ()
    "local.func"() <{function_type = (ui64) -> ui64, sym_name = "s3h7a6b6311h6d756c74696c696e6561724h726f7773"}> ({
    ^bb0(%arg49: ui64):
      %51 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["64"], site = "s0"}> : () -> ui64
      %52 = "local.apply"(%arg49, %51) <{callee = @s3h7a6b637h696e64696365734h6c657373, site = "s1"}> : (ui64, ui64) -> i1
      "local.if"(%52) <{site = "s2"}> ({
        "local.yield"() : () -> ()
      }, {
        "local.stop"() <{reason = "reject", site = "s2_reject"}> : () -> ()
      }) : (i1) -> ()
      %53 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["1"], site = "s3"}> : () -> ui64
      %54 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["0"], site = "s5"}> : () -> ui64
      %55 = "local.for"(%54, %arg49, %53) <{site = "s6"}> ({
      ^bb0(%arg50: ui64, %arg51: ui64):
        %56 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["2"], site = "s7"}> : () -> ui64
        %57 = "algebra.exec.index_mul"(%arg51, %56) <{binding = @zkl_binding_6, parameters = [], site = "s8"}> : (ui64, ui64) -> ui64
        "local.yield"(%57) : (ui64) -> ()
      }) : (ui64, ui64, ui64) -> ui64
      "local.return"(%55) : (ui64) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561724h726f7773", []]} : () -> ()
    "protocol.func"() <{contracts = [["input", "initial_sum", [@zkl_11c80248216cbe579879aabc5c6f64d5f465a4db68261d6da29eab7c94d7679c, [["input", 0, "role00000000"], ["input", 1, "role00000000"], ["input", 2, "role00000000"], ["input", 3, "role00000001"]]], unit, unit]], function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), input_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000000", "role00000001"], ["role00000001"]], origin = ["sumcheck::Reduce", [["F", ["field", "bls12-381.fr"]], ["Max", ["nat", "4"]]]], output_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d"}> ({
    ^bb0(%arg35: !algebra.field_vector<"bls12-381.fr">, %arg36: ui64, %arg37: ui64, %arg38: !algebra.field<"bls12-381.fr">, %arg39: ui64, %arg40: !protocol.service_ref<"random.bls12-381.fr/0">):
      %23 = "func.call"(%arg35, %arg36, %arg37) <{callee = @zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %24 = "data.index"() <{value = "1"}> : () -> ui64
      %25 = "data.index_equal"(%23, %24) : (ui64, ui64) -> i1
      "protocol.guard"(%25) <{owner = "role00000000", site = "s3"}> : (i1) -> ()
      %26 = "func.call"(%arg35, %arg36, %arg37) <{callee = @zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %27 = "protocol.local_call"(%26, %arg39) <{callee = @s3h7a6b637h696e64696365734h6c657373, role = "role00000000", site = "s5"}> : (ui64, ui64) -> i1
      %28 = "arith.constant"() <{value = false}> : () -> i1
      %29 = "arith.cmpi"(%27, %28) <{predicate = 0 : i64}> : (i1, i1) -> i1
      "protocol.guard"(%29) <{owner = "role00000000", site = "s8"}> : (i1) -> ()
      %30 = "protocol.local_call"() <{callee = @zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f, role = "role00000000", site = "s10"}> : () -> !algebra.field_vector<"bls12-381.fr">
      %31 = "protocol.local_call"() <{callee = @zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f, role = "role00000001", site = "s12"}> : () -> !algebra.field_vector<"bls12-381.fr">
      %32:6 = "protocol.repeat"(%arg39, %arg35, %arg36, %arg37, %30, %31, %arg38, %arg40) <{carried = 6 : i64, carried_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"]], maximum = 4 : i64, roles = ["role00000000", "role00000001"], site = "s15"}> ({
      ^bb0(%arg41: ui64, %arg42: !algebra.field_vector<"bls12-381.fr">, %arg43: ui64, %arg44: ui64, %arg45: !algebra.field_vector<"bls12-381.fr">, %arg46: !algebra.field_vector<"bls12-381.fr">, %arg47: !algebra.field<"bls12-381.fr">, %arg48: !protocol.service_ref<"random.bls12-381.fr/0">):
        %33:2 = "protocol.local_call"(%arg42, %arg43, %arg44) <{callee = @zkl_532a609cf36a935835501ca51308940142121e647ca360843a880bf231f04aa6, role = "role00000000", site = "s16"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %34 = "protocol.exchange"(%33#0) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %35 = "protocol.restrict_roles"(%34) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %36 = "protocol.exchange"(%33#1) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_1"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %37 = "protocol.restrict_roles"(%36) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %38 = "algebra.field_add"(%35, %37) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %39 = "algebra.field_equal"(%arg47, %38) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
        "protocol.guard"(%39) <{owner = "role00000001", site = "s24"}> : (i1) -> ()
        %40 = "protocol.query"(%arg48) <{method = "draw", owner = "role00000001", site = "label_6368616c6c656e6765"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
        %41 = "protocol.exchange"(%40) <{receiver = "role00000000", sender = "role00000001", site = "label_64656c6976657279_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %42 = "protocol.restrict_roles"(%41) <{roles = ["role00000000"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %43:3 = "protocol.local_call"(%arg42, %arg43, %arg44, %42) <{callee = @zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d, role = "role00000000", site = "s29"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
        %44 = "protocol.local_call"(%arg45, %42) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000000", site = "s31"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
        %45 = "protocol.local_call"(%arg46, %40) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000001", site = "s33"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
        %46 = "algebra.constant"() <{value = "1"}> : () -> !algebra.field<"bls12-381.fr">
        %47 = "algebra.field_subtract"(%46, %40) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %48 = "algebra.field_multiply"(%47, %35) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %49 = "algebra.field_multiply"(%40, %37) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %50 = "algebra.field_add"(%48, %49) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        "protocol.yield"(%43#0, %43#1, %43#2, %44, %45, %50) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
      }) : (ui64, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      "protocol.return"(%32#3, %32#0, %32#1, %32#2, %32#4, %32#5) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "zkf_654a0e58b11e83f398996b9e830df00890bec0f8dc08a65c5750d6d9c759b643", sym_visibility = "private"}> ({
    ^bb0(%arg31: !algebra.field_vector<"bls12-381.fr">, %arg32: ui64, %arg33: ui64, %arg34: !algebra.field<"bls12-381.fr">):
      %20 = "func.call"(%arg31, %arg32, %arg33) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">
      %21 = "func.call"(%20) <{callee = @zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e}> : (!algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %22 = "algebra.field_equal"(%arg34, %21) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "func.return"(%22) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">, sym_name = "zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", sym_visibility = "private"}> ({
    ^bb0(%arg28: !algebra.field_vector<"bls12-381.fr">, %arg29: ui64, %arg30: ui64):
      "func.return"(%arg28) : (!algebra.field_vector<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e", sym_visibility = "private"}> ({
    ^bb0(%arg27: !algebra.field_vector<"bls12-381.fr">):
      %18 = "algebra.constant"() <{value = "0"}> : () -> !algebra.field<"bls12-381.fr">
      %19 = "algebra.finite_fold"(%arg27, %18) <{domain = @finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_domain, step = @finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_body}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%19) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_domain", sym_visibility = "private"}> ({
    ^bb0(%arg26: !algebra.field_vector<"bls12-381.fr">):
      %17 = "data.domain_elements"(%arg26) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%17) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_body", sym_visibility = "private"}> ({
    ^bb0(%arg23: !algebra.field<"bls12-381.fr">, %arg24: !algebra.field<"bls12-381.fr">, %arg25: !algebra.field_vector<"bls12-381.fr">):
      %16 = "func.call"(%arg23, %arg24) <{callee = @zkl_3fc17a64a5bb6e75192d0a1362e9954f0d434a10d0f93e319db6b516835a1005}> : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%16) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_3fc17a64a5bb6e75192d0a1362e9954f0d434a10d0f93e319db6b516835a1005", sym_visibility = "private"}> ({
    ^bb0(%arg21: !algebra.field<"bls12-381.fr">, %arg22: !algebra.field<"bls12-381.fr">):
      %15 = "algebra.field_add"(%arg21, %arg22) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%15) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64, sym_name = "zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275", sym_visibility = "private"}> ({
    ^bb0(%arg18: !algebra.field_vector<"bls12-381.fr">, %arg19: ui64, %arg20: ui64):
      "func.return"(%arg20) : (ui64) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64, sym_name = "zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94", sym_visibility = "private"}> ({
    ^bb0(%arg15: !algebra.field_vector<"bls12-381.fr">, %arg16: ui64, %arg17: ui64):
      "func.return"(%arg16) : (ui64) -> ()
    }) : () -> ()
    "local.func"() <{function_type = () -> !algebra.field_vector<"bls12-381.fr">, sym_name = "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f"}> ({
      %14 = "algebra.exec.vector_empty"() <{binding = @zkl_binding_7, parameters = [], site = "s0"}> : () -> !algebra.field_vector<"bls12-381.fr">
      "local.return"(%14) : (!algebra.field_vector<"bls12-381.fr">) -> ()
    }) {logical_origin = ["s3h7a6b6310h7072696d6974697665736h766563746f725h656d707479", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), sym_name = "zkl_532a609cf36a935835501ca51308940142121e647ca360843a880bf231f04aa6"}> ({
    ^bb0(%arg12: !algebra.field_vector<"bls12-381.fr">, %arg13: ui64, %arg14: ui64):
      %11:2 = "local.apply"(%arg12, %arg13, %arg14) <{callee = @zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087, site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)
      %12 = "algebra.exec.vector_sum"(%11#0) <{binding = @zkl_binding_8, parameters = [], site = "s3"}> : (!algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %13 = "algebra.exec.vector_sum"(%11#1) <{binding = @zkl_binding_8, parameters = [], site = "s5"}> : (!algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "local.return"(%12, %13) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) {logical_origin = ["s8h73756d636865636b4h73756d73", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">), sym_name = "zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087"}> ({
    ^bb0(%arg9: !algebra.field_vector<"bls12-381.fr">, %arg10: ui64, %arg11: ui64):
      %8 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["0"], site = "s0"}> : () -> ui64
      %9 = "local.apply"(%8, %arg10) <{callee = @s3h7a6b637h696e64696365734h6c657373, site = "s2"}> : (ui64, ui64) -> i1
      "local.if"(%9) <{site = "s3"}> ({
        "local.yield"() : () -> ()
      }, {
        "local.stop"() <{reason = "reject", site = "s3_reject"}> : () -> ()
      }) : (i1) -> ()
      %10:2 = "algebra.exec.vector_split"(%arg9) <{binding = @zkl_binding_9, parameters = [], site = "s5"}> : (!algebra.field_vector<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)
      "local.return"(%10#0, %10#1) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561726h68616c766573", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), sym_name = "zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d"}> ({
    ^bb0(%arg5: !algebra.field_vector<"bls12-381.fr">, %arg6: ui64, %arg7: ui64, %arg8: !algebra.field<"bls12-381.fr">):
      %4:2 = "local.apply"(%arg5, %arg6, %arg7) <{callee = @zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087, site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)
      %5 = "local.apply"(%4#0, %4#1, %arg8) <{callee = @zkl_map_7aa10c0d106e0082840e035854d97e34de85744d05e64191205f7ada5a3efd95, site = "s4"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
      %6 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["1"], site = "s7"}> : () -> ui64
      %7 = "algebra.exec.index_sub"(%arg6, %6) <{binding = @zkl_binding_10, parameters = [], site = "s8"}> : (ui64, ui64) -> ui64
      "local.return"(%5, %7, %arg7) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561729h6669785f6669727374", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5", sym_visibility = "private"}> ({
    ^bb0(%arg2: !algebra.field<"bls12-381.fr">, %arg3: !algebra.field<"bls12-381.fr">, %arg4: !algebra.field<"bls12-381.fr">):
      %1 = "algebra.field_subtract"(%arg3, %arg2) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %2 = "algebra.field_multiply"(%1, %arg4) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %3 = "algebra.field_add"(%arg2, %2) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%3) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">, sym_name = "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d"}> ({
    ^bb0(%arg0: !algebra.field_vector<"bls12-381.fr">, %arg1: !algebra.field<"bls12-381.fr">):
      %0 = "algebra.exec.vector_append"(%arg0, %arg1) <{binding = @zkl_binding_11, parameters = [], site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
      "local.return"(%0) : (!algebra.field_vector<"bls12-381.fr">) -> ()
    }) {logical_origin = ["s3h7a6b6310h7072696d6974697665736h766563746f726h617070656e64", []]} : () -> ()
    "relation.declare"() <{formula = @zkf_654a0e58b11e83f398996b9e830df00890bec0f8dc08a65c5750d6d9c759b643, key = "zkl_11c80248216cbe579879aabc5c6f64d5f465a4db68261d6da29eab7c94d7679c", kind = "zkc.language.formula/0", purposes = ["parameter", "parameter", "parameter", "statement"], revision = "2c4b933d7a6995f34b80f29d1478e98e81ee53f22c19789c1c06958fba515a0f", signature = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "zkl_11c80248216cbe579879aabc5c6f64d5f465a4db68261d6da29eab7c94d7679c"}> : () -> ()
  }) : () -> ()
}) : () -> ()

