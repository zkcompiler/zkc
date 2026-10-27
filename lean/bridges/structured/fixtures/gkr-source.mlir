"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "runtime.binding"() <{arguments = [], contract = "index.add", implementation = "", sym_name = "zkl_binding_12"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.split", implementation = "", sym_name = "zkl_binding_11"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.sub", implementation = "", sym_name = "zkl_binding_10"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.mul", implementation = "", sym_name = "zkl_binding_9"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.less", implementation = "", sym_name = "zkl_binding_8"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.div", implementation = "", sym_name = "zkl_binding_7"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.equal", implementation = "", sym_name = "zkl_binding_6"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.mod", implementation = "", sym_name = "zkl_binding_5"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.sum", implementation = "", sym_name = "zkl_binding_4"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.constant", implementation = "", sym_name = "zkl_binding_3"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.length", implementation = "", sym_name = "zkl_binding_2"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.append", implementation = "", sym_name = "zkl_binding_1"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.empty", implementation = "", sym_name = "zkl_binding_0"}> : () -> ()
    "protocol.func"() <{contracts = [], function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> i1, input_roles = [["role00000000", "role00000001"], ["role00000001"], ["role00000000", "role00000001"], ["role00000000", "role00000001"], ["role00000000", "role00000001"], ["role00000000", "role00000001"], ["role00000000", "role00000001"], ["role00000001"]], origin = ["gkr::Gkr", [["F", ["field", "bls12-381.fr"]], ["MaxLayers", ["nat", "4"]], ["MaxWidth", ["nat", "4"]]]], output_roles = [["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2"}> ({
    ^bb0(%arg431: !algebra.field_vector<"bls12-381.fr">, %arg432: !algebra.field_vector<"bls12-381.fr">, %arg433: !algebra.field_vector<"bls12-381.fr">, %arg434: !algebra.field_vector<"bls12-381.fr">, %arg435: ui64, %arg436: ui64, %arg437: ui64, %arg438: !protocol.service_ref<"random.bls12-381.fr/0">):
      %1084 = "protocol.local_call"() <{callee = @zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f, role = "role00000001", site = "s0"}> : () -> !algebra.field_vector<"bls12-381.fr">
      %1085 = "protocol.local_call"() <{callee = @zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f, role = "role00000000", site = "s2"}> : () -> !algebra.field_vector<"bls12-381.fr">
      %1086:2 = "protocol.repeat"(%arg437, %1084, %1085, %arg438) <{carried = 2 : i64, carried_roles = [["role00000001"], ["role00000000"]], maximum = 4 : i64, roles = ["role00000000", "role00000001"], site = "s4"}> ({
      ^bb0(%arg453: ui64, %arg454: !algebra.field_vector<"bls12-381.fr">, %arg455: !algebra.field_vector<"bls12-381.fr">, %arg456: !protocol.service_ref<"random.bls12-381.fr/0">):
        %1126 = "protocol.query"(%arg456) <{method = "draw", owner = "role00000001", site = "label_6f7574707574"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
        %1127 = "protocol.exchange"(%1126) <{receiver = "role00000000", sender = "role00000001", site = "label_6f75747075745f64656c6976657279_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1128 = "protocol.restrict_roles"(%1127) <{roles = ["role00000000"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1129 = "protocol.local_call"(%arg454, %1126) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000001", site = "s9"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
        %1130 = "protocol.local_call"(%arg455, %1128) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000000", site = "s11"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
        "protocol.yield"(%1129, %1130) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> ()
      }) : (ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)
      %1087 = "protocol.local_call"(%arg432, %1086#0) <{callee = @zkl_28c1498dbf9d83fc38ed7b21a89d56146297abcbf1ac78968a8b454c9eef5496, role = "role00000001", site = "s15"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %1088:3 = "protocol.repeat"(%arg435, %1086#0, %1086#1, %1087, %arg431, %arg433, %arg434, %arg435, %arg436, %arg437, %arg438) <{carried = 3 : i64, carried_roles = [["role00000001"], ["role00000000"], ["role00000001"]], maximum = 4 : i64, roles = ["role00000000", "role00000001"], site = "s23"}> ({
      ^bb0(%arg439: ui64, %arg440: !algebra.field_vector<"bls12-381.fr">, %arg441: !algebra.field_vector<"bls12-381.fr">, %arg442: !algebra.field<"bls12-381.fr">, %arg443: !algebra.field_vector<"bls12-381.fr">, %arg444: !algebra.field_vector<"bls12-381.fr">, %arg445: !algebra.field_vector<"bls12-381.fr">, %arg446: ui64, %arg447: ui64, %arg448: ui64, %arg449: !protocol.service_ref<"random.bls12-381.fr/0">):
        %1091 = "protocol.local_call"(%arg444, %arg445, %arg443, %arg446, %arg447, %arg448, %arg439) <{callee = @zkl_8c63ad97d926a7762c597860addde408bcd2077ea9cda1b99df123dc13e64af6, role = "role00000000", site = "s24"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">
        %1092 = "protocol.local_call"(%arg444, %arg439, %arg447) <{callee = @zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e, role = "role00000000", site = "s26"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">
        %1093 = "protocol.local_call"(%arg445, %arg439, %arg447) <{callee = @zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e, role = "role00000000", site = "s27"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">
        %1094:4 = "protocol.local_call"(%1092, %1093, %arg441, %1091, %arg448) <{callee = @zkl_d1f2756b99b17aad26e4b85a966eec4c9419609618b22e3ee7f8a3349cb1e33b, role = "role00000000", site = "s28"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)
        %1095:7 = "protocol.apply"(%1094#0, %1094#1, %1094#2, %1094#3, %arg442, %arg448, %arg449) <{callee = @zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba, roles = ["role00000000", "role00000001"], site = "label_6c656674"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %1096:7 = "protocol.apply"(%1095#1, %1095#2, %1095#3, %1095#4, %1095#6, %arg448, %arg449) <{callee = @zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba, roles = ["role00000000", "role00000001"], site = "label_7269676874"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %1097 = "protocol.local_call"(%1091, %1095#0, %1096#0, %arg448) <{callee = @zkl_91fe8ea73b5db3432f90fc8fe9725c8455fce8782b4cc4d2839d05826de71b8f, role = "role00000000", site = "s38"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64) -> !algebra.field_vector<"bls12-381.fr">
        %1098 = "data.index"() <{value = "0"}> : () -> ui64
        %1099 = "protocol.local_call"(%1097, %1098) <{callee = @zkl_6ba53ec68a0230031d706e4a93e78f80425c51108d34ecc0a5aa5681eded9c8e, role = "role00000000", site = "s41"}> : (!algebra.field_vector<"bls12-381.fr">, ui64) -> !algebra.field<"bls12-381.fr">
        %1100 = "protocol.exchange"(%1099) <{receiver = "role00000001", sender = "role00000000", site = "label_6c696e655f636f6e7374616e74_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1101 = "protocol.restrict_roles"(%1100) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1102 = "protocol.local_call"() <{callee = @zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f, role = "role00000001", site = "s44"}> : () -> !algebra.field_vector<"bls12-381.fr">
        %1103 = "protocol.local_call"(%1102, %1101) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000001", site = "s45"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
        %1104 = "protocol.repeat"(%arg448, %1103, %1097) <{carried = 1 : i64, carried_roles = [["role00000001"]], maximum = 4 : i64, roles = ["role00000000", "role00000001"], site = "s48"}> ({
        ^bb0(%arg450: ui64, %arg451: !algebra.field_vector<"bls12-381.fr">, %arg452: !algebra.field_vector<"bls12-381.fr">):
          %1122 = "protocol.local_call"(%arg452, %arg450) <{callee = @zkl_ca5df6081733f8afff4ae42147eb8eba3338d5a96600a7155f619346f19e4b47, role = "role00000000", site = "s49"}> : (!algebra.field_vector<"bls12-381.fr">, ui64) -> !algebra.field<"bls12-381.fr">
          %1123 = "protocol.exchange"(%1122) <{receiver = "role00000001", sender = "role00000000", site = "label_6c696e655f636f656666696369656e74_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
          %1124 = "protocol.restrict_roles"(%1123) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
          %1125 = "protocol.local_call"(%arg451, %1124) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000001", site = "s52"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
          "protocol.yield"(%1125) : (!algebra.field_vector<"bls12-381.fr">) -> ()
        }) : (ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
        %1105 = "protocol.local_call"(%1104) <{callee = @zkl_6ec6b9d6cb41b6bf4ef8e898ba1b283d099252f7de2db0b173f26714e3a46216, role = "role00000001", site = "s56"}> : (!algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1106 = "protocol.local_call"(%arg444, %arg439, %arg447) <{callee = @zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e, role = "role00000001", site = "s58"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">
        %1107 = "protocol.local_call"(%1106, %arg440, %1095#5, %1096#5) <{callee = @zkl_161d519d8d5fe2674feddb6e6d14269c9cca82ff216b6b3205ade46cc8b8d35f, role = "role00000001", site = "s61"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1108 = "protocol.local_call"(%arg445, %arg439, %arg447) <{callee = @zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e, role = "role00000001", site = "s63"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">
        %1109 = "protocol.local_call"(%1108, %arg440, %1095#5, %1096#5) <{callee = @zkl_161d519d8d5fe2674feddb6e6d14269c9cca82ff216b6b3205ade46cc8b8d35f, role = "role00000001", site = "s66"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1110 = "algebra.field_add"(%1101, %1105) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1111 = "algebra.field_multiply"(%1107, %1110) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1112 = "algebra.field_multiply"(%1109, %1101) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1113 = "algebra.field_multiply"(%1112, %1105) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1114 = "algebra.field_add"(%1111, %1113) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1115 = "algebra.field_equal"(%1096#6, %1114) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
        "protocol.guard"(%1115) <{owner = "role00000001", site = "s75"}> : (i1) -> ()
        %1116 = "protocol.query"(%arg449) <{method = "draw", owner = "role00000001", site = "label_6c696e655f6368616c6c656e6765"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
        %1117 = "protocol.exchange"(%1116) <{receiver = "role00000000", sender = "role00000001", site = "label_6c696e655f64656c6976657279_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1118 = "protocol.restrict_roles"(%1117) <{roles = ["role00000000"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1119 = "protocol.local_call"(%1104, %1116) <{callee = @zkl_21465134b1aa848c616c790eff1907b1a442ba76730b77da2be48acd923d6ff7, role = "role00000001", site = "s80"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1120 = "protocol.local_call"(%1095#5, %1096#5, %1116) <{callee = @zkl_1f2e31017a1a0403a56241b1d83eac39d1ecc40b298cd066516f78ae9c5b3434, role = "role00000001", site = "s84"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
        %1121 = "protocol.local_call"(%1095#0, %1096#0, %1118) <{callee = @zkl_1f2e31017a1a0403a56241b1d83eac39d1ecc40b298cd066516f78ae9c5b3434, role = "role00000000", site = "s86"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
        "protocol.yield"(%1120, %1121, %1119) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
      }) : (ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %1089 = "protocol.local_call"(%arg431, %1088#0) <{callee = @zkl_28c1498dbf9d83fc38ed7b21a89d56146297abcbf1ac78968a8b454c9eef5496, role = "role00000001", site = "s90"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %1090 = "algebra.field_equal"(%1089, %1088#2) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "protocol.return"(%1090) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", sym_visibility = "private"}> ({
    ^bb0(%arg430: !runtime.scope):
      %1079 = "exec.apply"(%arg430) <{binding = @zkl_binding_0, parameters = [], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%1079)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%1080: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %1081 = "exec.returned"(%1080) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%1081) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%1082: !exec.stop):  // pred: ^bb0
      %1083 = "exec.failed"(%1082) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%1083) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6310h7072696d6974697665736h766563746f725h656d707479", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", sym_visibility = "private"}> ({
    ^bb0(%arg427: !runtime.scope, %arg428: !algebra.field_vector<"bls12-381.fr">, %arg429: !algebra.field<"bls12-381.fr">):
      %1074 = "exec.apply"(%arg427, %arg428, %arg429) <{binding = @zkl_binding_1, parameters = [], site = "s0"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%1074)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%1075: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %1076 = "exec.returned"(%1075) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%1076) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%1077: !exec.stop):  // pred: ^bb0
      %1078 = "exec.failed"(%1077) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%1078) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6310h7072696d6974697665736h766563746f726h617070656e64", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_28c1498dbf9d83fc38ed7b21a89d56146297abcbf1ac78968a8b454c9eef5496", sym_visibility = "private"}> ({
    ^bb0(%arg424: !runtime.scope, %arg425: !algebra.field_vector<"bls12-381.fr">, %arg426: !algebra.field_vector<"bls12-381.fr">):
      %1055 = "exec.apply"(%arg424, %arg426) <{binding = @zkl_binding_2, parameters = [], site = "s0"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1055)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1056: ui64):  // pred: ^bb0
      %1057 = "exec.apply"(%arg424) <{binding = @zkl_binding_3, parameters = ["1"], site = "s1"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1057)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%1058: !exec.stop):  // 6 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6
      %1059 = "exec.failed"(%1058) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%1059) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb3(%1060: ui64):  // pred: ^bb1
      %1061 = "func.call"(%arg424, %arg425, %1056, %1060) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a}> {runtime.site = "s2"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%1061)[^bb4, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb4(%1062: !algebra.field_vector<"bls12-381.fr">, %1063: ui64, %1064: ui64):  // pred: ^bb3
      %1065 = "func.call"(%arg424, %1062, %1063, %1064, %arg426) <{callee = @zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be}> {runtime.site = "s4"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%1065)[^bb5, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb5(%1066: !algebra.field_vector<"bls12-381.fr">, %1067: ui64, %1068: ui64):  // pred: ^bb4
      %1069 = "exec.compute"(%arg424, %1066, %1067, %1068) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33, site = "s5"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%1069)[^bb6, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb6(%1070: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb5
      %1071 = "exec.apply"(%arg424, %1070) <{binding = @zkl_binding_4, parameters = [], site = "s6"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%1071)[^bb7, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb7(%1072: !algebra.field<"bls12-381.fr">):  // pred: ^bb6
      %1073 = "exec.returned"(%1072) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%1073) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b728h6576616c75617465", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", sym_visibility = "private"}> ({
    ^bb0(%arg420: !runtime.scope, %arg421: !algebra.field_vector<"bls12-381.fr">, %arg422: ui64, %arg423: ui64):
      %1036 = "func.call"(%arg420, %arg421, %arg422, %arg423) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655}> {runtime.site = "s0"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1036)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1037: i1):  // pred: ^bb0
      %1038 = "exec.test"(%arg420, %1037) <{site = "s1"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1038)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%1039: !exec.stop):  // 8 preds: ^bb0, ^bb1, ^bb4, ^bb5, ^bb7, ^bb8, ^bb10, ^bb11
      %1040 = "exec.failed"(%1039) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%1040) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb3(%1041: i1):  // pred: ^bb1
      "cf.cond_br"(%1041)[^bb4, ^bb5] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb4:  // pred: ^bb3
      %1042 = "runtime.enter_scope"(%arg420) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1042)[^bb7, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb5:  // pred: ^bb3
      %1043 = "runtime.enter_scope"(%arg420) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1043)[^bb10, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // 2 preds: ^bb9, ^bb12
      %1044 = "exec.returned"(%arg421, %arg422, %arg423) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%1044) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb7(%1045: !runtime.scope):  // pred: ^bb4
      %1046 = "func.call"(%1045) <{callee = @zkl_control_0}> : (!runtime.scope) -> !exec.outcome<>
      %1047 = "runtime.exit_scope"(%1045, %1046) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%1047)[^bb8, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb8(%1048: !runtime.transfer<>):  // pred: ^bb7
      %1049 = "runtime.accept_transfer"(%arg420, %1048) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%1049)[^bb9, ^bb2] : (!exec.outcome<>) -> ()
    ^bb9:  // pred: ^bb8
      "cf.br"()[^bb6] : () -> ()
    ^bb10(%1050: !runtime.scope):  // pred: ^bb5
      %1051 = "func.call"(%1050) <{callee = @zkl_control_1}> : (!runtime.scope) -> !exec.outcome<>
      %1052 = "runtime.exit_scope"(%1050, %1051) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%1052)[^bb11, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb11(%1053: !runtime.transfer<>):  // pred: ^bb10
      %1054 = "runtime.accept_transfer"(%arg420, %1053) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%1054)[^bb12, ^bb2] : (!exec.outcome<>) -> ()
    ^bb12:  // pred: ^bb11
      "cf.br"()[^bb6] : () -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561725h7461626c65", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_0", sym_visibility = "private"}> ({
    ^bb0(%arg419: !runtime.scope):
      %1035 = "exec.complete"(%arg419) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%1035) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_1", sym_visibility = "private"}> ({
    ^bb0(%arg418: !runtime.scope):
      %1032 = "exec.reject"(%arg418) <{reason = "reject", site = "s1_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%1032)[^bb1] : (!exec.stop) -> ()
    ^bb1(%1033: !exec.stop):  // pred: ^bb0
      %1034 = "exec.failed"(%1033) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%1034) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", sym_visibility = "private"}> ({
    ^bb0(%arg414: !runtime.scope, %arg415: !algebra.field_vector<"bls12-381.fr">, %arg416: ui64, %arg417: ui64):
      %974 = "exec.apply"(%arg414) <{binding = @zkl_binding_3, parameters = ["0"], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%974)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%975: ui64):  // pred: ^bb0
      %976 = "func.call"(%arg414, %975, %arg417) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s1"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%976)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%977: !exec.stop):  // 23 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12, ^bb15, ^bb16, ^bb17, ^bb18, ^bb19, ^bb21, ^bb22, ^bb25, ^bb26, ^bb28, ^bb29, ^bb31, ^bb32
      %978 = "exec.failed"(%977) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%978) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%979: i1):  // pred: ^bb1
      %980 = "exec.test"(%arg414, %979) <{site = "s3"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%980)[^bb4, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb4(%981: i1):  // pred: ^bb3
      "cf.cond_br"(%981)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %982 = "runtime.enter_scope"(%arg414, %arg416) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "then", site = "s3"}> : (!runtime.scope, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%982)[^bb8, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %983 = "runtime.enter_scope"(%arg414, %arg416) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "else", site = "s3"}> : (!runtime.scope, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%983)[^bb11, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7(%984: i1):  // 2 preds: ^bb10, ^bb13
      %985 = "exec.test"(%arg414, %984) <{site = "s11"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%985)[^bb14, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb8(%986: !runtime.scope):  // pred: ^bb5
      %987 = "func.call"(%986, %arg416) <{callee = @zkl_control_2}> : (!runtime.scope, ui64) -> !exec.outcome<(i1)>
      %988 = "runtime.exit_scope"(%986, %987) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%988)[^bb9, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb9(%989: !runtime.transfer<(i1)>):  // pred: ^bb8
      %990 = "runtime.accept_transfer"(%arg414, %989) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%990)[^bb10, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb10(%991: i1):  // pred: ^bb9
      "cf.br"(%991)[^bb7] : (i1) -> ()
    ^bb11(%992: !runtime.scope):  // pred: ^bb6
      %993 = "func.call"(%992, %arg416) <{callee = @zkl_control_3}> : (!runtime.scope, ui64) -> !exec.outcome<(i1)>
      %994 = "runtime.exit_scope"(%992, %993) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%994)[^bb12, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb12(%995: !runtime.transfer<(i1)>):  // pred: ^bb11
      %996 = "runtime.accept_transfer"(%arg414, %995) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%996)[^bb13, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb13(%997: i1):  // pred: ^bb12
      "cf.br"(%997)[^bb7] : (i1) -> ()
    ^bb14(%998: i1):  // pred: ^bb7
      "cf.cond_br"(%998)[^bb15, ^bb16] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb15:  // pred: ^bb14
      %999 = "runtime.enter_scope"(%arg414, %arg415, %arg417) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "then", site = "s11"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%999)[^bb18, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb16:  // pred: ^bb14
      %1000 = "runtime.enter_scope"(%arg414, %arg415, %arg417) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "else", site = "s11"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1000)[^bb21, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb17(%1001: i1):  // 2 preds: ^bb20, ^bb23
      %1002 = "exec.test"(%arg414, %1001) <{site = "s22"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1002)[^bb24, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb18(%1003: !runtime.scope):  // pred: ^bb15
      %1004 = "func.call"(%1003, %arg415, %arg417) <{callee = @zkl_control_4}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>
      %1005 = "runtime.exit_scope"(%1003, %1004) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%1005)[^bb19, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb19(%1006: !runtime.transfer<(i1)>):  // pred: ^bb18
      %1007 = "runtime.accept_transfer"(%arg414, %1006) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1007)[^bb20, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb20(%1008: i1):  // pred: ^bb19
      "cf.br"(%1008)[^bb17] : (i1) -> ()
    ^bb21(%1009: !runtime.scope):  // pred: ^bb16
      %1010 = "func.call"(%1009, %arg415, %arg417) <{callee = @zkl_control_5}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>
      %1011 = "runtime.exit_scope"(%1009, %1010) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%1011)[^bb22, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb22(%1012: !runtime.transfer<(i1)>):  // pred: ^bb21
      %1013 = "runtime.accept_transfer"(%arg414, %1012) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1013)[^bb23, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb23(%1014: i1):  // pred: ^bb22
      "cf.br"(%1014)[^bb17] : (i1) -> ()
    ^bb24(%1015: i1):  // pred: ^bb17
      "cf.cond_br"(%1015)[^bb25, ^bb26] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb25:  // pred: ^bb24
      %1016 = "runtime.enter_scope"(%arg414, %arg415, %arg416, %arg417) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "then", site = "s22"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1016)[^bb28, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb26:  // pred: ^bb24
      %1017 = "runtime.enter_scope"(%arg414, %arg415, %arg416, %arg417) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "else", site = "s22"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1017)[^bb31, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb27(%1018: i1):  // 2 preds: ^bb30, ^bb33
      %1019 = "exec.returned"(%1018) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%1019) : (!exec.outcome<(i1)>) -> ()
    ^bb28(%1020: !runtime.scope):  // pred: ^bb25
      %1021 = "func.call"(%1020, %arg415, %arg416, %arg417) <{callee = @zkl_control_6}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      %1022 = "runtime.exit_scope"(%1020, %1021) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%1022)[^bb29, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb29(%1023: !runtime.transfer<(i1)>):  // pred: ^bb28
      %1024 = "runtime.accept_transfer"(%arg414, %1023) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1024)[^bb30, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb30(%1025: i1):  // pred: ^bb29
      "cf.br"(%1025)[^bb27] : (i1) -> ()
    ^bb31(%1026: !runtime.scope):  // pred: ^bb26
      %1027 = "func.call"(%1026, %arg415, %arg416, %arg417) <{callee = @zkl_control_7}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      %1028 = "runtime.exit_scope"(%1026, %1027) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%1028)[^bb32, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb32(%1029: !runtime.transfer<(i1)>):  // pred: ^bb31
      %1030 = "runtime.accept_transfer"(%arg414, %1029) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1030)[^bb33, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb33(%1031: i1):  // pred: ^bb32
      "cf.br"(%1031)[^bb27] : (i1) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_2", sym_visibility = "private"}> ({
    ^bb0(%arg412: !runtime.scope, %arg413: ui64):
      %967 = "exec.apply"(%arg412) <{binding = @zkl_binding_3, parameters = ["64"], site = "s4"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%967)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%968: ui64):  // pred: ^bb0
      %969 = "func.call"(%arg412, %arg413, %968) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s5"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%969)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%970: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %971 = "exec.failed"(%970) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%971) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%972: i1):  // pred: ^bb1
      %973 = "exec.complete"(%arg412, %972) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%973) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_3", sym_visibility = "private"}> ({
    ^bb0(%arg410: !runtime.scope, %arg411: ui64):
      %962 = "exec.boolean"(%arg410) <{site = "s7", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%962)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%963: i1):  // pred: ^bb0
      %964 = "exec.complete"(%arg410, %963) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%964) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%965: !exec.stop):  // pred: ^bb0
      %966 = "exec.failed"(%965) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%966) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_4", sym_visibility = "private"}> ({
    ^bb0(%arg407: !runtime.scope, %arg408: !algebra.field_vector<"bls12-381.fr">, %arg409: ui64):
      %951 = "exec.apply"(%arg407, %arg408) <{binding = @zkl_binding_2, parameters = [], site = "s12"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%951)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%952: ui64):  // pred: ^bb0
      %953 = "exec.apply"(%arg407, %952, %arg409) <{binding = @zkl_binding_5, parameters = [], site = "s13"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%953)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%954: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %955 = "exec.failed"(%954) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%955) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%956: ui64):  // pred: ^bb1
      %957 = "exec.apply"(%arg407) <{binding = @zkl_binding_3, parameters = ["0"], site = "s14"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%957)[^bb4, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%958: ui64):  // pred: ^bb3
      %959 = "exec.apply"(%arg407, %956, %958) <{binding = @zkl_binding_6, parameters = [], site = "s15"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%959)[^bb5, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb5(%960: i1):  // pred: ^bb4
      %961 = "exec.complete"(%arg407, %960) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%961) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_5", sym_visibility = "private"}> ({
    ^bb0(%arg404: !runtime.scope, %arg405: !algebra.field_vector<"bls12-381.fr">, %arg406: ui64):
      %946 = "exec.boolean"(%arg404) <{site = "s17", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%946)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%947: i1):  // pred: ^bb0
      %948 = "exec.complete"(%arg404, %947) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%948) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%949: !exec.stop):  // pred: ^bb0
      %950 = "exec.failed"(%949) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%950) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_6", sym_visibility = "private"}> ({
    ^bb0(%arg400: !runtime.scope, %arg401: !algebra.field_vector<"bls12-381.fr">, %arg402: ui64, %arg403: ui64):
      %935 = "exec.apply"(%arg400, %arg401) <{binding = @zkl_binding_2, parameters = [], site = "s23"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%935)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%936: ui64):  // pred: ^bb0
      %937 = "exec.apply"(%arg400, %936, %arg403) <{binding = @zkl_binding_7, parameters = [], site = "s24"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%937)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%938: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %939 = "exec.failed"(%938) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%939) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%940: ui64):  // pred: ^bb1
      %941 = "func.call"(%arg400, %arg402) <{callee = @s3h7a6b6311h6d756c74696c696e6561724h726f7773}> {runtime.site = "s25"} : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%941)[^bb4, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%942: ui64):  // pred: ^bb3
      %943 = "exec.apply"(%arg400, %940, %942) <{binding = @zkl_binding_6, parameters = [], site = "s26"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%943)[^bb5, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb5(%944: i1):  // pred: ^bb4
      %945 = "exec.complete"(%arg400, %944) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%945) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_7", sym_visibility = "private"}> ({
    ^bb0(%arg396: !runtime.scope, %arg397: !algebra.field_vector<"bls12-381.fr">, %arg398: ui64, %arg399: ui64):
      %930 = "exec.boolean"(%arg396) <{site = "s28", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%930)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%931: i1):  // pred: ^bb0
      %932 = "exec.complete"(%arg396, %931) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%932) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%933: !exec.stop):  // pred: ^bb0
      %934 = "exec.failed"(%933) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%934) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "s3h7a6b637h696e64696365734h6c657373", sym_visibility = "private"}> ({
    ^bb0(%arg393: !runtime.scope, %arg394: ui64, %arg395: ui64):
      %925 = "exec.apply"(%arg393, %arg394, %arg395) <{binding = @zkl_binding_8, parameters = [], site = "s0"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%925)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%926: i1):  // pred: ^bb0
      %927 = "exec.returned"(%926) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%927) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%928: !exec.stop):  // pred: ^bb0
      %929 = "exec.failed"(%928) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%929) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.origin = ["s3h7a6b637h696e64696365734h6c657373", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "s3h7a6b6311h6d756c74696c696e6561724h726f7773", sym_visibility = "private"}> ({
    ^bb0(%arg391: !runtime.scope, %arg392: ui64):
      %878 = "exec.apply"(%arg391) <{binding = @zkl_binding_3, parameters = ["64"], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%878)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%879: ui64):  // pred: ^bb0
      %880 = "func.call"(%arg391, %arg392, %879) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s1"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%880)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%881: !exec.stop):  // 14 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12, ^bb14, ^bb15, ^bb19, ^bb21
      %882 = "exec.failed"(%881) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%882) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%883: i1):  // pred: ^bb1
      %884 = "exec.test"(%arg391, %883) <{site = "s2"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%884)[^bb4, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb4(%885: i1):  // pred: ^bb3
      "cf.cond_br"(%885)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %886 = "runtime.enter_scope"(%arg391) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s2"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%886)[^bb8, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %887 = "runtime.enter_scope"(%arg391) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s2"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%887)[^bb11, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // 2 preds: ^bb10, ^bb13
      %888 = "exec.apply"(%arg391) <{binding = @zkl_binding_3, parameters = ["1"], site = "s3"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%888)[^bb14, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb8(%889: !runtime.scope):  // pred: ^bb5
      %890 = "func.call"(%889) <{callee = @zkl_control_8}> : (!runtime.scope) -> !exec.outcome<>
      %891 = "runtime.exit_scope"(%889, %890) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%891)[^bb9, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb9(%892: !runtime.transfer<>):  // pred: ^bb8
      %893 = "runtime.accept_transfer"(%arg391, %892) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%893)[^bb10, ^bb2] : (!exec.outcome<>) -> ()
    ^bb10:  // pred: ^bb9
      "cf.br"()[^bb7] : () -> ()
    ^bb11(%894: !runtime.scope):  // pred: ^bb6
      %895 = "func.call"(%894) <{callee = @zkl_control_9}> : (!runtime.scope) -> !exec.outcome<>
      %896 = "runtime.exit_scope"(%894, %895) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%896)[^bb12, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb12(%897: !runtime.transfer<>):  // pred: ^bb11
      %898 = "runtime.accept_transfer"(%arg391, %897) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%898)[^bb13, ^bb2] : (!exec.outcome<>) -> ()
    ^bb13:  // pred: ^bb12
      "cf.br"()[^bb7] : () -> ()
    ^bb14(%899: ui64):  // pred: ^bb7
      %900 = "exec.apply"(%arg391) <{binding = @zkl_binding_3, parameters = ["0"], site = "s5"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%900)[^bb15, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb15(%901: ui64):  // pred: ^bb14
      %902 = "exec.range"(%arg391, %901, %arg392) <{site = "s6"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%902)[^bb16, ^bb2] : (!exec.outcome<(i64, i64)>) -> ()
    ^bb16(%903: i64, %904: i64):  // pred: ^bb15
      %905 = "runtime.borrow_transfer"(%arg391, %899) : (!runtime.scope, ui64) -> !runtime.transfer<(ui64)>
      "cf.br"(%903, %905)[^bb17] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb17(%906: i64, %907: !runtime.transfer<(ui64)>):  // 2 preds: ^bb16, ^bb20
      %908 = "arith.cmpi"(%906, %904) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%908, %907)[^bb18, ^bb19] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(ui64)>) -> ()
    ^bb18:  // pred: ^bb17
      %909 = "runtime.iteration"(%arg391, %906) <{site = "s6"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%909)[^bb22, ^bb21] : (!exec.outcome<(ui64)>) -> ()
    ^bb19(%910: !runtime.transfer<(ui64)>):  // pred: ^bb17
      %911 = "runtime.accept_transfer"(%arg391, %910) : (!runtime.scope, !runtime.transfer<(ui64)>) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%911)[^bb25, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb20(%912: !runtime.transfer<(ui64)>):  // pred: ^bb24
      %913 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %914 = "arith.addi"(%906, %913) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%914, %912)[^bb17] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb21(%915: !exec.stop):  // 3 preds: ^bb18, ^bb22, ^bb23
      "runtime.release_transfer"(%907) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%915)[^bb2] : (!exec.stop) -> ()
    ^bb22(%916: ui64):  // pred: ^bb18
      %917 = "runtime.transfer_values"(%907) : (!runtime.transfer<(ui64)>) -> ui64
      %918 = "runtime.enter_scope"(%arg391, %906, %916, %917) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 2>, site = "s6"}> : (!runtime.scope, i64, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%918)[^bb23, ^bb21] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb23(%919: !runtime.scope):  // pred: ^bb22
      %920 = "func.call"(%919, %916, %917) <{callee = @zkl_control_10}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      %921 = "runtime.exit_scope"(%919, %920) : (!runtime.scope, !exec.outcome<(ui64)>) -> !exec.outcome<(!runtime.transfer<(ui64)>)>
      "exec.dispatch"(%921)[^bb24, ^bb21] : (!exec.outcome<(!runtime.transfer<(ui64)>)>) -> ()
    ^bb24(%922: !runtime.transfer<(ui64)>):  // pred: ^bb23
      "runtime.release_transfer"(%907) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%922)[^bb20] : (!runtime.transfer<(ui64)>) -> ()
    ^bb25(%923: ui64):  // pred: ^bb19
      %924 = "exec.returned"(%923) : (ui64) -> !exec.outcome<(ui64)>
      "func.return"(%924) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561724h726f7773", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_8", sym_visibility = "private"}> ({
    ^bb0(%arg390: !runtime.scope):
      %877 = "exec.complete"(%arg390) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%877) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_9", sym_visibility = "private"}> ({
    ^bb0(%arg389: !runtime.scope):
      %874 = "exec.reject"(%arg389) <{reason = "reject", site = "s2_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%874)[^bb1] : (!exec.stop) -> ()
    ^bb1(%875: !exec.stop):  // pred: ^bb0
      %876 = "exec.failed"(%875) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%876) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "zkl_control_10", sym_visibility = "private"}> ({
    ^bb0(%arg386: !runtime.scope, %arg387: ui64, %arg388: ui64):
      %867 = "exec.apply"(%arg386) <{binding = @zkl_binding_3, parameters = ["2"], site = "s7"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%867)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%868: ui64):  // pred: ^bb0
      %869 = "exec.apply"(%arg386, %arg388, %868) <{binding = @zkl_binding_9, parameters = [], site = "s8"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%869)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%870: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %871 = "exec.failed"(%870) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%871) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%872: ui64):  // pred: ^bb1
      %873 = "exec.complete"(%arg386, %872) : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "func.return"(%873) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be", sym_visibility = "private"}> ({
    ^bb0(%arg381: !runtime.scope, %arg382: !algebra.field_vector<"bls12-381.fr">, %arg383: ui64, %arg384: ui64, %arg385: !algebra.field_vector<"bls12-381.fr">):
      %860 = "func.call"(%arg381, %arg382, %arg383, %arg384, %arg385) <{callee = @zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2}> {runtime.site = "s0"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%860)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb1(%861: !algebra.field_vector<"bls12-381.fr">, %862: ui64, %863: ui64):  // pred: ^bb0
      %864 = "exec.returned"(%861, %862, %863) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%864) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb2(%865: !exec.stop):  // pred: ^bb0
      %866 = "exec.failed"(%865) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%866) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e65617210h6669785f707265666978", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_195a79478f48dffc2a6917273d8317df0fabae786920a46fa2ac6b2737144299", sym_visibility = "private"}> ({
    ^bb0(%arg376: !runtime.scope, %arg377: !algebra.field_vector<"bls12-381.fr">, %arg378: ui64, %arg379: ui64, %arg380: !algebra.field<"bls12-381.fr">):
      %853 = "func.call"(%arg376, %arg377, %arg378, %arg379, %arg380) <{callee = @zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d}> {runtime.site = "s2"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%853)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb1(%854: !algebra.field_vector<"bls12-381.fr">, %855: ui64, %856: ui64):  // pred: ^bb0
      %857 = "exec.returned"(%854, %855, %856) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%857) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb2(%858: !exec.stop):  // pred: ^bb0
      %859 = "exec.failed"(%858) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%859) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["zks_50b2228592370f9a2bce2e71277fbb9bf36d691d6ece4416923708e3a0c063ae", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d", sym_visibility = "private"}> ({
    ^bb0(%arg371: !runtime.scope, %arg372: !algebra.field_vector<"bls12-381.fr">, %arg373: ui64, %arg374: ui64, %arg375: !algebra.field<"bls12-381.fr">):
      %841 = "func.call"(%arg371, %arg372, %arg373, %arg374) <{callee = @zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087}> {runtime.site = "s0"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%841)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%842: !algebra.field_vector<"bls12-381.fr">, %843: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %844 = "exec.collect"(%arg371, %842, %843, %arg375) <{body = @zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body, domain = @zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_domain, site = "s4"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%844)[^bb3, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%845: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %846 = "exec.failed"(%845) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%846) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb3(%847: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb1
      %848 = "exec.apply"(%arg371) <{binding = @zkl_binding_3, parameters = ["1"], site = "s7"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%848)[^bb4, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%849: ui64):  // pred: ^bb3
      %850 = "exec.apply"(%arg371, %arg373, %849) <{binding = @zkl_binding_10, parameters = [], site = "s8"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%850)[^bb5, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%851: ui64):  // pred: ^bb4
      %852 = "exec.returned"(%847, %851, %arg374) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%852) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561729h6669785f6669727374", []]} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, sym_name = "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_domain", sym_visibility = "private"}> ({
    ^bb0(%arg369: !algebra.field_vector<"bls12-381.fr">, %arg370: !algebra.field_vector<"bls12-381.fr">):
      %838 = "data.domain_elements"(%arg369) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %839 = "data.domain_elements"(%arg370) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %840 = "data.domain_zip"(%838, %839) : (!data.domain<!algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%840) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body", sym_visibility = "private"}> ({
    ^bb0(%arg363: !runtime.scope, %arg364: !algebra.field<"bls12-381.fr">, %arg365: !algebra.field<"bls12-381.fr">, %arg366: !algebra.field_vector<"bls12-381.fr">, %arg367: !algebra.field_vector<"bls12-381.fr">, %arg368: !algebra.field<"bls12-381.fr">):
      %833 = "exec.compute"(%arg363, %arg364, %arg365, %arg368) <{callee = @zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5, site = "body"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%833)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%834: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %835 = "exec.returned"(%834) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%835) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%836: !exec.stop):  // pred: ^bb0
      %837 = "exec.failed"(%836) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%837) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087", sym_visibility = "private"}> ({
    ^bb0(%arg359: !runtime.scope, %arg360: !algebra.field_vector<"bls12-381.fr">, %arg361: ui64, %arg362: ui64):
      %809 = "exec.apply"(%arg359) <{binding = @zkl_binding_3, parameters = ["0"], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%809)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%810: ui64):  // pred: ^bb0
      %811 = "func.call"(%arg359, %810, %arg361) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s2"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%811)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%812: !exec.stop):  // 10 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12
      %813 = "exec.failed"(%812) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%813) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%814: i1):  // pred: ^bb1
      %815 = "exec.test"(%arg359, %814) <{site = "s3"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%815)[^bb4, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb4(%816: i1):  // pred: ^bb3
      "cf.cond_br"(%816)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %817 = "runtime.enter_scope"(%arg359) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s3"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%817)[^bb8, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %818 = "runtime.enter_scope"(%arg359) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s3"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%818)[^bb11, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // 2 preds: ^bb10, ^bb13
      %819 = "exec.apply"(%arg359, %arg360) <{binding = @zkl_binding_11, parameters = [], site = "s5"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%819)[^bb14, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%820: !runtime.scope):  // pred: ^bb5
      %821 = "func.call"(%820) <{callee = @zkl_control_11}> : (!runtime.scope) -> !exec.outcome<>
      %822 = "runtime.exit_scope"(%820, %821) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%822)[^bb9, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb9(%823: !runtime.transfer<>):  // pred: ^bb8
      %824 = "runtime.accept_transfer"(%arg359, %823) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%824)[^bb10, ^bb2] : (!exec.outcome<>) -> ()
    ^bb10:  // pred: ^bb9
      "cf.br"()[^bb7] : () -> ()
    ^bb11(%825: !runtime.scope):  // pred: ^bb6
      %826 = "func.call"(%825) <{callee = @zkl_control_12}> : (!runtime.scope) -> !exec.outcome<>
      %827 = "runtime.exit_scope"(%825, %826) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%827)[^bb12, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb12(%828: !runtime.transfer<>):  // pred: ^bb11
      %829 = "runtime.accept_transfer"(%arg359, %828) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%829)[^bb13, ^bb2] : (!exec.outcome<>) -> ()
    ^bb13:  // pred: ^bb12
      "cf.br"()[^bb7] : () -> ()
    ^bb14(%830: !algebra.field_vector<"bls12-381.fr">, %831: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb7
      %832 = "exec.returned"(%830, %831) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%832) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561726h68616c766573", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_11", sym_visibility = "private"}> ({
    ^bb0(%arg358: !runtime.scope):
      %808 = "exec.complete"(%arg358) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%808) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_12", sym_visibility = "private"}> ({
    ^bb0(%arg357: !runtime.scope):
      %805 = "exec.reject"(%arg357) <{reason = "reject", site = "s3_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%805)[^bb1] : (!exec.stop) -> ()
    ^bb1(%806: !exec.stop):  // pred: ^bb0
      %807 = "exec.failed"(%806) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%807) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5", sym_visibility = "private"}> ({
    ^bb0(%arg354: !algebra.field<"bls12-381.fr">, %arg355: !algebra.field<"bls12-381.fr">, %arg356: !algebra.field<"bls12-381.fr">):
      %802 = "algebra.field_subtract"(%arg355, %arg354) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %803 = "algebra.field_multiply"(%802, %arg356) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %804 = "algebra.field_add"(%arg354, %803) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%804) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2", sym_visibility = "private"}> ({
    ^bb0(%arg349: !runtime.scope, %arg350: !algebra.field_vector<"bls12-381.fr">, %arg351: ui64, %arg352: ui64, %arg353: !algebra.field_vector<"bls12-381.fr">):
      %795 = "exec.fold"(%arg349, %arg353, %arg350, %arg351, %arg352) <{domain = @finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_domain, site = "s0", step = @finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%795)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb1(%796: !algebra.field_vector<"bls12-381.fr">, %797: ui64, %798: ui64):  // pred: ^bb0
      %799 = "exec.returned"(%796, %797, %798) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%799) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb2(%800: !exec.stop):  // pred: ^bb0
      %801 = "exec.failed"(%800) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%801) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg348: !algebra.field_vector<"bls12-381.fr">):
      %794 = "data.domain_elements"(%arg348) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%794) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg342: !runtime.scope, %arg343: !algebra.field_vector<"bls12-381.fr">, %arg344: ui64, %arg345: ui64, %arg346: !algebra.field<"bls12-381.fr">, %arg347: !algebra.field_vector<"bls12-381.fr">):
      %787 = "func.call"(%arg342, %arg343, %arg344, %arg345, %arg346) <{callee = @zkl_195a79478f48dffc2a6917273d8317df0fabae786920a46fa2ac6b2737144299}> {runtime.site = "body"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%787)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb1(%788: !algebra.field_vector<"bls12-381.fr">, %789: ui64, %790: ui64):  // pred: ^bb0
      %791 = "exec.returned"(%788, %789, %790) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%791) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb2(%792: !exec.stop):  // pred: ^bb0
      %793 = "exec.failed"(%792) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%793) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">, sym_name = "zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", sym_visibility = "private"}> ({
    ^bb0(%arg339: !algebra.field_vector<"bls12-381.fr">, %arg340: ui64, %arg341: ui64):
      "func.return"(%arg339) : (!algebra.field_vector<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_8c63ad97d926a7762c597860addde408bcd2077ea9cda1b99df123dc13e64af6", sym_visibility = "private"}> ({
    ^bb0(%arg331: !runtime.scope, %arg332: !algebra.field_vector<"bls12-381.fr">, %arg333: !algebra.field_vector<"bls12-381.fr">, %arg334: !algebra.field_vector<"bls12-381.fr">, %arg335: ui64, %arg336: ui64, %arg337: ui64, %arg338: ui64):
      %753 = "exec.apply"(%arg331) <{binding = @zkl_binding_3, parameters = ["0"], site = "s2"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%753)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%754: ui64):  // pred: ^bb0
      %755 = "exec.apply"(%arg331, %arg335, %arg338) <{binding = @zkl_binding_10, parameters = [], site = "s3"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%755)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%756: !exec.stop):  // 7 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb9, ^bb11
      %757 = "exec.failed"(%756) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%757) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%758: ui64):  // pred: ^bb1
      %759 = "exec.apply"(%arg331) <{binding = @zkl_binding_3, parameters = ["1"], site = "s4"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%759)[^bb4, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%760: ui64):  // pred: ^bb3
      %761 = "exec.apply"(%arg331, %758, %760) <{binding = @zkl_binding_10, parameters = [], site = "s5"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%761)[^bb5, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%762: ui64):  // pred: ^bb4
      %763 = "exec.range"(%arg331, %754, %762) <{site = "s10"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%763)[^bb6, ^bb2] : (!exec.outcome<(i64, i64)>) -> ()
    ^bb6(%764: i64, %765: i64):  // pred: ^bb5
      %766 = "runtime.borrow_transfer"(%arg331, %arg334, %arg335) : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>
      "cf.br"(%764, %766)[^bb7] : (i64, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb7(%767: i64, %768: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>):  // 2 preds: ^bb6, ^bb10
      %769 = "arith.cmpi"(%767, %765) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%769, %768)[^bb8, ^bb9] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb8:  // pred: ^bb7
      %770 = "runtime.iteration"(%arg331, %767) <{site = "s10"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%770)[^bb12, ^bb11] : (!exec.outcome<(ui64)>) -> ()
    ^bb9(%771: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>):  // pred: ^bb7
      %772 = "runtime.accept_transfer"(%arg331, %771) : (!runtime.scope, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>
      "exec.dispatch"(%772)[^bb15, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb10(%773: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>):  // pred: ^bb14
      %774 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %775 = "arith.addi"(%767, %774) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%775, %773)[^bb7] : (i64, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb11(%776: !exec.stop):  // 3 preds: ^bb8, ^bb12, ^bb13
      "runtime.release_transfer"(%768) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
      "cf.br"(%776)[^bb2] : (!exec.stop) -> ()
    ^bb12(%777: ui64):  // pred: ^bb8
      %778:2 = "runtime.transfer_values"(%768) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> (!algebra.field_vector<"bls12-381.fr">, ui64)
      %779 = "runtime.enter_scope"(%arg331, %767, %777, %778#0, %778#1, %arg332, %arg333, %arg336, %arg337) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 7>, site = "s10"}> : (!runtime.scope, i64, ui64, !algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%779)[^bb13, ^bb11] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb13(%780: !runtime.scope):  // pred: ^bb12
      %781 = "func.call"(%780, %777, %778#0, %778#1, %arg332, %arg333, %arg336, %arg337) <{callee = @zkl_control_13}> : (!runtime.scope, ui64, !algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>
      %782 = "runtime.exit_scope"(%780, %781) : (!runtime.scope, !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> !exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>)>
      "exec.dispatch"(%782)[^bb14, ^bb11] : (!exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>)>) -> ()
    ^bb14(%783: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>):  // pred: ^bb13
      "runtime.release_transfer"(%768) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
      "cf.br"(%783)[^bb10] : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb15(%784: !algebra.field_vector<"bls12-381.fr">, %785: ui64):  // pred: ^bb9
      %786 = "exec.returned"(%784) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%786) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7212h76616c7565735f62656c6f77", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, !algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>, no_inline, sym_name = "zkl_control_13", sym_visibility = "private"}> ({
    ^bb0(%arg323: !runtime.scope, %arg324: ui64, %arg325: !algebra.field_vector<"bls12-381.fr">, %arg326: ui64, %arg327: !algebra.field_vector<"bls12-381.fr">, %arg328: !algebra.field_vector<"bls12-381.fr">, %arg329: ui64, %arg330: ui64):
      %740 = "exec.apply"(%arg323) <{binding = @zkl_binding_3, parameters = ["1"], site = "s11"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%740)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%741: ui64):  // pred: ^bb0
      %742 = "exec.apply"(%arg323, %arg326, %741) <{binding = @zkl_binding_10, parameters = [], site = "s12"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%742)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%743: !exec.stop):  // 5 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5
      %744 = "exec.failed"(%743) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>
      "func.return"(%744) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb3(%745: ui64):  // pred: ^bb1
      %746 = "func.call"(%arg323, %arg327, %745, %arg329) <{callee = @zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e}> {runtime.site = "s14"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%746)[^bb4, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb4(%747: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb3
      %748 = "func.call"(%arg323, %arg328, %745, %arg329) <{callee = @zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e}> {runtime.site = "s15"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%748)[^bb5, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb5(%749: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb4
      %750 = "func.call"(%arg323, %747, %749, %arg325, %arg330) <{callee = @zkl_3a99bc0fa1dab7cb27c9ec80754c3782b0a32e76ddc961a50e12c24c6cbff683}> {runtime.site = "s16"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%750)[^bb6, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb6(%751: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb5
      %752 = "exec.complete"(%arg323, %751, %745) : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>
      "func.return"(%752) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", sym_visibility = "private"}> ({
    ^bb0(%arg319: !runtime.scope, %arg320: !algebra.field_vector<"bls12-381.fr">, %arg321: ui64, %arg322: ui64):
      %712 = "exec.apply"(%arg319) <{binding = @zkl_binding_3, parameters = ["0"], site = "s2"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%712)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%713: ui64):  // pred: ^bb0
      %714 = "exec.range"(%arg319, %713, %arg322) <{site = "s4"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%714)[^bb3, ^bb2] : (!exec.outcome<(i64, i64)>) -> ()
    ^bb2(%715: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb6, ^bb8
      %716 = "exec.failed"(%715) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%716) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%717: i64, %718: i64):  // pred: ^bb1
      %719 = "runtime.borrow_transfer"(%arg319, %arg320, %arg322) : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>
      "cf.br"(%717, %719)[^bb4] : (i64, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb4(%720: i64, %721: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>):  // 2 preds: ^bb3, ^bb7
      %722 = "arith.cmpi"(%720, %718) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%722, %721)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb5:  // pred: ^bb4
      %723 = "runtime.iteration"(%arg319, %720) <{site = "s4"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%723)[^bb9, ^bb8] : (!exec.outcome<(ui64)>) -> ()
    ^bb6(%724: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>):  // pred: ^bb4
      %725 = "runtime.accept_transfer"(%arg319, %724) : (!runtime.scope, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>
      "exec.dispatch"(%725)[^bb12, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb7(%726: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>):  // pred: ^bb11
      %727 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %728 = "arith.addi"(%720, %727) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%728, %726)[^bb4] : (i64, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb8(%729: !exec.stop):  // 3 preds: ^bb5, ^bb9, ^bb10
      "runtime.release_transfer"(%721) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
      "cf.br"(%729)[^bb2] : (!exec.stop) -> ()
    ^bb9(%730: ui64):  // pred: ^bb5
      %731:2 = "runtime.transfer_values"(%721) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> (!algebra.field_vector<"bls12-381.fr">, ui64)
      %732 = "runtime.enter_scope"(%arg319, %720, %730, %731#0, %731#1, %arg321) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 4>, site = "s4"}> : (!runtime.scope, i64, ui64, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%732)[^bb10, ^bb8] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb10(%733: !runtime.scope):  // pred: ^bb9
      %734 = "func.call"(%733, %730, %731#0, %731#1, %arg321) <{callee = @zkl_control_14}> : (!runtime.scope, ui64, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>
      %735 = "runtime.exit_scope"(%733, %734) : (!runtime.scope, !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> !exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>)>
      "exec.dispatch"(%735)[^bb11, ^bb8] : (!exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>)>) -> ()
    ^bb11(%736: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>):  // pred: ^bb10
      "runtime.release_transfer"(%721) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
      "cf.br"(%736)[^bb7] : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb12(%737: !algebra.field_vector<"bls12-381.fr">, %738: ui64):  // pred: ^bb6
      %739 = "exec.returned"(%737) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%739) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7212h73656c6563745f626c6f636b", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>, no_inline, sym_name = "zkl_control_14", sym_visibility = "private"}> ({
    ^bb0(%arg314: !runtime.scope, %arg315: ui64, %arg316: !algebra.field_vector<"bls12-381.fr">, %arg317: ui64, %arg318: ui64):
      %673 = "exec.apply"(%arg314) <{binding = @zkl_binding_3, parameters = ["1"], site = "s5"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%673)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%674: ui64):  // pred: ^bb0
      %675 = "exec.apply"(%arg314, %arg317, %674) <{binding = @zkl_binding_10, parameters = [], site = "s6"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%675)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%676: !exec.stop):  // 16 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb10, ^bb12, ^bb13, ^bb15, ^bb16, ^bb18, ^bb19
      %677 = "exec.failed"(%676) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>
      "func.return"(%677) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb3(%678: ui64):  // pred: ^bb1
      %679 = "func.call"(%arg314, %678) <{callee = @s3h676b7212h706f7765725f6f665f74776f}> {runtime.site = "s8"} : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%679)[^bb4, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%680: ui64):  // pred: ^bb3
      %681 = "exec.apply"(%arg314, %arg318, %680) <{binding = @zkl_binding_7, parameters = [], site = "s9"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%681)[^bb5, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%682: ui64):  // pred: ^bb4
      %683 = "exec.apply"(%arg314) <{binding = @zkl_binding_3, parameters = ["2"], site = "s10"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%683)[^bb6, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb6(%684: ui64):  // pred: ^bb5
      %685 = "exec.apply"(%arg314, %682, %684) <{binding = @zkl_binding_5, parameters = [], site = "s11"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%685)[^bb7, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb7(%686: ui64):  // pred: ^bb6
      %687 = "exec.apply"(%arg314, %arg316) <{binding = @zkl_binding_11, parameters = [], site = "s13"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%687)[^bb8, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%688: !algebra.field_vector<"bls12-381.fr">, %689: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb7
      %690 = "exec.apply"(%arg314) <{binding = @zkl_binding_3, parameters = ["1"], site = "s15"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%690)[^bb9, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb9(%691: ui64):  // pred: ^bb8
      %692 = "exec.apply"(%arg314, %686, %691) <{binding = @zkl_binding_6, parameters = [], site = "s16"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%692)[^bb10, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb10(%693: i1):  // pred: ^bb9
      %694 = "exec.test"(%arg314, %693) <{site = "s19"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%694)[^bb11, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb11(%695: i1):  // pred: ^bb10
      "cf.cond_br"(%695)[^bb12, ^bb13] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb12:  // pred: ^bb11
      %696 = "runtime.enter_scope"(%arg314, %688, %689) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "then", site = "s19"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%696)[^bb15, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb13:  // pred: ^bb11
      %697 = "runtime.enter_scope"(%arg314, %688, %689) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "else", site = "s19"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%697)[^bb18, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb14(%698: !algebra.field_vector<"bls12-381.fr">):  // 2 preds: ^bb17, ^bb20
      %699 = "exec.complete"(%arg314, %698, %678) : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>
      "func.return"(%699) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb15(%700: !runtime.scope):  // pred: ^bb12
      %701 = "func.call"(%700, %688, %689) <{callee = @zkl_control_15}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      %702 = "runtime.exit_scope"(%700, %701) : (!runtime.scope, !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>)>
      "exec.dispatch"(%702)[^bb16, ^bb2] : (!exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>)>) -> ()
    ^bb16(%703: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>):  // pred: ^bb15
      %704 = "runtime.accept_transfer"(%arg314, %703) : (!runtime.scope, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%704)[^bb17, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb17(%705: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb16
      "cf.br"(%705)[^bb14] : (!algebra.field_vector<"bls12-381.fr">) -> ()
    ^bb18(%706: !runtime.scope):  // pred: ^bb13
      %707 = "func.call"(%706, %688, %689) <{callee = @zkl_control_16}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      %708 = "runtime.exit_scope"(%706, %707) : (!runtime.scope, !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>)>
      "exec.dispatch"(%708)[^bb19, ^bb2] : (!exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>)>) -> ()
    ^bb19(%709: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>):  // pred: ^bb18
      %710 = "runtime.accept_transfer"(%arg314, %709) : (!runtime.scope, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%710)[^bb20, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb20(%711: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb19
      "cf.br"(%711)[^bb14] : (!algebra.field_vector<"bls12-381.fr">) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_15", sym_visibility = "private"}> ({
    ^bb0(%arg311: !runtime.scope, %arg312: !algebra.field_vector<"bls12-381.fr">, %arg313: !algebra.field_vector<"bls12-381.fr">):
      %672 = "exec.complete"(%arg311, %arg313) : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%672) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_16", sym_visibility = "private"}> ({
    ^bb0(%arg308: !runtime.scope, %arg309: !algebra.field_vector<"bls12-381.fr">, %arg310: !algebra.field_vector<"bls12-381.fr">):
      %671 = "exec.complete"(%arg308, %arg309) : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%671) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "s3h676b7212h706f7765725f6f665f74776f", sym_visibility = "private"}> ({
    ^bb0(%arg306: !runtime.scope, %arg307: ui64):
      %642 = "exec.apply"(%arg306) <{binding = @zkl_binding_3, parameters = ["1"], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%642)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%643: ui64):  // pred: ^bb0
      %644 = "exec.apply"(%arg306) <{binding = @zkl_binding_3, parameters = ["0"], site = "s2"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%644)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%645: !exec.stop):  // 5 preds: ^bb0, ^bb1, ^bb3, ^bb7, ^bb9
      %646 = "exec.failed"(%645) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%646) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%647: ui64):  // pred: ^bb1
      %648 = "exec.range"(%arg306, %647, %arg307) <{site = "s3"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%648)[^bb4, ^bb2] : (!exec.outcome<(i64, i64)>) -> ()
    ^bb4(%649: i64, %650: i64):  // pred: ^bb3
      %651 = "runtime.borrow_transfer"(%arg306, %643) : (!runtime.scope, ui64) -> !runtime.transfer<(ui64)>
      "cf.br"(%649, %651)[^bb5] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb5(%652: i64, %653: !runtime.transfer<(ui64)>):  // 2 preds: ^bb4, ^bb8
      %654 = "arith.cmpi"(%652, %650) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%654, %653)[^bb6, ^bb7] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(ui64)>) -> ()
    ^bb6:  // pred: ^bb5
      %655 = "runtime.iteration"(%arg306, %652) <{site = "s3"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%655)[^bb10, ^bb9] : (!exec.outcome<(ui64)>) -> ()
    ^bb7(%656: !runtime.transfer<(ui64)>):  // pred: ^bb5
      %657 = "runtime.accept_transfer"(%arg306, %656) : (!runtime.scope, !runtime.transfer<(ui64)>) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%657)[^bb13, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb8(%658: !runtime.transfer<(ui64)>):  // pred: ^bb12
      %659 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %660 = "arith.addi"(%652, %659) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%660, %658)[^bb5] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb9(%661: !exec.stop):  // 3 preds: ^bb6, ^bb10, ^bb11
      "runtime.release_transfer"(%653) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%661)[^bb2] : (!exec.stop) -> ()
    ^bb10(%662: ui64):  // pred: ^bb6
      %663 = "runtime.transfer_values"(%653) : (!runtime.transfer<(ui64)>) -> ui64
      %664 = "runtime.enter_scope"(%arg306, %652, %662, %663) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 2>, site = "s3"}> : (!runtime.scope, i64, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%664)[^bb11, ^bb9] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb11(%665: !runtime.scope):  // pred: ^bb10
      %666 = "func.call"(%665, %662, %663) <{callee = @zkl_control_17}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      %667 = "runtime.exit_scope"(%665, %666) : (!runtime.scope, !exec.outcome<(ui64)>) -> !exec.outcome<(!runtime.transfer<(ui64)>)>
      "exec.dispatch"(%667)[^bb12, ^bb9] : (!exec.outcome<(!runtime.transfer<(ui64)>)>) -> ()
    ^bb12(%668: !runtime.transfer<(ui64)>):  // pred: ^bb11
      "runtime.release_transfer"(%653) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%668)[^bb8] : (!runtime.transfer<(ui64)>) -> ()
    ^bb13(%669: ui64):  // pred: ^bb7
      %670 = "exec.returned"(%669) : (ui64) -> !exec.outcome<(ui64)>
      "func.return"(%670) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.origin = ["s3h676b7212h706f7765725f6f665f74776f", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "zkl_control_17", sym_visibility = "private"}> ({
    ^bb0(%arg303: !runtime.scope, %arg304: ui64, %arg305: ui64):
      %635 = "exec.apply"(%arg303) <{binding = @zkl_binding_3, parameters = ["2"], site = "s4"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%635)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%636: ui64):  // pred: ^bb0
      %637 = "exec.apply"(%arg303, %arg305, %636) <{binding = @zkl_binding_9, parameters = [], site = "s5"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%637)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%638: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %639 = "exec.failed"(%638) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%639) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%640: ui64):  // pred: ^bb1
      %641 = "exec.complete"(%arg303, %640) : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "func.return"(%641) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_3a99bc0fa1dab7cb27c9ec80754c3782b0a32e76ddc961a50e12c24c6cbff683", sym_visibility = "private"}> ({
    ^bb0(%arg298: !runtime.scope, %arg299: !algebra.field_vector<"bls12-381.fr">, %arg300: !algebra.field_vector<"bls12-381.fr">, %arg301: !algebra.field_vector<"bls12-381.fr">, %arg302: ui64):
      %600 = "func.call"(%arg298, %arg302) <{callee = @s3h676b7212h706f7765725f6f665f74776f}> {runtime.site = "s0"} : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%600)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%601: ui64):  // pred: ^bb0
      %602 = "func.call"(%arg298, %arg301, %601) <{callee = @zkl_afd97de07c9ccae9db68186ebf66098aed7daffb4b11c598d0da5cd116df8490}> {runtime.site = "s2"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%602)[^bb3, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%603: !exec.stop):  // 8 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb10, ^bb12
      %604 = "exec.failed"(%603) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%604) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%605: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb1
      %606 = "func.call"(%arg298, %arg301, %601) <{callee = @zkl_33f3047479634e63ecd16a0855f88ad8af019c37d677a4ffe6f5bacc63307947}> {runtime.site = "s4"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%606)[^bb4, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb4(%607: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb3
      %608 = "exec.apply"(%arg298) <{binding = @zkl_binding_0, parameters = [], site = "s6"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%608)[^bb5, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb5(%609: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb4
      %610 = "exec.apply"(%arg298) <{binding = @zkl_binding_3, parameters = ["0"], site = "s8"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%610)[^bb6, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb6(%611: ui64):  // pred: ^bb5
      %612 = "exec.range"(%arg298, %611, %601) <{site = "s14"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%612)[^bb7, ^bb2] : (!exec.outcome<(i64, i64)>) -> ()
    ^bb7(%613: i64, %614: i64):  // pred: ^bb6
      %615 = "runtime.borrow_transfer"(%arg298, %609) : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>
      "cf.br"(%613, %615)[^bb8] : (i64, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%616: i64, %617: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>):  // 2 preds: ^bb7, ^bb11
      %618 = "arith.cmpi"(%616, %614) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%618, %617)[^bb9, ^bb10] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb9:  // pred: ^bb8
      %619 = "runtime.iteration"(%arg298, %616) <{site = "s14"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%619)[^bb13, ^bb12] : (!exec.outcome<(ui64)>) -> ()
    ^bb10(%620: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>):  // pred: ^bb8
      %621 = "runtime.accept_transfer"(%arg298, %620) : (!runtime.scope, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%621)[^bb16, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb11(%622: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>):  // pred: ^bb15
      %623 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %624 = "arith.addi"(%616, %623) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%624, %622)[^bb8] : (i64, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb12(%625: !exec.stop):  // 3 preds: ^bb9, ^bb13, ^bb14
      "runtime.release_transfer"(%617) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
      "cf.br"(%625)[^bb2] : (!exec.stop) -> ()
    ^bb13(%626: ui64):  // pred: ^bb9
      %627 = "runtime.transfer_values"(%617) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> !algebra.field_vector<"bls12-381.fr">
      %628 = "runtime.enter_scope"(%arg298, %616, %626, %627, %arg299, %arg300, %arg302, %605, %607) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 7>, site = "s14"}> : (!runtime.scope, i64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%628)[^bb14, ^bb12] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb14(%629: !runtime.scope):  // pred: ^bb13
      %630 = "func.call"(%629, %626, %627, %arg299, %arg300, %arg302, %605, %607) <{callee = @zkl_control_18}> : (!runtime.scope, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      %631 = "runtime.exit_scope"(%629, %630) : (!runtime.scope, !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>)>
      "exec.dispatch"(%631)[^bb15, ^bb12] : (!exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>)>) -> ()
    ^bb15(%632: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>):  // pred: ^bb14
      "runtime.release_transfer"(%617) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
      "cf.br"(%632)[^bb11] : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb16(%633: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb10
      %634 = "exec.returned"(%633) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%634) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7212h6c617965725f76616c756573", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_18", sym_visibility = "private"}> ({
    ^bb0(%arg290: !runtime.scope, %arg291: ui64, %arg292: !algebra.field_vector<"bls12-381.fr">, %arg293: !algebra.field_vector<"bls12-381.fr">, %arg294: !algebra.field_vector<"bls12-381.fr">, %arg295: ui64, %arg296: !algebra.field_vector<"bls12-381.fr">, %arg297: !algebra.field_vector<"bls12-381.fr">):
      %587 = "func.call"(%arg290, %arg293, %arg291, %arg295) <{callee = @zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e}> {runtime.site = "s15"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%587)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%588: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %589 = "func.call"(%arg290, %arg294, %arg291, %arg295) <{callee = @zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e}> {runtime.site = "s17"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%589)[^bb3, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%590: !exec.stop):  // 5 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5
      %591 = "exec.failed"(%590) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%591) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%592: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb1
      %593 = "exec.collect"(%arg290, %588, %592, %arg296, %arg297) <{body = @zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_body, domain = @zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_domain, site = "s19"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%593)[^bb4, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb4(%594: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb3
      %595 = "exec.apply"(%arg290, %594) <{binding = @zkl_binding_4, parameters = [], site = "s20"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%595)[^bb5, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb5(%596: !algebra.field<"bls12-381.fr">):  // pred: ^bb4
      %597 = "exec.apply"(%arg290, %arg292, %596) <{binding = @zkl_binding_1, parameters = [], site = "s21"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%597)[^bb6, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb6(%598: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb5
      %599 = "exec.complete"(%arg290, %598) : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%599) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, sym_name = "zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_domain", sym_visibility = "private"}> ({
    ^bb0(%arg286: !algebra.field_vector<"bls12-381.fr">, %arg287: !algebra.field_vector<"bls12-381.fr">, %arg288: !algebra.field_vector<"bls12-381.fr">, %arg289: !algebra.field_vector<"bls12-381.fr">):
      %580 = "data.domain_elements"(%arg286) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %581 = "data.domain_elements"(%arg287) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %582 = "data.domain_zip"(%580, %581) : (!data.domain<!algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      %583 = "data.domain_elements"(%arg288) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %584 = "data.domain_zip"(%582, %583) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      %585 = "data.domain_elements"(%arg289) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %586 = "data.domain_zip"(%584, %585) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%586) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_body", sym_visibility = "private"}> ({
    ^bb0(%arg277: !runtime.scope, %arg278: !algebra.field<"bls12-381.fr">, %arg279: !algebra.field<"bls12-381.fr">, %arg280: !algebra.field<"bls12-381.fr">, %arg281: !algebra.field<"bls12-381.fr">, %arg282: !algebra.field_vector<"bls12-381.fr">, %arg283: !algebra.field_vector<"bls12-381.fr">, %arg284: !algebra.field_vector<"bls12-381.fr">, %arg285: !algebra.field_vector<"bls12-381.fr">):
      %575 = "exec.compute"(%arg277, %arg278, %arg279, %arg280, %arg281) <{callee = @zkl_6b3d366572d1ba53650a202f39ff52a2f298a1591829443fbeaa34ef3974f084, site = "body"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%575)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%576: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %577 = "exec.returned"(%576) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%577) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%578: !exec.stop):  // pred: ^bb0
      %579 = "exec.failed"(%578) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%579) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_body", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_afd97de07c9ccae9db68186ebf66098aed7daffb4b11c598d0da5cd116df8490", sym_visibility = "private"}> ({
    ^bb0(%arg274: !runtime.scope, %arg275: !algebra.field_vector<"bls12-381.fr">, %arg276: ui64):
      %568 = "exec.apply"(%arg274) <{binding = @zkl_binding_0, parameters = [], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%568)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%569: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %570 = "func.call"(%arg274, %569, %arg276, %arg275) <{callee = @zkl_33e26704899171b0d3e366f86377dfc6602b55f53021ce20930f7ae9e8061294}> {runtime.site = "s2"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%570)[^bb3, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%571: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %572 = "exec.failed"(%571) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%572) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%573: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb1
      %574 = "exec.returned"(%573) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%574) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b729h7265706c6963617465", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_e7a7efcd14676d32c0e577ff1097f611a3dc84c74ecaa8bfdbebb25968971255", sym_visibility = "private"}> ({
    ^bb0(%arg270: !runtime.scope, %arg271: !algebra.field_vector<"bls12-381.fr">, %arg272: !algebra.field<"bls12-381.fr">, %arg273: ui64):
      %563 = "func.call"(%arg270, %arg271, %arg272, %arg273) <{callee = @zkl_fbd2531b804047766f8107241edd0ea81368b70795e44e4d8e07484d142783bb}> {runtime.site = "s2"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%563)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%564: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %565 = "exec.returned"(%564) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%565) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%566: !exec.stop):  // pred: ^bb0
      %567 = "exec.failed"(%566) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%567) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zks_99cdc30b104640f79094177f26387b3c04df24c083a5fa7125a3fd69fc1eb459", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_fbd2531b804047766f8107241edd0ea81368b70795e44e4d8e07484d142783bb", sym_visibility = "private"}> ({
    ^bb0(%arg266: !runtime.scope, %arg267: !algebra.field_vector<"bls12-381.fr">, %arg268: !algebra.field<"bls12-381.fr">, %arg269: ui64):
      %536 = "exec.apply"(%arg266) <{binding = @zkl_binding_3, parameters = ["0"], site = "s1"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%536)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%537: ui64):  // pred: ^bb0
      %538 = "exec.range"(%arg266, %537, %arg269) <{site = "s3"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%538)[^bb3, ^bb2] : (!exec.outcome<(i64, i64)>) -> ()
    ^bb2(%539: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb6, ^bb8
      %540 = "exec.failed"(%539) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%540) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%541: i64, %542: i64):  // pred: ^bb1
      %543 = "runtime.borrow_transfer"(%arg266, %arg267) : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>
      "cf.br"(%541, %543)[^bb4] : (i64, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb4(%544: i64, %545: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>):  // 2 preds: ^bb3, ^bb7
      %546 = "arith.cmpi"(%544, %542) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%546, %545)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb5:  // pred: ^bb4
      %547 = "runtime.iteration"(%arg266, %544) <{site = "s3"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%547)[^bb9, ^bb8] : (!exec.outcome<(ui64)>) -> ()
    ^bb6(%548: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>):  // pred: ^bb4
      %549 = "runtime.accept_transfer"(%arg266, %548) : (!runtime.scope, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%549)[^bb12, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb7(%550: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>):  // pred: ^bb11
      %551 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %552 = "arith.addi"(%544, %551) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%552, %550)[^bb4] : (i64, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%553: !exec.stop):  // 3 preds: ^bb5, ^bb9, ^bb10
      "runtime.release_transfer"(%545) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
      "cf.br"(%553)[^bb2] : (!exec.stop) -> ()
    ^bb9(%554: ui64):  // pred: ^bb5
      %555 = "runtime.transfer_values"(%545) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> !algebra.field_vector<"bls12-381.fr">
      %556 = "runtime.enter_scope"(%arg266, %544, %554, %555, %arg268) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 3>, site = "s3"}> : (!runtime.scope, i64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%556)[^bb10, ^bb8] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb10(%557: !runtime.scope):  // pred: ^bb9
      %558 = "func.call"(%557, %554, %555, %arg268) <{callee = @zkl_control_19}> : (!runtime.scope, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      %559 = "runtime.exit_scope"(%557, %558) : (!runtime.scope, !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>)>
      "exec.dispatch"(%559)[^bb11, ^bb8] : (!exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>)>) -> ()
    ^bb11(%560: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>):  // pred: ^bb10
      "runtime.release_transfer"(%545) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
      "cf.br"(%560)[^bb7] : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb12(%561: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb6
      %562 = "exec.returned"(%561) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%562) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7212h7265706561745f76616c7565", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_19", sym_visibility = "private"}> ({
    ^bb0(%arg262: !runtime.scope, %arg263: ui64, %arg264: !algebra.field_vector<"bls12-381.fr">, %arg265: !algebra.field<"bls12-381.fr">):
      %531 = "exec.apply"(%arg262, %arg264, %arg265) <{binding = @zkl_binding_1, parameters = [], site = "s4"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%531)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%532: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %533 = "exec.complete"(%arg262, %532) : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%533) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%534: !exec.stop):  // pred: ^bb0
      %535 = "exec.failed"(%534) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%535) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_33e26704899171b0d3e366f86377dfc6602b55f53021ce20930f7ae9e8061294", sym_visibility = "private"}> ({
    ^bb0(%arg258: !runtime.scope, %arg259: !algebra.field_vector<"bls12-381.fr">, %arg260: ui64, %arg261: !algebra.field_vector<"bls12-381.fr">):
      %526 = "exec.fold"(%arg258, %arg261, %arg259, %arg260) <{domain = @finite_zkl_33e26704899171b0d3e366f86377dfc6602b55f53021ce20930f7ae9e8061294_s0_domain, site = "s0", step = @finite_zkl_33e26704899171b0d3e366f86377dfc6602b55f53021ce20930f7ae9e8061294_s0_body}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%526)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%527: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %528 = "exec.returned"(%527) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%528) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%529: !exec.stop):  // pred: ^bb0
      %530 = "exec.failed"(%529) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%530) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_33e26704899171b0d3e366f86377dfc6602b55f53021ce20930f7ae9e8061294_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg257: !algebra.field_vector<"bls12-381.fr">):
      %525 = "data.domain_elements"(%arg257) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%525) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "finite_zkl_33e26704899171b0d3e366f86377dfc6602b55f53021ce20930f7ae9e8061294_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg252: !runtime.scope, %arg253: !algebra.field_vector<"bls12-381.fr">, %arg254: !algebra.field<"bls12-381.fr">, %arg255: !algebra.field_vector<"bls12-381.fr">, %arg256: ui64):
      %520 = "func.call"(%arg252, %arg253, %arg254, %arg256) <{callee = @zkl_e7a7efcd14676d32c0e577ff1097f611a3dc84c74ecaa8bfdbebb25968971255}> {runtime.site = "body"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%520)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%521: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %522 = "exec.returned"(%521) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%522) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%523: !exec.stop):  // pred: ^bb0
      %524 = "exec.failed"(%523) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%524) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["finite_zkl_33e26704899171b0d3e366f86377dfc6602b55f53021ce20930f7ae9e8061294_s0_body", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_33f3047479634e63ecd16a0855f88ad8af019c37d677a4ffe6f5bacc63307947", sym_visibility = "private"}> ({
    ^bb0(%arg249: !runtime.scope, %arg250: !algebra.field_vector<"bls12-381.fr">, %arg251: ui64):
      %491 = "exec.apply"(%arg249) <{binding = @zkl_binding_0, parameters = [], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%491)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%492: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %493 = "exec.apply"(%arg249) <{binding = @zkl_binding_3, parameters = ["0"], site = "s2"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%493)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%494: !exec.stop):  // 5 preds: ^bb0, ^bb1, ^bb3, ^bb7, ^bb9
      %495 = "exec.failed"(%494) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%495) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%496: ui64):  // pred: ^bb1
      %497 = "exec.range"(%arg249, %496, %arg251) <{site = "s4"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%497)[^bb4, ^bb2] : (!exec.outcome<(i64, i64)>) -> ()
    ^bb4(%498: i64, %499: i64):  // pred: ^bb3
      %500 = "runtime.borrow_transfer"(%arg249, %492) : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>
      "cf.br"(%498, %500)[^bb5] : (i64, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb5(%501: i64, %502: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>):  // 2 preds: ^bb4, ^bb8
      %503 = "arith.cmpi"(%501, %499) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%503, %502)[^bb6, ^bb7] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb6:  // pred: ^bb5
      %504 = "runtime.iteration"(%arg249, %501) <{site = "s4"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%504)[^bb10, ^bb9] : (!exec.outcome<(ui64)>) -> ()
    ^bb7(%505: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>):  // pred: ^bb5
      %506 = "runtime.accept_transfer"(%arg249, %505) : (!runtime.scope, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%506)[^bb13, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%507: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>):  // pred: ^bb12
      %508 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %509 = "arith.addi"(%501, %508) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%509, %507)[^bb5] : (i64, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb9(%510: !exec.stop):  // 3 preds: ^bb6, ^bb10, ^bb11
      "runtime.release_transfer"(%502) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
      "cf.br"(%510)[^bb2] : (!exec.stop) -> ()
    ^bb10(%511: ui64):  // pred: ^bb6
      %512 = "runtime.transfer_values"(%502) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> !algebra.field_vector<"bls12-381.fr">
      %513 = "runtime.enter_scope"(%arg249, %501, %511, %512, %arg250) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 3>, site = "s4"}> : (!runtime.scope, i64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%513)[^bb11, ^bb9] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb11(%514: !runtime.scope):  // pred: ^bb10
      %515 = "func.call"(%514, %511, %512, %arg250) <{callee = @zkl_control_20}> : (!runtime.scope, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      %516 = "runtime.exit_scope"(%514, %515) : (!runtime.scope, !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>)>
      "exec.dispatch"(%516)[^bb12, ^bb9] : (!exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>)>) -> ()
    ^bb12(%517: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>):  // pred: ^bb11
      "runtime.release_transfer"(%502) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
      "cf.br"(%517)[^bb8] : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb13(%518: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb7
      %519 = "exec.returned"(%518) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%519) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b724h74696c65", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_20", sym_visibility = "private"}> ({
    ^bb0(%arg245: !runtime.scope, %arg246: ui64, %arg247: !algebra.field_vector<"bls12-381.fr">, %arg248: !algebra.field_vector<"bls12-381.fr">):
      %486 = "func.call"(%arg245, %arg247, %arg248) <{callee = @zkl_5939bc7a1ddcd11f8e2153f23b3ed89c16434b9b99db1512543ee10e7b59b248}> {runtime.site = "s5"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%486)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%487: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %488 = "exec.complete"(%arg245, %487) : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%488) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%489: !exec.stop):  // pred: ^bb0
      %490 = "exec.failed"(%489) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%490) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_ac1d3513b06c1d4950d126f678b9482e4ca13944fc4b35442d1a33796d064b0c", sym_visibility = "private"}> ({
    ^bb0(%arg242: !runtime.scope, %arg243: !algebra.field_vector<"bls12-381.fr">, %arg244: !algebra.field<"bls12-381.fr">):
      %481 = "exec.apply"(%arg242, %arg243, %arg244) <{binding = @zkl_binding_1, parameters = [], site = "s2"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%481)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%482: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %483 = "exec.returned"(%482) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%483) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%484: !exec.stop):  // pred: ^bb0
      %485 = "exec.failed"(%484) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%485) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zks_42e44eec4fd7419218a6cf70cf462d528dfc3e199764475009d12bc09d4ada97", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_5939bc7a1ddcd11f8e2153f23b3ed89c16434b9b99db1512543ee10e7b59b248", sym_visibility = "private"}> ({
    ^bb0(%arg239: !runtime.scope, %arg240: !algebra.field_vector<"bls12-381.fr">, %arg241: !algebra.field_vector<"bls12-381.fr">):
      %476 = "exec.fold"(%arg239, %arg241, %arg240) <{domain = @finite_zkl_5939bc7a1ddcd11f8e2153f23b3ed89c16434b9b99db1512543ee10e7b59b248_s0_domain, site = "s0", step = @finite_zkl_5939bc7a1ddcd11f8e2153f23b3ed89c16434b9b99db1512543ee10e7b59b248_s0_body}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%476)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%477: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %478 = "exec.returned"(%477) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%478) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%479: !exec.stop):  // pred: ^bb0
      %480 = "exec.failed"(%479) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%480) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_5939bc7a1ddcd11f8e2153f23b3ed89c16434b9b99db1512543ee10e7b59b248_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg238: !algebra.field_vector<"bls12-381.fr">):
      %475 = "data.domain_elements"(%arg238) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%475) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "finite_zkl_5939bc7a1ddcd11f8e2153f23b3ed89c16434b9b99db1512543ee10e7b59b248_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg234: !runtime.scope, %arg235: !algebra.field_vector<"bls12-381.fr">, %arg236: !algebra.field<"bls12-381.fr">, %arg237: !algebra.field_vector<"bls12-381.fr">):
      %470 = "func.call"(%arg234, %arg235, %arg236) <{callee = @zkl_ac1d3513b06c1d4950d126f678b9482e4ca13944fc4b35442d1a33796d064b0c}> {runtime.site = "body"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%470)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%471: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %472 = "exec.returned"(%471) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%472) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%473: !exec.stop):  // pred: ^bb0
      %474 = "exec.failed"(%473) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%474) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["finite_zkl_5939bc7a1ddcd11f8e2153f23b3ed89c16434b9b99db1512543ee10e7b59b248_s0_body", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_6b3d366572d1ba53650a202f39ff52a2f298a1591829443fbeaa34ef3974f084", sym_visibility = "private"}> ({
    ^bb0(%arg230: !algebra.field<"bls12-381.fr">, %arg231: !algebra.field<"bls12-381.fr">, %arg232: !algebra.field<"bls12-381.fr">, %arg233: !algebra.field<"bls12-381.fr">):
      %465 = "algebra.field_add"(%arg232, %arg233) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %466 = "algebra.field_multiply"(%arg230, %465) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %467 = "algebra.field_multiply"(%arg231, %arg232) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %468 = "algebra.field_multiply"(%467, %arg233) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %469 = "algebra.field_add"(%466, %468) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%469) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_d1f2756b99b17aad26e4b85a966eec4c9419609618b22e3ee7f8a3349cb1e33b", sym_visibility = "private"}> ({
    ^bb0(%arg224: !runtime.scope, %arg225: !algebra.field_vector<"bls12-381.fr">, %arg226: !algebra.field_vector<"bls12-381.fr">, %arg227: !algebra.field_vector<"bls12-381.fr">, %arg228: !algebra.field_vector<"bls12-381.fr">, %arg229: ui64):
      %446 = "func.call"(%arg224, %arg229) <{callee = @s3h676b7212h706f7765725f6f665f74776f}> {runtime.site = "s0"} : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%446)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%447: ui64):  // pred: ^bb0
      %448 = "exec.apply"(%arg224, %arg227) <{binding = @zkl_binding_2, parameters = [], site = "s2"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%448)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%449: !exec.stop):  // 8 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb8
      %450 = "exec.failed"(%449) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%450) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%451: ui64):  // pred: ^bb1
      %452 = "exec.apply"(%arg224, %451, %arg229) <{binding = @zkl_binding_12, parameters = [], site = "s3"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%452)[^bb4, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%453: ui64):  // pred: ^bb3
      %454 = "exec.apply"(%arg224, %453, %arg229) <{binding = @zkl_binding_12, parameters = [], site = "s4"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%454)[^bb5, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%455: ui64):  // pred: ^bb4
      %456 = "func.call"(%arg224, %arg225, %455, %arg227) <{callee = @zkl_b16c159516733e0a19ce242015622636ee99dc6084d8c851dfb43c25cee57b59}> {runtime.site = "s6"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%456)[^bb6, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb6(%457: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb5
      %458 = "func.call"(%arg224, %arg226, %455, %arg227) <{callee = @zkl_b16c159516733e0a19ce242015622636ee99dc6084d8c851dfb43c25cee57b59}> {runtime.site = "s7"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%458)[^bb7, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb7(%459: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb6
      %460 = "func.call"(%arg224, %arg228, %447) <{callee = @zkl_afd97de07c9ccae9db68186ebf66098aed7daffb4b11c598d0da5cd116df8490}> {runtime.site = "s8"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%460)[^bb8, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%461: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb7
      %462 = "func.call"(%arg224, %arg228, %447) <{callee = @zkl_33f3047479634e63ecd16a0855f88ad8af019c37d677a4ffe6f5bacc63307947}> {runtime.site = "s9"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%462)[^bb9, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb9(%463: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb8
      %464 = "exec.returned"(%457, %459, %461, %463) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%464) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7211h6c617965725f6761746573", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_b16c159516733e0a19ce242015622636ee99dc6084d8c851dfb43c25cee57b59", sym_visibility = "private"}> ({
    ^bb0(%arg220: !runtime.scope, %arg221: !algebra.field_vector<"bls12-381.fr">, %arg222: ui64, %arg223: !algebra.field_vector<"bls12-381.fr">):
      %431 = "exec.apply"(%arg220) <{binding = @zkl_binding_3, parameters = ["1"], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%431)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%432: ui64):  // pred: ^bb0
      %433 = "func.call"(%arg220, %arg221, %arg222, %432) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a}> {runtime.site = "s1"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%433)[^bb3, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb2(%434: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %435 = "exec.failed"(%434) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%435) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%436: !algebra.field_vector<"bls12-381.fr">, %437: ui64, %438: ui64):  // pred: ^bb1
      %439 = "func.call"(%arg220, %436, %437, %438, %arg223) <{callee = @zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be}> {runtime.site = "s2"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%439)[^bb4, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb4(%440: !algebra.field_vector<"bls12-381.fr">, %441: ui64, %442: ui64):  // pred: ^bb3
      %443 = "exec.compute"(%arg220, %440, %441, %442) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33, site = "s3"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%443)[^bb5, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb5(%444: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb4
      %445 = "exec.returned"(%444) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%445) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b728h7265737472696374", []]} : () -> ()
    "protocol.func"() <{contracts = [], function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), input_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000000", "role00000001"], ["role00000001"]], origin = ["gkr::Rounds", [["F", ["field", "bls12-381.fr"]], ["Max", ["nat", "4"]]]], output_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba"}> ({
    ^bb0(%arg204: !algebra.field_vector<"bls12-381.fr">, %arg205: !algebra.field_vector<"bls12-381.fr">, %arg206: !algebra.field_vector<"bls12-381.fr">, %arg207: !algebra.field_vector<"bls12-381.fr">, %arg208: !algebra.field<"bls12-381.fr">, %arg209: ui64, %arg210: !protocol.service_ref<"random.bls12-381.fr/0">):
      %407 = "protocol.local_call"() <{callee = @zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f, role = "role00000000", site = "s1"}> : () -> !algebra.field_vector<"bls12-381.fr">
      %408 = "protocol.local_call"() <{callee = @zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f, role = "role00000001", site = "s3"}> : () -> !algebra.field_vector<"bls12-381.fr">
      %409:7 = "protocol.repeat"(%arg209, %arg204, %arg205, %arg206, %arg207, %407, %408, %arg208, %arg210) <{carried = 7 : i64, carried_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"]], maximum = 4 : i64, roles = ["role00000000", "role00000001"], site = "s6"}> ({
      ^bb0(%arg211: ui64, %arg212: !algebra.field_vector<"bls12-381.fr">, %arg213: !algebra.field_vector<"bls12-381.fr">, %arg214: !algebra.field_vector<"bls12-381.fr">, %arg215: !algebra.field_vector<"bls12-381.fr">, %arg216: !algebra.field_vector<"bls12-381.fr">, %arg217: !algebra.field_vector<"bls12-381.fr">, %arg218: !algebra.field<"bls12-381.fr">, %arg219: !protocol.service_ref<"random.bls12-381.fr/0">):
        %410:3 = "protocol.local_call"(%arg212, %arg213, %arg214, %arg215) <{callee = @zkl_e2f65d17b480da5da0270346faa1bd036c7a5f879e30f4b2b6bac1224b05e394, role = "role00000000", site = "s7"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %411 = "protocol.exchange"(%410#0) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %412 = "protocol.restrict_roles"(%411) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %413 = "protocol.exchange"(%410#1) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_1"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %414 = "protocol.restrict_roles"(%413) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %415 = "protocol.exchange"(%410#2) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_2"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %416 = "protocol.restrict_roles"(%415) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %417 = "algebra.field_add"(%412, %412) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %418 = "algebra.field_add"(%417, %414) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %419 = "algebra.field_add"(%418, %416) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %420 = "algebra.field_equal"(%arg218, %419) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
        "protocol.guard"(%420) <{owner = "role00000001", site = "s18"}> : (i1) -> ()
        %421 = "protocol.query"(%arg219) <{method = "draw", owner = "role00000001", site = "label_6368616c6c656e6765"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
        %422 = "protocol.exchange"(%421) <{receiver = "role00000000", sender = "role00000001", site = "label_64656c6976657279_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %423 = "protocol.restrict_roles"(%422) <{roles = ["role00000000"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %424:4 = "protocol.local_call"(%arg212, %arg213, %arg214, %arg215, %423) <{callee = @zkl_36caebca415236dd6aac1763c9a581b89c25a00e62432b484ec92ae08e6a0099, role = "role00000000", site = "s23"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)
        %425 = "protocol.local_call"(%arg216, %423) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000000", site = "s25"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
        %426 = "protocol.local_call"(%arg217, %421) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000001", site = "s27"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
        %427 = "algebra.field_multiply"(%421, %416) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %428 = "algebra.field_add"(%414, %427) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %429 = "algebra.field_multiply"(%421, %428) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %430 = "algebra.field_add"(%412, %429) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        "protocol.yield"(%424#0, %424#1, %424#2, %424#3, %425, %426, %430) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
      }) : (ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      "protocol.return"(%409#4, %409#0, %409#1, %409#2, %409#3, %409#5, %409#6) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_e2f65d17b480da5da0270346faa1bd036c7a5f879e30f4b2b6bac1224b05e394", sym_visibility = "private"}> ({
    ^bb0(%arg199: !runtime.scope, %arg200: !algebra.field_vector<"bls12-381.fr">, %arg201: !algebra.field_vector<"bls12-381.fr">, %arg202: !algebra.field_vector<"bls12-381.fr">, %arg203: !algebra.field_vector<"bls12-381.fr">):
      %378 = "exec.apply"(%arg199, %arg200) <{binding = @zkl_binding_11, parameters = [], site = "s1"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%378)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%379: !algebra.field_vector<"bls12-381.fr">, %380: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %381 = "exec.apply"(%arg199, %arg201) <{binding = @zkl_binding_11, parameters = [], site = "s4"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%381)[^bb3, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%382: !exec.stop):  // 11 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb10, ^bb11
      %383 = "exec.failed"(%382) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%383) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb3(%384: !algebra.field_vector<"bls12-381.fr">, %385: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb1
      %386 = "exec.apply"(%arg199, %arg202) <{binding = @zkl_binding_11, parameters = [], site = "s7"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%386)[^bb4, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb4(%387: !algebra.field_vector<"bls12-381.fr">, %388: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb3
      %389 = "exec.apply"(%arg199, %arg203) <{binding = @zkl_binding_11, parameters = [], site = "s10"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%389)[^bb5, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb5(%390: !algebra.field_vector<"bls12-381.fr">, %391: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb4
      %392 = "exec.collect"(%arg199, %379, %384, %387, %390) <{body = @zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_body, domain = @zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_domain, site = "s16"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%392)[^bb6, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb6(%393: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb5
      %394 = "exec.apply"(%arg199, %393) <{binding = @zkl_binding_4, parameters = [], site = "s17"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%394)[^bb7, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb7(%395: !algebra.field<"bls12-381.fr">):  // pred: ^bb6
      %396 = "exec.collect"(%arg199, %380, %385, %388, %391) <{body = @zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_body, domain = @zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_domain, site = "s23"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%396)[^bb8, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%397: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb7
      %398 = "exec.apply"(%arg199, %397) <{binding = @zkl_binding_4, parameters = [], site = "s24"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%398)[^bb9, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb9(%399: !algebra.field<"bls12-381.fr">):  // pred: ^bb8
      %400 = "exec.collect"(%arg199, %379, %380, %384, %385, %387, %388, %390, %391) <{body = @zkl_map_b02c6bec831af4d953cc5d5558b1dfebb2f6666e509fde68f0a09745680b6577_body, domain = @zkl_map_b02c6bec831af4d953cc5d5558b1dfebb2f6666e509fde68f0a09745680b6577_domain, site = "s34"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%400)[^bb10, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb10(%401: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb9
      %402 = "exec.apply"(%arg199, %401) <{binding = @zkl_binding_4, parameters = [], site = "s35"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%402)[^bb11, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb11(%403: !algebra.field<"bls12-381.fr">):  // pred: ^bb10
      %404 = "exec.compute"(%arg199, %395, %399, %403) <{callee = @zkl_ae0ec2b882ea51d896368927e811be493e3af32def2e5ada1525e385646e6229, site = "s37"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%404)[^bb12, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb12(%405: !algebra.field<"bls12-381.fr">):  // pred: ^bb11
      %406 = "exec.returned"(%395, %405, %403) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%406) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7213h726f756e645f6d657373616765", []]} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, sym_name = "zkl_map_b02c6bec831af4d953cc5d5558b1dfebb2f6666e509fde68f0a09745680b6577_domain", sym_visibility = "private"}> ({
    ^bb0(%arg191: !algebra.field_vector<"bls12-381.fr">, %arg192: !algebra.field_vector<"bls12-381.fr">, %arg193: !algebra.field_vector<"bls12-381.fr">, %arg194: !algebra.field_vector<"bls12-381.fr">, %arg195: !algebra.field_vector<"bls12-381.fr">, %arg196: !algebra.field_vector<"bls12-381.fr">, %arg197: !algebra.field_vector<"bls12-381.fr">, %arg198: !algebra.field_vector<"bls12-381.fr">):
      %363 = "data.domain_elements"(%arg191) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %364 = "data.domain_elements"(%arg192) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %365 = "data.domain_zip"(%363, %364) : (!data.domain<!algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      %366 = "data.domain_elements"(%arg193) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %367 = "data.domain_zip"(%365, %366) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      %368 = "data.domain_elements"(%arg194) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %369 = "data.domain_zip"(%367, %368) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      %370 = "data.domain_elements"(%arg195) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %371 = "data.domain_zip"(%369, %370) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      %372 = "data.domain_elements"(%arg196) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %373 = "data.domain_zip"(%371, %372) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      %374 = "data.domain_elements"(%arg197) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %375 = "data.domain_zip"(%373, %374) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      %376 = "data.domain_elements"(%arg198) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %377 = "data.domain_zip"(%375, %376) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%377) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_map_b02c6bec831af4d953cc5d5558b1dfebb2f6666e509fde68f0a09745680b6577_body", sym_visibility = "private"}> ({
    ^bb0(%arg174: !runtime.scope, %arg175: !algebra.field<"bls12-381.fr">, %arg176: !algebra.field<"bls12-381.fr">, %arg177: !algebra.field<"bls12-381.fr">, %arg178: !algebra.field<"bls12-381.fr">, %arg179: !algebra.field<"bls12-381.fr">, %arg180: !algebra.field<"bls12-381.fr">, %arg181: !algebra.field<"bls12-381.fr">, %arg182: !algebra.field<"bls12-381.fr">, %arg183: !algebra.field_vector<"bls12-381.fr">, %arg184: !algebra.field_vector<"bls12-381.fr">, %arg185: !algebra.field_vector<"bls12-381.fr">, %arg186: !algebra.field_vector<"bls12-381.fr">, %arg187: !algebra.field_vector<"bls12-381.fr">, %arg188: !algebra.field_vector<"bls12-381.fr">, %arg189: !algebra.field_vector<"bls12-381.fr">, %arg190: !algebra.field_vector<"bls12-381.fr">):
      %358 = "exec.compute"(%arg174, %arg175, %arg176, %arg177, %arg178, %arg179, %arg180, %arg181, %arg182) <{callee = @zkl_f5e0b2f9a4003d8d806a7a288580cf1f30d07d383f870564beff948ccf011d6b, site = "body"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%358)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%359: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %360 = "exec.returned"(%359) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%360) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%361: !exec.stop):  // pred: ^bb0
      %362 = "exec.failed"(%361) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%362) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zkl_map_b02c6bec831af4d953cc5d5558b1dfebb2f6666e509fde68f0a09745680b6577_body", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_f5e0b2f9a4003d8d806a7a288580cf1f30d07d383f870564beff948ccf011d6b", sym_visibility = "private"}> ({
    ^bb0(%arg166: !algebra.field<"bls12-381.fr">, %arg167: !algebra.field<"bls12-381.fr">, %arg168: !algebra.field<"bls12-381.fr">, %arg169: !algebra.field<"bls12-381.fr">, %arg170: !algebra.field<"bls12-381.fr">, %arg171: !algebra.field<"bls12-381.fr">, %arg172: !algebra.field<"bls12-381.fr">, %arg173: !algebra.field<"bls12-381.fr">):
      %344 = "algebra.field_subtract"(%arg167, %arg166) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %345 = "algebra.field_subtract"(%arg169, %arg168) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %346 = "algebra.field_subtract"(%arg171, %arg170) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %347 = "algebra.field_subtract"(%arg173, %arg172) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %348 = "algebra.field_add"(%346, %347) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %349 = "algebra.field_multiply"(%344, %348) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %350 = "algebra.field_multiply"(%346, %arg172) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %351 = "algebra.field_multiply"(%arg170, %347) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %352 = "algebra.field_add"(%350, %351) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %353 = "algebra.field_multiply"(%345, %352) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %354 = "algebra.field_add"(%349, %353) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %355 = "algebra.field_multiply"(%arg168, %346) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %356 = "algebra.field_multiply"(%355, %347) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %357 = "algebra.field_add"(%354, %356) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%357) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_ae0ec2b882ea51d896368927e811be493e3af32def2e5ada1525e385646e6229", sym_visibility = "private"}> ({
    ^bb0(%arg163: !algebra.field<"bls12-381.fr">, %arg164: !algebra.field<"bls12-381.fr">, %arg165: !algebra.field<"bls12-381.fr">):
      %342 = "algebra.field_subtract"(%arg164, %arg163) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %343 = "algebra.field_subtract"(%342, %arg165) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%343) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_36caebca415236dd6aac1763c9a581b89c25a00e62432b484ec92ae08e6a0099", sym_visibility = "private"}> ({
    ^bb0(%arg157: !runtime.scope, %arg158: !algebra.field_vector<"bls12-381.fr">, %arg159: !algebra.field_vector<"bls12-381.fr">, %arg160: !algebra.field_vector<"bls12-381.fr">, %arg161: !algebra.field_vector<"bls12-381.fr">, %arg162: !algebra.field<"bls12-381.fr">):
      %331 = "func.call"(%arg157, %arg158, %arg162) <{callee = @zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac}> {runtime.site = "s1"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%331)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%332: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %333 = "func.call"(%arg157, %arg159, %arg162) <{callee = @zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac}> {runtime.site = "s3"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%333)[^bb3, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%334: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %335 = "exec.failed"(%334) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%335) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%336: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb1
      %337 = "func.call"(%arg157, %arg160, %arg162) <{callee = @zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac}> {runtime.site = "s5"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%337)[^bb4, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb4(%338: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb3
      %339 = "func.call"(%arg157, %arg161, %arg162) <{callee = @zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac}> {runtime.site = "s7"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%339)[^bb5, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb5(%340: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb4
      %341 = "exec.returned"(%332, %336, %338, %340) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%341) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b729h6669785f6761746573", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac", sym_visibility = "private"}> ({
    ^bb0(%arg154: !runtime.scope, %arg155: !algebra.field_vector<"bls12-381.fr">, %arg156: !algebra.field<"bls12-381.fr">):
      %323 = "exec.apply"(%arg154, %arg155) <{binding = @zkl_binding_11, parameters = [], site = "s0"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%323)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%324: !algebra.field_vector<"bls12-381.fr">, %325: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %326 = "exec.collect"(%arg154, %324, %325, %arg156) <{body = @zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_body, domain = @zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_domain, site = "s4"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%326)[^bb3, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%327: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %328 = "exec.failed"(%327) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%328) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%329: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb1
      %330 = "exec.returned"(%329) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%330) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b723h666978", []]} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, sym_name = "zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_domain", sym_visibility = "private"}> ({
    ^bb0(%arg152: !algebra.field_vector<"bls12-381.fr">, %arg153: !algebra.field_vector<"bls12-381.fr">):
      %320 = "data.domain_elements"(%arg152) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %321 = "data.domain_elements"(%arg153) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %322 = "data.domain_zip"(%320, %321) : (!data.domain<!algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%322) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_body", sym_visibility = "private"}> ({
    ^bb0(%arg146: !runtime.scope, %arg147: !algebra.field<"bls12-381.fr">, %arg148: !algebra.field<"bls12-381.fr">, %arg149: !algebra.field_vector<"bls12-381.fr">, %arg150: !algebra.field_vector<"bls12-381.fr">, %arg151: !algebra.field<"bls12-381.fr">):
      %315 = "exec.compute"(%arg146, %arg147, %arg148, %arg151) <{callee = @zkl_9de40b3e39acd7da53c8d9f1ec759779b60f4d0d3b7314f8741f798f050dbfd1, site = "body"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%315)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%316: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %317 = "exec.returned"(%316) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%317) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%318: !exec.stop):  // pred: ^bb0
      %319 = "exec.failed"(%318) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%319) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_body", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_9de40b3e39acd7da53c8d9f1ec759779b60f4d0d3b7314f8741f798f050dbfd1", sym_visibility = "private"}> ({
    ^bb0(%arg143: !algebra.field<"bls12-381.fr">, %arg144: !algebra.field<"bls12-381.fr">, %arg145: !algebra.field<"bls12-381.fr">):
      %312 = "algebra.field_subtract"(%arg144, %arg143) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %313 = "algebra.field_multiply"(%312, %arg145) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %314 = "algebra.field_add"(%arg143, %313) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%314) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_91fe8ea73b5db3432f90fc8fe9725c8455fce8782b4cc4d2839d05826de71b8f", sym_visibility = "private"}> ({
    ^bb0(%arg138: !runtime.scope, %arg139: !algebra.field_vector<"bls12-381.fr">, %arg140: !algebra.field_vector<"bls12-381.fr">, %arg141: !algebra.field_vector<"bls12-381.fr">, %arg142: ui64):
      %274 = "exec.apply"(%arg138) <{binding = @zkl_binding_3, parameters = ["1"], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%274)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%275: ui64):  // pred: ^bb0
      %276 = "exec.apply"(%arg138, %arg142, %275) <{binding = @zkl_binding_12, parameters = [], site = "s1"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%276)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%277: !exec.stop):  // 9 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb11, ^bb13
      %278 = "exec.failed"(%277) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%278) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%279: ui64):  // pred: ^bb1
      %280 = "exec.apply"(%arg138) <{binding = @zkl_binding_0, parameters = [], site = "s3"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%280)[^bb4, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb4(%281: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb3
      %282 = "func.call"(%arg138, %281, %arg142, %arg139) <{callee = @zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35}> {runtime.site = "s5"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%282)[^bb5, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb5(%283: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb4
      %284 = "exec.apply"(%arg138) <{binding = @zkl_binding_3, parameters = ["0"], site = "s7"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%284)[^bb6, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb6(%285: ui64):  // pred: ^bb5
      %286 = "exec.apply"(%arg138) <{binding = @zkl_binding_3, parameters = ["0"], site = "s9"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%286)[^bb7, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb7(%287: ui64):  // pred: ^bb6
      %288 = "exec.range"(%arg138, %287, %arg142) <{site = "s13"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%288)[^bb8, ^bb2] : (!exec.outcome<(i64, i64)>) -> ()
    ^bb8(%289: i64, %290: i64):  // pred: ^bb7
      %291 = "runtime.borrow_transfer"(%arg138, %283, %285) : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>
      "cf.br"(%289, %291)[^bb9] : (i64, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb9(%292: i64, %293: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>):  // 2 preds: ^bb8, ^bb12
      %294 = "arith.cmpi"(%292, %290) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%294, %293)[^bb10, ^bb11] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb10:  // pred: ^bb9
      %295 = "runtime.iteration"(%arg138, %292) <{site = "s13"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%295)[^bb14, ^bb13] : (!exec.outcome<(ui64)>) -> ()
    ^bb11(%296: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>):  // pred: ^bb9
      %297 = "runtime.accept_transfer"(%arg138, %296) : (!runtime.scope, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>
      "exec.dispatch"(%297)[^bb17, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb12(%298: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>):  // pred: ^bb16
      %299 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %300 = "arith.addi"(%292, %299) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%300, %298)[^bb9] : (i64, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb13(%301: !exec.stop):  // 3 preds: ^bb10, ^bb14, ^bb15
      "runtime.release_transfer"(%293) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
      "cf.br"(%301)[^bb2] : (!exec.stop) -> ()
    ^bb14(%302: ui64):  // pred: ^bb10
      %303:2 = "runtime.transfer_values"(%293) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> (!algebra.field_vector<"bls12-381.fr">, ui64)
      %304 = "runtime.enter_scope"(%arg138, %292, %302, %303#0, %303#1, %arg140, %arg141, %279) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 6>, site = "s13"}> : (!runtime.scope, i64, ui64, !algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%304)[^bb15, ^bb13] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb15(%305: !runtime.scope):  // pred: ^bb14
      %306 = "func.call"(%305, %302, %303#0, %303#1, %arg140, %arg141, %279) <{callee = @zkl_control_21}> : (!runtime.scope, ui64, !algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>
      %307 = "runtime.exit_scope"(%305, %306) : (!runtime.scope, !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> !exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>)>
      "exec.dispatch"(%307)[^bb16, ^bb13] : (!exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>)>) -> ()
    ^bb16(%308: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>):  // pred: ^bb15
      "runtime.release_transfer"(%293) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
      "cf.br"(%308)[^bb12] : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb17(%309: !algebra.field_vector<"bls12-381.fr">, %310: ui64):  // pred: ^bb11
      %311 = "exec.returned"(%309) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%311) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7217h6c696e655f636f656666696369656e7473", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, !algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>, no_inline, sym_name = "zkl_control_21", sym_visibility = "private"}> ({
    ^bb0(%arg131: !runtime.scope, %arg132: ui64, %arg133: !algebra.field_vector<"bls12-381.fr">, %arg134: ui64, %arg135: !algebra.field_vector<"bls12-381.fr">, %arg136: !algebra.field_vector<"bls12-381.fr">, %arg137: ui64):
      %250 = "func.call"(%arg131, %arg135, %arg134) <{callee = @zkl_6ba53ec68a0230031d706e4a93e78f80425c51108d34ecc0a5aa5681eded9c8e}> {runtime.site = "s14"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%250)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%251: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %252 = "func.call"(%arg131, %arg136, %arg134) <{callee = @zkl_6ba53ec68a0230031d706e4a93e78f80425c51108d34ecc0a5aa5681eded9c8e}> {runtime.site = "s16"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%252)[^bb3, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%253: !exec.stop):  // 10 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb10
      %254 = "exec.failed"(%253) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>
      "func.return"(%254) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb3(%255: !algebra.field<"bls12-381.fr">):  // pred: ^bb1
      %256 = "exec.apply"(%arg131, %arg133) <{binding = @zkl_binding_11, parameters = [], site = "s18"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%256)[^bb4, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb4(%257: !algebra.field_vector<"bls12-381.fr">, %258: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb3
      %259 = "exec.collect"(%arg131, %257, %258, %251) <{body = @zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_body, domain = @zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_domain, site = "s22"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%259)[^bb5, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb5(%260: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb4
      %261 = "exec.compute"(%arg131, %255, %251) <{callee = @zkl_c15efd5f24b71cb9e6e3766d00c208e0a0014177a6ae1e9dd67b23bda4eff8ab, site = "s26"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%261)[^bb6, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb6(%262: !algebra.field<"bls12-381.fr">):  // pred: ^bb5
      %263 = "exec.collect"(%arg131, %257, %258, %262) <{body = @zkl_map_f8f9614d3bd7d4196ffb7d73d3d80b5571e091e9fdbaeb4adc8aa23e703bd4a5_body, domain = @zkl_map_f8f9614d3bd7d4196ffb7d73d3d80b5571e091e9fdbaeb4adc8aa23e703bd4a5_domain, site = "s27"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%263)[^bb7, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb7(%264: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb6
      %265 = "func.call"(%arg131, %264, %arg137) <{callee = @zkl_3d3958243128671a7ae06c730aba5c78b4cae61932510ab43ba5bcabe7324295}> {runtime.site = "s29"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%265)[^bb8, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%266: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb7
      %267 = "exec.collect"(%arg131, %260, %266) <{body = @zkl_map_b7eb5d68e6edd9e938f02a44220440e7b9e5f3fe195e305a87f963f93affd321_body, domain = @zkl_map_b7eb5d68e6edd9e938f02a44220440e7b9e5f3fe195e305a87f963f93affd321_domain, site = "s30"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%267)[^bb9, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb9(%268: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb8
      %269 = "exec.apply"(%arg131) <{binding = @zkl_binding_3, parameters = ["1"], site = "s32"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%269)[^bb10, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb10(%270: ui64):  // pred: ^bb9
      %271 = "exec.apply"(%arg131, %arg134, %270) <{binding = @zkl_binding_12, parameters = [], site = "s33"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%271)[^bb11, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb11(%272: ui64):  // pred: ^bb10
      %273 = "exec.complete"(%arg131, %268, %272) : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>
      "func.return"(%273) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    }) {runtime.region} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, sym_name = "zkl_map_f8f9614d3bd7d4196ffb7d73d3d80b5571e091e9fdbaeb4adc8aa23e703bd4a5_domain", sym_visibility = "private"}> ({
    ^bb0(%arg129: !algebra.field_vector<"bls12-381.fr">, %arg130: !algebra.field_vector<"bls12-381.fr">):
      %247 = "data.domain_elements"(%arg129) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %248 = "data.domain_elements"(%arg130) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %249 = "data.domain_zip"(%247, %248) : (!data.domain<!algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%249) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_map_f8f9614d3bd7d4196ffb7d73d3d80b5571e091e9fdbaeb4adc8aa23e703bd4a5_body", sym_visibility = "private"}> ({
    ^bb0(%arg123: !runtime.scope, %arg124: !algebra.field<"bls12-381.fr">, %arg125: !algebra.field<"bls12-381.fr">, %arg126: !algebra.field_vector<"bls12-381.fr">, %arg127: !algebra.field_vector<"bls12-381.fr">, %arg128: !algebra.field<"bls12-381.fr">):
      %242 = "exec.compute"(%arg123, %arg124, %arg125, %arg128) <{callee = @zkl_c8eacd293248ba42cad22bd955e2dec7c6105efe1dabf391c3a74b436be7412e, site = "body"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%242)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%243: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %244 = "exec.returned"(%243) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%244) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%245: !exec.stop):  // pred: ^bb0
      %246 = "exec.failed"(%245) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%246) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zkl_map_f8f9614d3bd7d4196ffb7d73d3d80b5571e091e9fdbaeb4adc8aa23e703bd4a5_body", []]} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, sym_name = "zkl_map_b7eb5d68e6edd9e938f02a44220440e7b9e5f3fe195e305a87f963f93affd321_domain", sym_visibility = "private"}> ({
    ^bb0(%arg121: !algebra.field_vector<"bls12-381.fr">, %arg122: !algebra.field_vector<"bls12-381.fr">):
      %239 = "data.domain_elements"(%arg121) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %240 = "data.domain_elements"(%arg122) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %241 = "data.domain_zip"(%239, %240) : (!data.domain<!algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%241) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_map_b7eb5d68e6edd9e938f02a44220440e7b9e5f3fe195e305a87f963f93affd321_body", sym_visibility = "private"}> ({
    ^bb0(%arg116: !runtime.scope, %arg117: !algebra.field<"bls12-381.fr">, %arg118: !algebra.field<"bls12-381.fr">, %arg119: !algebra.field_vector<"bls12-381.fr">, %arg120: !algebra.field_vector<"bls12-381.fr">):
      %234 = "exec.compute"(%arg116, %arg117, %arg118) <{callee = @zkl_02aa9bd9900f843069baf97f23f4f5ccab54b136c8fed5b90842e4c46b7e5fcd, site = "body"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%234)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%235: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %236 = "exec.returned"(%235) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%236) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%237: !exec.stop):  // pred: ^bb0
      %238 = "exec.failed"(%237) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%238) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zkl_map_b7eb5d68e6edd9e938f02a44220440e7b9e5f3fe195e305a87f963f93affd321_body", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_f9bc3972b3acce79409bfe72125c3b04de4dbb81a13d1dfbc918146c1354315c", sym_visibility = "private"}> ({
    ^bb0(%arg112: !runtime.scope, %arg113: !algebra.field_vector<"bls12-381.fr">, %arg114: !algebra.field<"bls12-381.fr">, %arg115: ui64):
      %229 = "func.call"(%arg112, %arg113, %arg114, %arg115) <{callee = @zkl_8184464d79b9512ca72dac4d64d1ba3d187fd1efb0b8118690b5a104ab35f351}> {runtime.site = "s2"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%229)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%230: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %231 = "exec.returned"(%230) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%231) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%232: !exec.stop):  // pred: ^bb0
      %233 = "exec.failed"(%232) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%233) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zks_dab24f1af4cf6ec12b12d53d6ef952d45bf4866eaa489b84bfcce536b42b3f2a", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_8184464d79b9512ca72dac4d64d1ba3d187fd1efb0b8118690b5a104ab35f351", sym_visibility = "private"}> ({
    ^bb0(%arg108: !runtime.scope, %arg109: !algebra.field_vector<"bls12-381.fr">, %arg110: !algebra.field<"bls12-381.fr">, %arg111: ui64):
      %220 = "exec.apply"(%arg108, %arg109, %arg110) <{binding = @zkl_binding_1, parameters = [], site = "s0"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%220)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%221: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %222 = "exec.compute"(%arg108) <{callee = @zkl_e38306e1154810613f8b855b4e24394048cbbd4c4b2723722235b0e03496f137, site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%222)[^bb3, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%223: !exec.stop):  // 3 preds: ^bb0, ^bb1, ^bb3
      %224 = "exec.failed"(%223) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%224) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%225: !algebra.field<"bls12-381.fr">):  // pred: ^bb1
      %226 = "func.call"(%arg108, %221, %225, %arg111) <{callee = @zkl_fbd2531b804047766f8107241edd0ea81368b70795e44e4d8e07484d142783bb}> {runtime.site = "s2"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%226)[^bb4, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb4(%227: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb3
      %228 = "exec.returned"(%227) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%228) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7212h636f6e7374616e745f726f77", []]} : () -> ()
    "func.func"() <{function_type = () -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_e38306e1154810613f8b855b4e24394048cbbd4c4b2723722235b0e03496f137", sym_visibility = "private"}> ({
      %219 = "algebra.constant"() <{value = "0"}> : () -> !algebra.field<"bls12-381.fr">
      "func.return"(%219) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35", sym_visibility = "private"}> ({
    ^bb0(%arg104: !runtime.scope, %arg105: !algebra.field_vector<"bls12-381.fr">, %arg106: ui64, %arg107: !algebra.field_vector<"bls12-381.fr">):
      %214 = "exec.fold"(%arg104, %arg107, %arg105, %arg106) <{domain = @finite_zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35_s0_domain, site = "s0", step = @finite_zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35_s0_body}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%214)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%215: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %216 = "exec.returned"(%215) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%216) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%217: !exec.stop):  // pred: ^bb0
      %218 = "exec.failed"(%217) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%218) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg103: !algebra.field_vector<"bls12-381.fr">):
      %213 = "data.domain_elements"(%arg103) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%213) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "finite_zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg98: !runtime.scope, %arg99: !algebra.field_vector<"bls12-381.fr">, %arg100: !algebra.field<"bls12-381.fr">, %arg101: !algebra.field_vector<"bls12-381.fr">, %arg102: ui64):
      %208 = "func.call"(%arg98, %arg99, %arg100, %arg102) <{callee = @zkl_f9bc3972b3acce79409bfe72125c3b04de4dbb81a13d1dfbc918146c1354315c}> {runtime.site = "body"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%208)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%209: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %210 = "exec.returned"(%209) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%210) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%211: !exec.stop):  // pred: ^bb0
      %212 = "exec.failed"(%211) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%212) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["finite_zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35_s0_body", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_6ba53ec68a0230031d706e4a93e78f80425c51108d34ecc0a5aa5681eded9c8e", sym_visibility = "private"}> ({
    ^bb0(%arg95: !runtime.scope, %arg96: !algebra.field_vector<"bls12-381.fr">, %arg97: ui64):
      %198 = "exec.compute"(%arg95) <{callee = @zkl_e38306e1154810613f8b855b4e24394048cbbd4c4b2723722235b0e03496f137, site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%198)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%199: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %200 = "exec.apply"(%arg95) <{binding = @zkl_binding_3, parameters = ["0"], site = "s1"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%200)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%201: !exec.stop):  // 3 preds: ^bb0, ^bb1, ^bb3
      %202 = "exec.failed"(%201) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%202) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb3(%203: ui64):  // pred: ^bb1
      %204 = "func.call"(%arg95, %199, %203, %arg97, %arg96) <{callee = @zkl_4d05c370830a894df2470c3859782e53b3322378b124acf8f383759935b54a45}> {runtime.site = "s5"} : (!runtime.scope, !algebra.field<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
      "exec.dispatch"(%204)[^bb4, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb4(%205: !algebra.field<"bls12-381.fr">, %206: ui64):  // pred: ^bb3
      %207 = "exec.returned"(%205) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%207) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b727h656c656d656e74", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, ui64, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>, no_inline, sym_name = "zkl_09043a1369ab6c082f8534fc9d21f34f77067e68b9a4c2a907a132342ff59811", sym_visibility = "private"}> ({
    ^bb0(%arg90: !runtime.scope, %arg91: !algebra.field<"bls12-381.fr">, %arg92: ui64, %arg93: !algebra.field<"bls12-381.fr">, %arg94: ui64):
      %172 = "exec.apply"(%arg90, %arg92, %arg94) <{binding = @zkl_binding_6, parameters = [], site = "s3"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%172)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%173: i1):  // pred: ^bb0
      %174 = "exec.test"(%arg90, %173) <{site = "s6"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%174)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%175: !exec.stop):  // 10 preds: ^bb0, ^bb1, ^bb4, ^bb5, ^bb6, ^bb7, ^bb8, ^bb10, ^bb11, ^bb13
      %176 = "exec.failed"(%175) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%176) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb3(%177: i1):  // pred: ^bb1
      "cf.cond_br"(%177)[^bb4, ^bb5] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb4:  // pred: ^bb3
      %178 = "runtime.enter_scope"(%arg90, %arg91, %arg93) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "then", site = "s6"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%178)[^bb7, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb5:  // pred: ^bb3
      %179 = "runtime.enter_scope"(%arg90, %arg91, %arg93) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "else", site = "s6"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%179)[^bb10, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6(%180: !algebra.field<"bls12-381.fr">):  // 2 preds: ^bb9, ^bb12
      %181 = "exec.apply"(%arg90) <{binding = @zkl_binding_3, parameters = ["1"], site = "s11"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%181)[^bb13, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb7(%182: !runtime.scope):  // pred: ^bb4
      %183 = "func.call"(%182, %arg91, %arg93) <{callee = @zkl_control_22}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      %184 = "runtime.exit_scope"(%182, %183) : (!runtime.scope, !exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!algebra.field<"bls12-381.fr">)>)>
      "exec.dispatch"(%184)[^bb8, ^bb2] : (!exec.outcome<(!runtime.transfer<(!algebra.field<"bls12-381.fr">)>)>) -> ()
    ^bb8(%185: !runtime.transfer<(!algebra.field<"bls12-381.fr">)>):  // pred: ^bb7
      %186 = "runtime.accept_transfer"(%arg90, %185) : (!runtime.scope, !runtime.transfer<(!algebra.field<"bls12-381.fr">)>) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%186)[^bb9, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb9(%187: !algebra.field<"bls12-381.fr">):  // pred: ^bb8
      "cf.br"(%187)[^bb6] : (!algebra.field<"bls12-381.fr">) -> ()
    ^bb10(%188: !runtime.scope):  // pred: ^bb5
      %189 = "func.call"(%188, %arg91, %arg93) <{callee = @zkl_control_23}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      %190 = "runtime.exit_scope"(%188, %189) : (!runtime.scope, !exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!algebra.field<"bls12-381.fr">)>)>
      "exec.dispatch"(%190)[^bb11, ^bb2] : (!exec.outcome<(!runtime.transfer<(!algebra.field<"bls12-381.fr">)>)>) -> ()
    ^bb11(%191: !runtime.transfer<(!algebra.field<"bls12-381.fr">)>):  // pred: ^bb10
      %192 = "runtime.accept_transfer"(%arg90, %191) : (!runtime.scope, !runtime.transfer<(!algebra.field<"bls12-381.fr">)>) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%192)[^bb12, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb12(%193: !algebra.field<"bls12-381.fr">):  // pred: ^bb11
      "cf.br"(%193)[^bb6] : (!algebra.field<"bls12-381.fr">) -> ()
    ^bb13(%194: ui64):  // pred: ^bb6
      %195 = "exec.apply"(%arg90, %arg92, %194) <{binding = @zkl_binding_12, parameters = [], site = "s12"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%195)[^bb14, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb14(%196: ui64):  // pred: ^bb13
      %197 = "exec.returned"(%180, %196) : (!algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%197) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>) -> ()
    }) {runtime.origin = ["zks_09bf7b2d0f9a7fa09310de095093a32f6884e18e73addb2f7bae58f6b7c6de5b", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_22", sym_visibility = "private"}> ({
    ^bb0(%arg87: !runtime.scope, %arg88: !algebra.field<"bls12-381.fr">, %arg89: !algebra.field<"bls12-381.fr">):
      %171 = "exec.complete"(%arg87, %arg89) : (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%171) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_23", sym_visibility = "private"}> ({
    ^bb0(%arg84: !runtime.scope, %arg85: !algebra.field<"bls12-381.fr">, %arg86: !algebra.field<"bls12-381.fr">):
      %170 = "exec.complete"(%arg84, %arg85) : (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%170) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>, no_inline, sym_name = "zkl_4d05c370830a894df2470c3859782e53b3322378b124acf8f383759935b54a45", sym_visibility = "private"}> ({
    ^bb0(%arg79: !runtime.scope, %arg80: !algebra.field<"bls12-381.fr">, %arg81: ui64, %arg82: ui64, %arg83: !algebra.field_vector<"bls12-381.fr">):
      %164 = "exec.fold"(%arg79, %arg83, %arg80, %arg81, %arg82) <{domain = @finite_zkl_4d05c370830a894df2470c3859782e53b3322378b124acf8f383759935b54a45_s0_domain, site = "s0", step = @finite_zkl_4d05c370830a894df2470c3859782e53b3322378b124acf8f383759935b54a45_s0_body}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
      "exec.dispatch"(%164)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb1(%165: !algebra.field<"bls12-381.fr">, %166: ui64):  // pred: ^bb0
      %167 = "exec.returned"(%165, %166) : (!algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%167) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb2(%168: !exec.stop):  // pred: ^bb0
      %169 = "exec.failed"(%168) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%169) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_4d05c370830a894df2470c3859782e53b3322378b124acf8f383759935b54a45_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg78: !algebra.field_vector<"bls12-381.fr">):
      %163 = "data.domain_elements"(%arg78) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%163) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, ui64, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>, no_inline, sym_name = "finite_zkl_4d05c370830a894df2470c3859782e53b3322378b124acf8f383759935b54a45_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg72: !runtime.scope, %arg73: !algebra.field<"bls12-381.fr">, %arg74: ui64, %arg75: !algebra.field<"bls12-381.fr">, %arg76: !algebra.field_vector<"bls12-381.fr">, %arg77: ui64):
      %157 = "func.call"(%arg72, %arg73, %arg74, %arg75, %arg77) <{callee = @zkl_09043a1369ab6c082f8534fc9d21f34f77067e68b9a4c2a907a132342ff59811}> {runtime.site = "body"} : (!runtime.scope, !algebra.field<"bls12-381.fr">, ui64, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
      "exec.dispatch"(%157)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb1(%158: !algebra.field<"bls12-381.fr">, %159: ui64):  // pred: ^bb0
      %160 = "exec.returned"(%158, %159) : (!algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%160) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb2(%161: !exec.stop):  // pred: ^bb0
      %162 = "exec.failed"(%161) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%162) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>) -> ()
    }) {runtime.origin = ["finite_zkl_4d05c370830a894df2470c3859782e53b3322378b124acf8f383759935b54a45_s0_body", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_c15efd5f24b71cb9e6e3766d00c208e0a0014177a6ae1e9dd67b23bda4eff8ab", sym_visibility = "private"}> ({
    ^bb0(%arg70: !algebra.field<"bls12-381.fr">, %arg71: !algebra.field<"bls12-381.fr">):
      %156 = "algebra.field_subtract"(%arg70, %arg71) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%156) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_c8eacd293248ba42cad22bd955e2dec7c6105efe1dabf391c3a74b436be7412e", sym_visibility = "private"}> ({
    ^bb0(%arg67: !algebra.field<"bls12-381.fr">, %arg68: !algebra.field<"bls12-381.fr">, %arg69: !algebra.field<"bls12-381.fr">):
      %154 = "algebra.field_subtract"(%arg68, %arg67) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %155 = "algebra.field_multiply"(%154, %arg69) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%155) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_3d3958243128671a7ae06c730aba5c78b4cae61932510ab43ba5bcabe7324295", sym_visibility = "private"}> ({
    ^bb0(%arg64: !runtime.scope, %arg65: !algebra.field_vector<"bls12-381.fr">, %arg66: ui64):
      %141 = "exec.apply"(%arg64) <{binding = @zkl_binding_0, parameters = [], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%141)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%142: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %143 = "exec.compute"(%arg64) <{callee = @zkl_e38306e1154810613f8b855b4e24394048cbbd4c4b2723722235b0e03496f137, site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%143)[^bb3, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%144: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %145 = "exec.failed"(%144) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%145) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%146: !algebra.field<"bls12-381.fr">):  // pred: ^bb1
      %147 = "exec.apply"(%arg64) <{binding = @zkl_binding_3, parameters = ["0"], site = "s2"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%147)[^bb4, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%148: ui64):  // pred: ^bb3
      %149 = "func.call"(%arg64, %142, %146, %148, %arg66, %arg65) <{callee = @zkl_b09f44c87195c8e3d60f4dede007ee713df6eb6126ac95620f16b0ca8ac2c403}> {runtime.site = "s6"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
      "exec.dispatch"(%149)[^bb5, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb5(%150: !algebra.field_vector<"bls12-381.fr">, %151: !algebra.field<"bls12-381.fr">, %152: ui64):  // pred: ^bb4
      %153 = "exec.returned"(%150) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%153) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7210h73686966745f726f7773", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>, no_inline, sym_name = "zkl_abd6f98141af14ddf8b9152129fb3a9fb361b5735ade780e8d1c876d68deb283", sym_visibility = "private"}> ({
    ^bb0(%arg58: !runtime.scope, %arg59: !algebra.field_vector<"bls12-381.fr">, %arg60: !algebra.field<"bls12-381.fr">, %arg61: ui64, %arg62: !algebra.field<"bls12-381.fr">, %arg63: ui64):
      %109 = "exec.apply"(%arg58, %arg61, %arg63) <{binding = @zkl_binding_5, parameters = [], site = "s4"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%109)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%110: ui64):  // pred: ^bb0
      %111 = "exec.apply"(%arg58) <{binding = @zkl_binding_3, parameters = ["0"], site = "s5"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%111)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%112: !exec.stop):  // 13 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb6, ^bb7, ^bb8, ^bb9, ^bb10, ^bb12, ^bb13, ^bb15, ^bb16
      %113 = "exec.failed"(%112) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%113) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb3(%114: ui64):  // pred: ^bb1
      %115 = "exec.apply"(%arg58, %110, %114) <{binding = @zkl_binding_6, parameters = [], site = "s6"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%115)[^bb4, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb4(%116: i1):  // pred: ^bb3
      %117 = "exec.test"(%arg58, %116) <{site = "s8"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%117)[^bb5, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb5(%118: i1):  // pred: ^bb4
      "cf.cond_br"(%118)[^bb6, ^bb7] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb6:  // pred: ^bb5
      %119 = "runtime.enter_scope"(%arg58, %arg60) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "then", site = "s8"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%119)[^bb9, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // pred: ^bb5
      %120 = "runtime.enter_scope"(%arg58, %arg60) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "else", site = "s8"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%120)[^bb12, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb8(%121: !algebra.field<"bls12-381.fr">):  // 2 preds: ^bb11, ^bb14
      %122 = "exec.apply"(%arg58, %arg59, %121) <{binding = @zkl_binding_1, parameters = [], site = "s13"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%122)[^bb15, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb9(%123: !runtime.scope):  // pred: ^bb6
      %124 = "func.call"(%123, %arg60) <{callee = @zkl_control_24}> : (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      %125 = "runtime.exit_scope"(%123, %124) : (!runtime.scope, !exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!algebra.field<"bls12-381.fr">)>)>
      "exec.dispatch"(%125)[^bb10, ^bb2] : (!exec.outcome<(!runtime.transfer<(!algebra.field<"bls12-381.fr">)>)>) -> ()
    ^bb10(%126: !runtime.transfer<(!algebra.field<"bls12-381.fr">)>):  // pred: ^bb9
      %127 = "runtime.accept_transfer"(%arg58, %126) : (!runtime.scope, !runtime.transfer<(!algebra.field<"bls12-381.fr">)>) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%127)[^bb11, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb11(%128: !algebra.field<"bls12-381.fr">):  // pred: ^bb10
      "cf.br"(%128)[^bb8] : (!algebra.field<"bls12-381.fr">) -> ()
    ^bb12(%129: !runtime.scope):  // pred: ^bb7
      %130 = "func.call"(%129, %arg60) <{callee = @zkl_control_25}> : (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      %131 = "runtime.exit_scope"(%129, %130) : (!runtime.scope, !exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!algebra.field<"bls12-381.fr">)>)>
      "exec.dispatch"(%131)[^bb13, ^bb2] : (!exec.outcome<(!runtime.transfer<(!algebra.field<"bls12-381.fr">)>)>) -> ()
    ^bb13(%132: !runtime.transfer<(!algebra.field<"bls12-381.fr">)>):  // pred: ^bb12
      %133 = "runtime.accept_transfer"(%arg58, %132) : (!runtime.scope, !runtime.transfer<(!algebra.field<"bls12-381.fr">)>) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%133)[^bb14, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb14(%134: !algebra.field<"bls12-381.fr">):  // pred: ^bb13
      "cf.br"(%134)[^bb8] : (!algebra.field<"bls12-381.fr">) -> ()
    ^bb15(%135: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb8
      %136 = "exec.apply"(%arg58) <{binding = @zkl_binding_3, parameters = ["1"], site = "s15"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%136)[^bb16, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb16(%137: ui64):  // pred: ^bb15
      %138 = "exec.apply"(%arg58, %arg61, %137) <{binding = @zkl_binding_12, parameters = [], site = "s16"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%138)[^bb17, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb17(%139: ui64):  // pred: ^bb16
      %140 = "exec.returned"(%135, %arg62, %139) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%140) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>) -> ()
    }) {runtime.origin = ["zks_8581fd068387f06c481369dff1456320f16962167c6391f3d8bc1fe2a6daf333", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_24", sym_visibility = "private"}> ({
    ^bb0(%arg56: !runtime.scope, %arg57: !algebra.field<"bls12-381.fr">):
      %104 = "exec.compute"(%arg56) <{callee = @zkl_e38306e1154810613f8b855b4e24394048cbbd4c4b2723722235b0e03496f137, site = "s9"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%104)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%105: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %106 = "exec.complete"(%arg56, %105) : (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%106) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%107: !exec.stop):  // pred: ^bb0
      %108 = "exec.failed"(%107) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%108) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_25", sym_visibility = "private"}> ({
    ^bb0(%arg54: !runtime.scope, %arg55: !algebra.field<"bls12-381.fr">):
      %103 = "exec.complete"(%arg54, %arg55) : (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%103) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>, no_inline, sym_name = "zkl_b09f44c87195c8e3d60f4dede007ee713df6eb6126ac95620f16b0ca8ac2c403", sym_visibility = "private"}> ({
    ^bb0(%arg48: !runtime.scope, %arg49: !algebra.field_vector<"bls12-381.fr">, %arg50: !algebra.field<"bls12-381.fr">, %arg51: ui64, %arg52: ui64, %arg53: !algebra.field_vector<"bls12-381.fr">):
      %96 = "exec.fold"(%arg48, %arg53, %arg49, %arg50, %arg51, %arg52) <{domain = @finite_zkl_b09f44c87195c8e3d60f4dede007ee713df6eb6126ac95620f16b0ca8ac2c403_s0_domain, site = "s0", step = @finite_zkl_b09f44c87195c8e3d60f4dede007ee713df6eb6126ac95620f16b0ca8ac2c403_s0_body}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
      "exec.dispatch"(%96)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb1(%97: !algebra.field_vector<"bls12-381.fr">, %98: !algebra.field<"bls12-381.fr">, %99: ui64):  // pred: ^bb0
      %100 = "exec.returned"(%97, %98, %99) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%100) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb2(%101: !exec.stop):  // pred: ^bb0
      %102 = "exec.failed"(%101) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%102) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_b09f44c87195c8e3d60f4dede007ee713df6eb6126ac95620f16b0ca8ac2c403_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg47: !algebra.field_vector<"bls12-381.fr">):
      %95 = "data.domain_elements"(%arg47) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%95) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>, no_inline, sym_name = "finite_zkl_b09f44c87195c8e3d60f4dede007ee713df6eb6126ac95620f16b0ca8ac2c403_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg40: !runtime.scope, %arg41: !algebra.field_vector<"bls12-381.fr">, %arg42: !algebra.field<"bls12-381.fr">, %arg43: ui64, %arg44: !algebra.field<"bls12-381.fr">, %arg45: !algebra.field_vector<"bls12-381.fr">, %arg46: ui64):
      %88 = "func.call"(%arg40, %arg41, %arg42, %arg43, %arg44, %arg46) <{callee = @zkl_abd6f98141af14ddf8b9152129fb3a9fb361b5735ade780e8d1c876d68deb283}> {runtime.site = "body"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
      "exec.dispatch"(%88)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb1(%89: !algebra.field_vector<"bls12-381.fr">, %90: !algebra.field<"bls12-381.fr">, %91: ui64):  // pred: ^bb0
      %92 = "exec.returned"(%89, %90, %91) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%92) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb2(%93: !exec.stop):  // pred: ^bb0
      %94 = "exec.failed"(%93) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%94) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>) -> ()
    }) {runtime.origin = ["finite_zkl_b09f44c87195c8e3d60f4dede007ee713df6eb6126ac95620f16b0ca8ac2c403_s0_body", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_02aa9bd9900f843069baf97f23f4f5ccab54b136c8fed5b90842e4c46b7e5fcd", sym_visibility = "private"}> ({
    ^bb0(%arg38: !algebra.field<"bls12-381.fr">, %arg39: !algebra.field<"bls12-381.fr">):
      %87 = "algebra.field_add"(%arg38, %arg39) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%87) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_ca5df6081733f8afff4ae42147eb8eba3338d5a96600a7155f619346f19e4b47", sym_visibility = "private"}> ({
    ^bb0(%arg35: !runtime.scope, %arg36: !algebra.field_vector<"bls12-381.fr">, %arg37: ui64):
      %78 = "exec.apply"(%arg35) <{binding = @zkl_binding_3, parameters = ["1"], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%78)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%79: ui64):  // pred: ^bb0
      %80 = "exec.apply"(%arg35, %arg37, %79) <{binding = @zkl_binding_12, parameters = [], site = "s1"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%80)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%81: !exec.stop):  // 3 preds: ^bb0, ^bb1, ^bb3
      %82 = "exec.failed"(%81) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%82) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb3(%83: ui64):  // pred: ^bb1
      %84 = "func.call"(%arg35, %arg36, %83) <{callee = @zkl_6ba53ec68a0230031d706e4a93e78f80425c51108d34ecc0a5aa5681eded9c8e}> {runtime.site = "s2"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%84)[^bb4, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb4(%85: !algebra.field<"bls12-381.fr">):  // pred: ^bb3
      %86 = "exec.returned"(%85) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%86) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7213h656c656d656e745f6166746572", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_6ec6b9d6cb41b6bf4ef8e898ba1b283d099252f7de2db0b173f26714e3a46216", sym_visibility = "private"}> ({
    ^bb0(%arg33: !runtime.scope, %arg34: !algebra.field_vector<"bls12-381.fr">):
      %73 = "exec.apply"(%arg33, %arg34) <{binding = @zkl_binding_4, parameters = [], site = "s0"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%73)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%74: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %75 = "exec.returned"(%74) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%75) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%76: !exec.stop):  // pred: ^bb0
      %77 = "exec.failed"(%76) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%77) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6310h7072696d6974697665736h766563746f723h73756d", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_161d519d8d5fe2674feddb6e6d14269c9cca82ff216b6b3205ade46cc8b8d35f", sym_visibility = "private"}> ({
    ^bb0(%arg28: !runtime.scope, %arg29: !algebra.field_vector<"bls12-381.fr">, %arg30: !algebra.field_vector<"bls12-381.fr">, %arg31: !algebra.field_vector<"bls12-381.fr">, %arg32: !algebra.field_vector<"bls12-381.fr">):
      %38 = "exec.apply"(%arg28, %arg30) <{binding = @zkl_binding_2, parameters = [], site = "s0"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%38)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%39: ui64):  // pred: ^bb0
      %40 = "exec.apply"(%arg28, %arg31) <{binding = @zkl_binding_2, parameters = [], site = "s1"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%40)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%41: !exec.stop):  // 12 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb10, ^bb11, ^bb12
      %42 = "exec.failed"(%41) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%42) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb3(%43: ui64):  // pred: ^bb1
      %44 = "exec.apply"(%arg28, %39, %43) <{binding = @zkl_binding_12, parameters = [], site = "s2"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%44)[^bb4, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%45: ui64):  // pred: ^bb3
      %46 = "exec.apply"(%arg28, %arg32) <{binding = @zkl_binding_2, parameters = [], site = "s3"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%46)[^bb5, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%47: ui64):  // pred: ^bb4
      %48 = "exec.apply"(%arg28, %45, %47) <{binding = @zkl_binding_12, parameters = [], site = "s4"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%48)[^bb6, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb6(%49: ui64):  // pred: ^bb5
      %50 = "exec.apply"(%arg28) <{binding = @zkl_binding_3, parameters = ["1"], site = "s5"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%50)[^bb7, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb7(%51: ui64):  // pred: ^bb6
      %52 = "func.call"(%arg28, %arg29, %49, %51) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a}> {runtime.site = "s6"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%52)[^bb8, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb8(%53: !algebra.field_vector<"bls12-381.fr">, %54: ui64, %55: ui64):  // pred: ^bb7
      %56 = "func.call"(%arg28, %53, %54, %55, %arg30) <{callee = @zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be}> {runtime.site = "s8"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%56)[^bb9, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb9(%57: !algebra.field_vector<"bls12-381.fr">, %58: ui64, %59: ui64):  // pred: ^bb8
      %60 = "func.call"(%arg28, %57, %58, %59, %arg31) <{callee = @zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be}> {runtime.site = "s9"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%60)[^bb10, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb10(%61: !algebra.field_vector<"bls12-381.fr">, %62: ui64, %63: ui64):  // pred: ^bb9
      %64 = "func.call"(%arg28, %61, %62, %63, %arg32) <{callee = @zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be}> {runtime.site = "s10"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%64)[^bb11, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb11(%65: !algebra.field_vector<"bls12-381.fr">, %66: ui64, %67: ui64):  // pred: ^bb10
      %68 = "exec.compute"(%arg28, %65, %66, %67) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33, site = "s11"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%68)[^bb12, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb12(%69: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb11
      %70 = "exec.apply"(%arg28, %69) <{binding = @zkl_binding_4, parameters = [], site = "s12"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%70)[^bb13, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb13(%71: !algebra.field<"bls12-381.fr">):  // pred: ^bb12
      %72 = "exec.returned"(%71) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%72) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7215h6576616c756174655f776972696e67", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_21465134b1aa848c616c790eff1907b1a442ba76730b77da2be48acd923d6ff7", sym_visibility = "private"}> ({
    ^bb0(%arg25: !runtime.scope, %arg26: !algebra.field_vector<"bls12-381.fr">, %arg27: !algebra.field<"bls12-381.fr">):
      %29 = "exec.compute"(%arg25) <{callee = @zkl_acc5a50f3a300b126874f48e782cbb903e9f900ea776915474c16f8e7ecd49b5, site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%29)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%30: !algebra.field<"bls12-381.fr">, %31: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %32 = "func.call"(%arg25, %30, %31, %arg27, %arg26) <{callee = @zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d}> {runtime.site = "s2"} : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%32)[^bb3, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%33: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %34 = "exec.failed"(%33) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%34) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb3(%35: !algebra.field<"bls12-381.fr">, %36: !algebra.field<"bls12-381.fr">):  // pred: ^bb1
      %37 = "exec.returned"(%35) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%37) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7221h6576616c756174655f636f656666696369656e7473", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_bcbdb252ffc9abd0563757a6a45f0dccb9a7c345ecbfb58b787c5137455bd42e", sym_visibility = "private"}> ({
    ^bb0(%arg20: !runtime.scope, %arg21: !algebra.field<"bls12-381.fr">, %arg22: !algebra.field<"bls12-381.fr">, %arg23: !algebra.field<"bls12-381.fr">, %arg24: !algebra.field<"bls12-381.fr">):
      %23 = "exec.compute"(%arg20, %arg21, %arg22, %arg23, %arg24) <{callee = @zkl_82e44b33934fd674fa24fbb7f5705f2364f5020774fe25318dd2b968f9d001e4, site = "s4"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%23)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%24: !algebra.field<"bls12-381.fr">, %25: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %26 = "exec.returned"(%24, %25) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%26) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%27: !exec.stop):  // pred: ^bb0
      %28 = "exec.failed"(%27) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%28) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zks_c896eee882b0de19255b06dc85cce9b3173549e68e26b71cdd01e723c9c5b52d", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), sym_name = "zkl_82e44b33934fd674fa24fbb7f5705f2364f5020774fe25318dd2b968f9d001e4", sym_visibility = "private"}> ({
    ^bb0(%arg16: !algebra.field<"bls12-381.fr">, %arg17: !algebra.field<"bls12-381.fr">, %arg18: !algebra.field<"bls12-381.fr">, %arg19: !algebra.field<"bls12-381.fr">):
      %20 = "algebra.field_multiply"(%arg18, %arg17) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %21 = "algebra.field_add"(%arg16, %20) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %22 = "algebra.field_multiply"(%arg17, %arg19) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%21, %22) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = () -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), sym_name = "zkl_acc5a50f3a300b126874f48e782cbb903e9f900ea776915474c16f8e7ecd49b5", sym_visibility = "private"}> ({
      %18 = "algebra.constant"() <{value = "0"}> : () -> !algebra.field<"bls12-381.fr">
      %19 = "algebra.constant"() <{value = "1"}> : () -> !algebra.field<"bls12-381.fr">
      "func.return"(%18, %19) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d", sym_visibility = "private"}> ({
    ^bb0(%arg11: !runtime.scope, %arg12: !algebra.field<"bls12-381.fr">, %arg13: !algebra.field<"bls12-381.fr">, %arg14: !algebra.field<"bls12-381.fr">, %arg15: !algebra.field_vector<"bls12-381.fr">):
      %12 = "exec.fold"(%arg11, %arg15, %arg12, %arg13, %arg14) <{domain = @finite_zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d_s0_domain, site = "s0", step = @finite_zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d_s0_body}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%12)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%13: !algebra.field<"bls12-381.fr">, %14: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %15 = "exec.returned"(%13, %14) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%15) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%16: !exec.stop):  // pred: ^bb0
      %17 = "exec.failed"(%16) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%17) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg10: !algebra.field_vector<"bls12-381.fr">):
      %11 = "data.domain_elements"(%arg10) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%11) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "finite_zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg4: !runtime.scope, %arg5: !algebra.field<"bls12-381.fr">, %arg6: !algebra.field<"bls12-381.fr">, %arg7: !algebra.field<"bls12-381.fr">, %arg8: !algebra.field_vector<"bls12-381.fr">, %arg9: !algebra.field<"bls12-381.fr">):
      %5 = "func.call"(%arg4, %arg5, %arg6, %arg7, %arg9) <{callee = @zkl_bcbdb252ffc9abd0563757a6a45f0dccb9a7c345ecbfb58b787c5137455bd42e}> {runtime.site = "body"} : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%5)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%6: !algebra.field<"bls12-381.fr">, %7: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %8 = "exec.returned"(%6, %7) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%8) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%9: !exec.stop):  // pred: ^bb0
      %10 = "exec.failed"(%9) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%10) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["finite_zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d_s0_body", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_1f2e31017a1a0403a56241b1d83eac39d1ecc40b298cd066516f78ae9c5b3434", sym_visibility = "private"}> ({
    ^bb0(%arg0: !runtime.scope, %arg1: !algebra.field_vector<"bls12-381.fr">, %arg2: !algebra.field_vector<"bls12-381.fr">, %arg3: !algebra.field<"bls12-381.fr">):
      %0 = "exec.collect"(%arg0, %arg1, %arg2, %arg3) <{body = @zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_body, domain = @zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_domain, site = "s0"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%1: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%2) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%4) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7210h6c696e655f706f696e74", []]} : () -> ()
  }) : () -> ()
}) : () -> ()

