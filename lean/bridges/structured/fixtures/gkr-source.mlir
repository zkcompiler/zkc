"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>, source_declarations = [[[["nominal", "record", "gkr::LayerClaim", [["field", "bls12-381.fr"]]], "linear", true, [["point", ["builtin", "vector", [["field", "bls12-381.fr"]]]], ["value", ["field", "bls12-381.fr"]]]], [["nominal", "record", "gkr::Gates", [["field", "bls12-381.fr"]]], "ordinary", false, [["add", ["builtin", "vector", [["field", "bls12-381.fr"]]]], ["mul", ["builtin", "vector", [["field", "bls12-381.fr"]]]], ["left", ["builtin", "vector", [["field", "bls12-381.fr"]]]], ["right", ["builtin", "vector", [["field", "bls12-381.fr"]]]]]], [["nominal", "record", "gkr::Pending", [["field", "bls12-381.fr"]]], "linear", true, [["point", ["builtin", "vector", [["field", "bls12-381.fr"]]]], ["value", ["field", "bls12-381.fr"]]]], [["nominal", "record", "zkc::multilinear::Table", [["field", "bls12-381.fr"]]], "ordinary", false, [["entries", ["builtin", "vector", [["field", "bls12-381.fr"]]]], ["dimensions", ["index"]], ["columns", ["index"]]]]], [["zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [["inputs", ["builtin", "vector", [["field", "bls12-381.fr"]]], ["role00000000", "role00000001"], 0 : ui64, 1 : ui64], ["outputs", ["builtin", "vector", [["field", "bls12-381.fr"]]], ["role00000001"], 1 : ui64, 1 : ui64], ["add", ["builtin", "vector", [["field", "bls12-381.fr"]]], ["role00000000", "role00000001"], 2 : ui64, 1 : ui64], ["mul", ["builtin", "vector", [["field", "bls12-381.fr"]]], ["role00000000", "role00000001"], 3 : ui64, 1 : ui64], ["layers", ["index"], ["role00000000", "role00000001"], 4 : ui64, 1 : ui64], ["selector", ["index"], ["role00000000", "role00000001"], 5 : ui64, 1 : ui64], ["width", ["index"], ["role00000000", "role00000001"], 6 : ui64, 1 : ui64]], [["accepted", ["bool"], ["role00000001"], 0 : ui64, 1 : ui64]]], ["zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", [["gates", ["nominal", "record", "gkr::Gates", [["field", "bls12-381.fr"]]], ["role00000000"], 0 : ui64, 4 : ui64], ["claim", ["nominal", "record", "gkr::Pending", [["field", "bls12-381.fr"]]], ["role00000001"], 4 : ui64, 2 : ui64], ["rounds", ["index"], ["role00000000", "role00000001"], 6 : ui64, 1 : ui64]], [["point", ["builtin", "vector", [["field", "bls12-381.fr"]]], ["role00000000"], 0 : ui64, 1 : ui64], ["residual", ["nominal", "record", "gkr::Gates", [["field", "bls12-381.fr"]]], ["role00000000"], 1 : ui64, 4 : ui64], ["evaluation", ["nominal", "record", "gkr::Pending", [["field", "bls12-381.fr"]]], ["role00000001"], 5 : ui64, 2 : ui64]]], ["zkl_9719be65739d901a935dbaa0f3f8323a785562f7eee1e60cc8c8c9676f8fdb55", [["values", ["builtin", "vector", [["field", "bls12-381.fr"]]], ["role00000000"], 0 : ui64, 1 : ui64], ["claim", ["nominal", "record", "gkr::LayerClaim", [["field", "bls12-381.fr"]]], ["role00000000"], 1 : ui64, 2 : ui64]], [["accepted", ["bool"], ["role00000000"], 0 : ui64, 1 : ui64]]]]]}> ({
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "field.equal", function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>, implementation = "", sym_name = "zkl_binding_13"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.split", function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>, implementation = "", sym_name = "zkl_binding_12"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.sub", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_11"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.sum", function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, implementation = "", sym_name = "zkl_binding_10"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.append", function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, implementation = "", sym_name = "zkl_binding_9"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.empty", function_type = (!runtime.scope) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, implementation = "", sym_name = "zkl_binding_8"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.add", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_7"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.mul", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_6"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.div", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_5"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.equal", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>, implementation = "", sym_name = "zkl_binding_4"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.mod", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_3"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.length", function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_2"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.constant", function_type = (!runtime.scope) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_1"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.less", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>, implementation = "", sym_name = "zkl_binding_0"}> : () -> ()
    "protocol.func"() <{contracts = [["input", "shape", [@zkl_cb1c10731e59161b14394fbb472272285b0bbba78877994f53fa6955497a3df4, [["input", 0, "role00000001"], ["input", 1, "role00000001"], ["input", 2, "role00000001"], ["input", 3, "role00000001"], ["input", 4, "role00000001"], ["input", 5, "role00000001"], ["input", 6, "role00000001"]]], unit, unit], ["target", "circuit_outputs", [@zkl_5effead4fa609f078c405b9340f603e2dc77b3e9155c76d7032b9f0b55bf1801, [["input", 0, "role00000001"], ["input", 2, "role00000001"], ["input", 3, "role00000001"], ["input", 4, "role00000001"], ["input", 5, "role00000001"], ["input", 6, "role00000001"], ["input", 1, "role00000001"]]], unit, ["output", 0, "role00000001"]]], function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> i1, input_roles = [["role00000000", "role00000001"], ["role00000001"], ["role00000000", "role00000001"], ["role00000000", "role00000001"], ["role00000000", "role00000001"], ["role00000000", "role00000001"], ["role00000000", "role00000001"], ["role00000001"]], origin = ["gkr::Gkr", [["F", ["field", "bls12-381.fr"]], ["MaxLayers", ["nat", "4"]], ["MaxWidth", ["nat", "4"]]]], output_roles = [["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2"}> ({
    ^bb0(%arg475: !algebra.field_vector<"bls12-381.fr">, %arg476: !algebra.field_vector<"bls12-381.fr">, %arg477: !algebra.field_vector<"bls12-381.fr">, %arg478: !algebra.field_vector<"bls12-381.fr">, %arg479: ui64, %arg480: ui64, %arg481: ui64, %arg482: !protocol.service_ref<"random.bls12-381.fr/0">):
      %1161 = "data.index"() <{value = 4 : ui64}> : () -> ui64
      %1162 = "protocol.local_call"(%1161, %arg481) <{callee = @s3h7a6b637h696e64696365734h6c657373, role = "role00000001", site = "s1"}> : (ui64, ui64) -> i1
      %1163 = "arith.constant"() <{value = false}> : () -> i1
      %1164 = "arith.cmpi"(%1162, %1163) <{predicate = 0 : i64}> : (i1, i1) -> i1
      "protocol.guard"(%1164) <{owner = "role00000001", site = "s4"}> : (i1) -> ()
      %1165 = "data.index"() <{value = 4 : ui64}> : () -> ui64
      %1166 = "protocol.local_call"(%1165, %arg479) <{callee = @s3h7a6b637h696e64696365734h6c657373, role = "role00000001", site = "s6"}> : (ui64, ui64) -> i1
      %1167 = "arith.constant"() <{value = false}> : () -> i1
      %1168 = "arith.cmpi"(%1166, %1167) <{predicate = 0 : i64}> : (i1, i1) -> i1
      "protocol.guard"(%1168) <{owner = "role00000001", site = "s9"}> : (i1) -> ()
      %1169 = "data.index"() <{value = 1 : ui64}> : () -> ui64
      %1170 = "protocol.local_call"(%arg475, %arg481, %1169) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655, role = "role00000001", site = "s11"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1
      "protocol.guard"(%1170) <{owner = "role00000001", site = "s12"}> : (i1) -> ()
      %1171 = "data.index"() <{value = 1 : ui64}> : () -> ui64
      %1172 = "protocol.local_call"(%arg476, %arg481, %1171) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655, role = "role00000001", site = "s14"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1
      "protocol.guard"(%1172) <{owner = "role00000001", site = "s15"}> : (i1) -> ()
      %1173 = "protocol.local_call"(%arg480, %arg481) <{callee = @s3h7a6b637h7072656c7564659h696e6465785f616464, role = "role00000001", site = "s16"}> : (ui64, ui64) -> ui64
      %1174 = "protocol.local_call"(%1173, %arg481) <{callee = @s3h7a6b637h7072656c7564659h696e6465785f616464, role = "role00000001", site = "s17"}> : (ui64, ui64) -> ui64
      %1175 = "protocol.local_call"(%1174, %arg481) <{callee = @s3h7a6b637h7072656c7564659h696e6465785f616464, role = "role00000001", site = "s18"}> : (ui64, ui64) -> ui64
      %1176 = "data.index"() <{value = 1 : ui64}> : () -> ui64
      %1177 = "protocol.local_call"(%arg477, %1175, %1176) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655, role = "role00000001", site = "s20"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1
      "protocol.guard"(%1177) <{owner = "role00000001", site = "s21"}> : (i1) -> ()
      %1178 = "protocol.local_call"(%arg480, %arg481) <{callee = @s3h7a6b637h7072656c7564659h696e6465785f616464, role = "role00000001", site = "s22"}> : (ui64, ui64) -> ui64
      %1179 = "protocol.local_call"(%1178, %arg481) <{callee = @s3h7a6b637h7072656c7564659h696e6465785f616464, role = "role00000001", site = "s23"}> : (ui64, ui64) -> ui64
      %1180 = "protocol.local_call"(%1179, %arg481) <{callee = @s3h7a6b637h7072656c7564659h696e6465785f616464, role = "role00000001", site = "s24"}> : (ui64, ui64) -> ui64
      %1181 = "data.index"() <{value = 1 : ui64}> : () -> ui64
      %1182 = "protocol.local_call"(%arg478, %1180, %1181) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655, role = "role00000001", site = "s26"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1
      "protocol.guard"(%1182) <{owner = "role00000001", site = "s27"}> : (i1) -> ()
      %1183 = "protocol.local_call"(%arg480) <{callee = @s3h676b7212h706f7765725f6f665f74776f, role = "role00000001", site = "s28"}> : (ui64) -> ui64
      %1184 = "protocol.local_call"(%1183, %arg479) <{callee = @s3h7a6b637h696e64696365734h6c657373, role = "role00000001", site = "s29"}> : (ui64, ui64) -> i1
      %1185 = "arith.constant"() <{value = false}> : () -> i1
      %1186 = "arith.cmpi"(%1184, %1185) <{predicate = 0 : i64}> : (i1, i1) -> i1
      "protocol.guard"(%1186) <{owner = "role00000001", site = "s32"}> : (i1) -> ()
      %1187 = "protocol.local_call"() <{callee = @zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f, role = "role00000001", site = "s33"}> : () -> !algebra.field_vector<"bls12-381.fr">
      %1188 = "protocol.local_call"() <{callee = @zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f, role = "role00000000", site = "s35"}> : () -> !algebra.field_vector<"bls12-381.fr">
      %1189:2 = "protocol.repeat"(%arg481, %1187, %1188, %arg482) <{carried = 2 : i64, carried_roles = [["role00000001"], ["role00000000"]], maximum = 4 : i64, roles = ["role00000000", "role00000001"], site = "s37"}> ({
      ^bb0(%arg497: ui64, %arg498: !algebra.field_vector<"bls12-381.fr">, %arg499: !algebra.field_vector<"bls12-381.fr">, %arg500: !protocol.service_ref<"random.bls12-381.fr/0">):
        %1234 = "protocol.query"(%arg500) <{method = "draw", owner = "role00000001", site = "label_6f7574707574"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
        %1235 = "protocol.exchange"(%1234) <{receiver = "role00000000", sender = "role00000001", site = "label_6f75747075745f64656c6976657279_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1236 = "protocol.restrict_roles"(%1235) <{roles = ["role00000000"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1237 = "protocol.local_call"(%arg498, %1234) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000001", site = "s42"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
        %1238 = "protocol.local_call"(%arg499, %1236) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000000", site = "s44"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
        "protocol.yield"(%1237, %1238) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> ()
      }) : (ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)
      %1190 = "protocol.local_call"(%arg476, %1189#0) <{callee = @zkl_28c1498dbf9d83fc38ed7b21a89d56146297abcbf1ac78968a8b454c9eef5496, role = "role00000001", site = "s48"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %1191:2 = "protocol.local_call"(%1189#0, %1190) <{callee = @zkl_7b9dfa97fa3e158d428459ec12d8a2d5aa171a060ab79f314eeccc53ee772b17, role = "role00000001", site = "s49"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %1192:3 = "protocol.repeat"(%arg479, %1189#1, %1191#0, %1191#1, %arg475, %arg477, %arg478, %arg479, %arg480, %arg481, %arg482) <{carried = 3 : i64, carried_roles = [["role00000000"], ["role00000001"], ["role00000001"]], maximum = 4 : i64, roles = ["role00000000", "role00000001"], site = "s57"}> ({
      ^bb0(%arg483: ui64, %arg484: !algebra.field_vector<"bls12-381.fr">, %arg485: !algebra.field_vector<"bls12-381.fr">, %arg486: !algebra.field<"bls12-381.fr">, %arg487: !algebra.field_vector<"bls12-381.fr">, %arg488: !algebra.field_vector<"bls12-381.fr">, %arg489: !algebra.field_vector<"bls12-381.fr">, %arg490: ui64, %arg491: ui64, %arg492: ui64, %arg493: !protocol.service_ref<"random.bls12-381.fr/0">):
        %1194:2 = "protocol.local_call"(%arg485, %arg486) <{callee = @zkl_e0f7a4e58ae24eb13e9b2033c42c179b2766ff6cdb4ae1470bf7ef9b1721d646, role = "role00000001", site = "s58"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %1195 = "protocol.local_call"(%arg488, %arg489, %arg487, %arg490, %arg491, %arg492, %arg483) <{callee = @zkl_8c63ad97d926a7762c597860addde408bcd2077ea9cda1b99df123dc13e64af6, role = "role00000000", site = "s60"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">
        %1196 = "protocol.local_call"(%arg488, %arg483, %arg491) <{callee = @zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e, role = "role00000000", site = "s62"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">
        %1197 = "protocol.local_call"(%arg489, %arg483, %arg491) <{callee = @zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e, role = "role00000000", site = "s63"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">
        %1198:4 = "protocol.local_call"(%1196, %1197, %arg484, %1195, %arg492) <{callee = @zkl_d1f2756b99b17aad26e4b85a966eec4c9419609618b22e3ee7f8a3349cb1e33b, role = "role00000000", site = "s64"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)
        %1199:2 = "protocol.local_call"(%1194#1) <{callee = @zkl_e1405e1bb4604e60f337203132c746492bf7c31b55302426ae19c2c021c2da1a, role = "role00000001", site = "s67"}> : (!algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %1200:7 = "protocol.apply"(%1198#0, %1198#1, %1198#2, %1198#3, %1199#0, %1199#1, %arg492, %arg493) <{callee = @zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba, roles = ["role00000000", "role00000001"], site = "label_6c656674"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %1201:7 = "protocol.apply"(%1200#1, %1200#2, %1200#3, %1200#4, %1200#5, %1200#6, %arg492, %arg493) <{callee = @zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba, roles = ["role00000000", "role00000001"], site = "label_7269676874"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %1202:2 = "protocol.local_call"(%1201#5, %1201#6) <{callee = @zkl_bd4f0d76e787de675c5732a4a96fc396d45486f32b3dcda5182ccc324969c825, role = "role00000001", site = "s76"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %1203:2 = "protocol.local_call"(%1202#0) <{callee = @zkl_cfcf40daaab145a916368cf7a01eccd9ba0e536fbbc30a06c4a25e7ec96ecbe7, role = "role00000001", site = "s79"}> : (!algebra.field_vector<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)
        %1204 = "protocol.local_call"(%1195, %1200#0, %1201#0, %arg492) <{callee = @zkl_91fe8ea73b5db3432f90fc8fe9725c8455fce8782b4cc4d2839d05826de71b8f, role = "role00000000", site = "s81"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64) -> !algebra.field_vector<"bls12-381.fr">
        %1205 = "data.index"() <{value = 0 : ui64}> : () -> ui64
        %1206 = "protocol.local_call"(%1204, %1205) <{callee = @zkl_6ba53ec68a0230031d706e4a93e78f80425c51108d34ecc0a5aa5681eded9c8e, role = "role00000000", site = "s84"}> : (!algebra.field_vector<"bls12-381.fr">, ui64) -> !algebra.field<"bls12-381.fr">
        %1207 = "protocol.exchange"(%1206) <{receiver = "role00000001", sender = "role00000000", site = "label_6c696e655f636f6e7374616e74_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1208 = "protocol.restrict_roles"(%1207) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1209 = "protocol.local_call"() <{callee = @zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f, role = "role00000001", site = "s87"}> : () -> !algebra.field_vector<"bls12-381.fr">
        %1210 = "protocol.local_call"(%1209, %1208) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000001", site = "s88"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
        %1211 = "protocol.repeat"(%arg492, %1210, %1204) <{carried = 1 : i64, carried_roles = [["role00000001"]], maximum = 4 : i64, roles = ["role00000000", "role00000001"], site = "s91"}> ({
        ^bb0(%arg494: ui64, %arg495: !algebra.field_vector<"bls12-381.fr">, %arg496: !algebra.field_vector<"bls12-381.fr">):
          %1230 = "protocol.local_call"(%arg496, %arg494) <{callee = @zkl_ca5df6081733f8afff4ae42147eb8eba3338d5a96600a7155f619346f19e4b47, role = "role00000000", site = "s92"}> : (!algebra.field_vector<"bls12-381.fr">, ui64) -> !algebra.field<"bls12-381.fr">
          %1231 = "protocol.exchange"(%1230) <{receiver = "role00000001", sender = "role00000000", site = "label_6c696e655f636f656666696369656e74_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
          %1232 = "protocol.restrict_roles"(%1231) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
          %1233 = "protocol.local_call"(%arg495, %1232) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000001", site = "s95"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
          "protocol.yield"(%1233) : (!algebra.field_vector<"bls12-381.fr">) -> ()
        }) : (ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
        %1212 = "protocol.local_call"(%1211) <{callee = @zkl_6ec6b9d6cb41b6bf4ef8e898ba1b283d099252f7de2db0b173f26714e3a46216, role = "role00000001", site = "s99"}> : (!algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1213 = "protocol.local_call"(%arg488, %arg483, %arg491) <{callee = @zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e, role = "role00000001", site = "s101"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">
        %1214 = "protocol.local_call"(%1213, %1194#0, %1203#0, %1203#1) <{callee = @zkl_161d519d8d5fe2674feddb6e6d14269c9cca82ff216b6b3205ade46cc8b8d35f, role = "role00000001", site = "s105"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1215 = "protocol.local_call"(%arg489, %arg483, %arg491) <{callee = @zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e, role = "role00000001", site = "s107"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">
        %1216 = "protocol.local_call"(%1215, %1194#0, %1203#0, %1203#1) <{callee = @zkl_161d519d8d5fe2674feddb6e6d14269c9cca82ff216b6b3205ade46cc8b8d35f, role = "role00000001", site = "s111"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1217 = "algebra.field_add"(%1208, %1212) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1218 = "algebra.field_multiply"(%1214, %1217) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1219 = "algebra.field_multiply"(%1216, %1208) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1220 = "algebra.field_multiply"(%1219, %1212) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1221 = "algebra.field_add"(%1218, %1220) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1222 = "algebra.field_equal"(%1202#1, %1221) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
        "protocol.guard"(%1222) <{owner = "role00000001", site = "s120"}> : (i1) -> ()
        %1223 = "protocol.query"(%arg493) <{method = "draw", owner = "role00000001", site = "label_6c696e655f6368616c6c656e6765"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
        %1224 = "protocol.exchange"(%1223) <{receiver = "role00000000", sender = "role00000001", site = "label_6c696e655f64656c6976657279_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1225 = "protocol.restrict_roles"(%1224) <{roles = ["role00000000"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1226 = "protocol.local_call"(%1203#0, %1203#1, %1223) <{callee = @zkl_1f2e31017a1a0403a56241b1d83eac39d1ecc40b298cd066516f78ae9c5b3434, role = "role00000001", site = "s127"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
        %1227 = "protocol.local_call"(%1211, %1223) <{callee = @zkl_21465134b1aa848c616c790eff1907b1a442ba76730b77da2be48acd923d6ff7, role = "role00000001", site = "s128"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1228:2 = "protocol.local_call"(%1226, %1227) <{callee = @zkl_7b9dfa97fa3e158d428459ec12d8a2d5aa171a060ab79f314eeccc53ee772b17, role = "role00000001", site = "s129"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %1229 = "protocol.local_call"(%1200#0, %1201#0, %1225) <{callee = @zkl_1f2e31017a1a0403a56241b1d83eac39d1ecc40b298cd066516f78ae9c5b3434, role = "role00000000", site = "s131"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
        "protocol.yield"(%1229, %1228#0, %1228#1) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
      }) : (ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %1193 = "protocol.apply"(%arg475, %1192#1, %1192#2) <{callee = @zkl_9719be65739d901a935dbaa0f3f8323a785562f7eee1e60cc8c8c9676f8fdb55, roles = ["role00000001"], site = "label_696e707574"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "protocol.return"(%1193) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "s3h7a6b637h696e64696365734h6c657373", sym_visibility = "private"}> ({
    ^bb0(%arg472: !runtime.scope, %arg473: ui64, %arg474: ui64):
      %1156 = "exec.apply"(%arg472, %arg473, %arg474) <{binding = @zkl_binding_0, parameters = [], site = "s0"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1156)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1157: i1):  // pred: ^bb0
      %1158 = "exec.returned"(%1157) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%1158) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%1159: !exec.stop):  // pred: ^bb0
      %1160 = "exec.failed"(%1159) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%1160) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.origin = ["s3h7a6b637h696e64696365734h6c657373", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", sym_visibility = "private"}> ({
    ^bb0(%arg468: !runtime.scope, %arg469: !algebra.field_vector<"bls12-381.fr">, %arg470: ui64, %arg471: ui64):
      %1098 = "exec.apply"(%arg468) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1098)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1099: ui64):  // pred: ^bb0
      %1100 = "func.call"(%arg468, %1099, %arg471) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s1"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1100)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%1101: !exec.stop):  // 23 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12, ^bb15, ^bb16, ^bb17, ^bb18, ^bb19, ^bb21, ^bb22, ^bb25, ^bb26, ^bb28, ^bb29, ^bb31, ^bb32
      %1102 = "exec.failed"(%1101) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%1102) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%1103: i1):  // pred: ^bb1
      %1104 = "exec.test"(%arg468, %1103) <{site = "s3"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1104)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb4(%1105: i1):  // pred: ^bb3
      "cf.cond_br"(%1105)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %1106 = "runtime.enter_scope"(%arg468, %arg470) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "then", site = "s3"}> : (!runtime.scope, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1106)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %1107 = "runtime.enter_scope"(%arg468, %arg470) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "else", site = "s3"}> : (!runtime.scope, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1107)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7(%1108: i1):  // 2 preds: ^bb10, ^bb13
      %1109 = "exec.test"(%arg468, %1108) <{site = "s11"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1109)[^bb14, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb8(%1110: !runtime.scope):  // pred: ^bb5
      %1111 = "func.call"(%1110, %arg470) <{callee = @zkl_control_0}> : (!runtime.scope, ui64) -> !exec.outcome<(i1)>
      %1112 = "runtime.exit_scope"(%1110, %1111) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%1112)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb9(%1113: !runtime.transfer<(i1)>):  // pred: ^bb8
      %1114 = "runtime.accept_transfer"(%arg468, %1113) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1114)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb10(%1115: i1):  // pred: ^bb9
      "cf.br"(%1115)[^bb7] : (i1) -> ()
    ^bb11(%1116: !runtime.scope):  // pred: ^bb6
      %1117 = "func.call"(%1116, %arg470) <{callee = @zkl_control_1}> : (!runtime.scope, ui64) -> !exec.outcome<(i1)>
      %1118 = "runtime.exit_scope"(%1116, %1117) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%1118)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb12(%1119: !runtime.transfer<(i1)>):  // pred: ^bb11
      %1120 = "runtime.accept_transfer"(%arg468, %1119) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1120)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb13(%1121: i1):  // pred: ^bb12
      "cf.br"(%1121)[^bb7] : (i1) -> ()
    ^bb14(%1122: i1):  // pred: ^bb7
      "cf.cond_br"(%1122)[^bb15, ^bb16] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb15:  // pred: ^bb14
      %1123 = "runtime.enter_scope"(%arg468, %arg469, %arg471) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "then", site = "s11"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1123)[^bb18, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb16:  // pred: ^bb14
      %1124 = "runtime.enter_scope"(%arg468, %arg469, %arg471) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "else", site = "s11"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1124)[^bb21, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb17(%1125: i1):  // 2 preds: ^bb20, ^bb23
      %1126 = "exec.test"(%arg468, %1125) <{site = "s22"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1126)[^bb24, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb18(%1127: !runtime.scope):  // pred: ^bb15
      %1128 = "func.call"(%1127, %arg469, %arg471) <{callee = @zkl_control_2}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>
      %1129 = "runtime.exit_scope"(%1127, %1128) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%1129)[^bb19, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb19(%1130: !runtime.transfer<(i1)>):  // pred: ^bb18
      %1131 = "runtime.accept_transfer"(%arg468, %1130) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1131)[^bb20, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb20(%1132: i1):  // pred: ^bb19
      "cf.br"(%1132)[^bb17] : (i1) -> ()
    ^bb21(%1133: !runtime.scope):  // pred: ^bb16
      %1134 = "func.call"(%1133, %arg469, %arg471) <{callee = @zkl_control_3}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>
      %1135 = "runtime.exit_scope"(%1133, %1134) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%1135)[^bb22, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb22(%1136: !runtime.transfer<(i1)>):  // pred: ^bb21
      %1137 = "runtime.accept_transfer"(%arg468, %1136) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1137)[^bb23, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb23(%1138: i1):  // pred: ^bb22
      "cf.br"(%1138)[^bb17] : (i1) -> ()
    ^bb24(%1139: i1):  // pred: ^bb17
      "cf.cond_br"(%1139)[^bb25, ^bb26] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb25:  // pred: ^bb24
      %1140 = "runtime.enter_scope"(%arg468, %arg469, %arg470, %arg471) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "then", site = "s22"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1140)[^bb28, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb26:  // pred: ^bb24
      %1141 = "runtime.enter_scope"(%arg468, %arg469, %arg470, %arg471) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "else", site = "s22"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1141)[^bb31, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb27(%1142: i1):  // 2 preds: ^bb30, ^bb33
      %1143 = "exec.returned"(%1142) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%1143) : (!exec.outcome<(i1)>) -> ()
    ^bb28(%1144: !runtime.scope):  // pred: ^bb25
      %1145 = "func.call"(%1144, %arg469, %arg470, %arg471) <{callee = @zkl_control_4}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      %1146 = "runtime.exit_scope"(%1144, %1145) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%1146)[^bb29, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb29(%1147: !runtime.transfer<(i1)>):  // pred: ^bb28
      %1148 = "runtime.accept_transfer"(%arg468, %1147) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1148)[^bb30, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb30(%1149: i1):  // pred: ^bb29
      "cf.br"(%1149)[^bb27] : (i1) -> ()
    ^bb31(%1150: !runtime.scope):  // pred: ^bb26
      %1151 = "func.call"(%1150, %arg469, %arg470, %arg471) <{callee = @zkl_control_5}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      %1152 = "runtime.exit_scope"(%1150, %1151) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%1152)[^bb32, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb32(%1153: !runtime.transfer<(i1)>):  // pred: ^bb31
      %1154 = "runtime.accept_transfer"(%arg468, %1153) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1154)[^bb33, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb33(%1155: i1):  // pred: ^bb32
      "cf.br"(%1155)[^bb27] : (i1) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_0", sym_visibility = "private"}> ({
    ^bb0(%arg466: !runtime.scope, %arg467: ui64):
      %1091 = "exec.apply"(%arg466) <{binding = @zkl_binding_1, parameters = [64 : ui64], site = "s4"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1091)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1092: ui64):  // pred: ^bb0
      %1093 = "func.call"(%arg466, %arg467, %1092) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s5"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1093)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%1094: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %1095 = "exec.failed"(%1094) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%1095) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%1096: i1):  // pred: ^bb1
      %1097 = "exec.complete"(%arg466, %1096) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%1097) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_1", sym_visibility = "private"}> ({
    ^bb0(%arg464: !runtime.scope, %arg465: ui64):
      %1086 = "exec.boolean"(%arg464) <{site = "s7", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1086)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1087: i1):  // pred: ^bb0
      %1088 = "exec.complete"(%arg464, %1087) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%1088) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%1089: !exec.stop):  // pred: ^bb0
      %1090 = "exec.failed"(%1089) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%1090) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_2", sym_visibility = "private"}> ({
    ^bb0(%arg461: !runtime.scope, %arg462: !algebra.field_vector<"bls12-381.fr">, %arg463: ui64):
      %1075 = "exec.apply"(%arg461, %arg462) <{binding = @zkl_binding_2, parameters = [], site = "s12"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1075)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1076: ui64):  // pred: ^bb0
      %1077 = "exec.apply"(%arg461, %1076, %arg463) <{binding = @zkl_binding_3, parameters = [], site = "s13"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1077)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%1078: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %1079 = "exec.failed"(%1078) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%1079) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%1080: ui64):  // pred: ^bb1
      %1081 = "exec.apply"(%arg461) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s14"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1081)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%1082: ui64):  // pred: ^bb3
      %1083 = "exec.apply"(%arg461, %1080, %1082) <{binding = @zkl_binding_4, parameters = [], site = "s15"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1083)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb5(%1084: i1):  // pred: ^bb4
      %1085 = "exec.complete"(%arg461, %1084) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%1085) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_3", sym_visibility = "private"}> ({
    ^bb0(%arg458: !runtime.scope, %arg459: !algebra.field_vector<"bls12-381.fr">, %arg460: ui64):
      %1070 = "exec.boolean"(%arg458) <{site = "s17", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1070)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1071: i1):  // pred: ^bb0
      %1072 = "exec.complete"(%arg458, %1071) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%1072) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%1073: !exec.stop):  // pred: ^bb0
      %1074 = "exec.failed"(%1073) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%1074) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_4", sym_visibility = "private"}> ({
    ^bb0(%arg454: !runtime.scope, %arg455: !algebra.field_vector<"bls12-381.fr">, %arg456: ui64, %arg457: ui64):
      %1059 = "exec.apply"(%arg454, %arg455) <{binding = @zkl_binding_2, parameters = [], site = "s23"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1059)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1060: ui64):  // pred: ^bb0
      %1061 = "exec.apply"(%arg454, %1060, %arg457) <{binding = @zkl_binding_5, parameters = [], site = "s24"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1061)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%1062: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %1063 = "exec.failed"(%1062) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%1063) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%1064: ui64):  // pred: ^bb1
      %1065 = "func.call"(%arg454, %arg456) <{callee = @s3h7a6b6311h6d756c74696c696e6561724h726f7773}> {runtime.site = "s25"} : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1065)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%1066: ui64):  // pred: ^bb3
      %1067 = "exec.apply"(%arg454, %1064, %1066) <{binding = @zkl_binding_4, parameters = [], site = "s26"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1067)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb5(%1068: i1):  // pred: ^bb4
      %1069 = "exec.complete"(%arg454, %1068) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%1069) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_5", sym_visibility = "private"}> ({
    ^bb0(%arg450: !runtime.scope, %arg451: !algebra.field_vector<"bls12-381.fr">, %arg452: ui64, %arg453: ui64):
      %1054 = "exec.boolean"(%arg450) <{site = "s28", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1054)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1055: i1):  // pred: ^bb0
      %1056 = "exec.complete"(%arg450, %1055) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%1056) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%1057: !exec.stop):  // pred: ^bb0
      %1058 = "exec.failed"(%1057) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%1058) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "s3h7a6b6311h6d756c74696c696e6561724h726f7773", sym_visibility = "private"}> ({
    ^bb0(%arg448: !runtime.scope, %arg449: ui64):
      %1007 = "exec.apply"(%arg448) <{binding = @zkl_binding_1, parameters = [64 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1007)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1008: ui64):  // pred: ^bb0
      %1009 = "func.call"(%arg448, %arg449, %1008) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s1"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1009)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%1010: !exec.stop):  // 14 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12, ^bb14, ^bb15, ^bb19, ^bb21
      %1011 = "exec.failed"(%1010) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%1011) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%1012: i1):  // pred: ^bb1
      %1013 = "exec.test"(%arg448, %1012) <{site = "s2"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1013)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb4(%1014: i1):  // pred: ^bb3
      "cf.cond_br"(%1014)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %1015 = "runtime.enter_scope"(%arg448) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s2"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1015)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %1016 = "runtime.enter_scope"(%arg448) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s2"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1016)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // 2 preds: ^bb10, ^bb13
      %1017 = "exec.apply"(%arg448) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s3"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1017)[^bb14, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb8(%1018: !runtime.scope):  // pred: ^bb5
      %1019 = "func.call"(%1018) <{callee = @zkl_control_6}> : (!runtime.scope) -> !exec.outcome<>
      %1020 = "runtime.exit_scope"(%1018, %1019) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%1020)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb9(%1021: !runtime.transfer<>):  // pred: ^bb8
      %1022 = "runtime.accept_transfer"(%arg448, %1021) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%1022)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb10:  // pred: ^bb9
      "cf.br"()[^bb7] : () -> ()
    ^bb11(%1023: !runtime.scope):  // pred: ^bb6
      %1024 = "func.call"(%1023) <{callee = @zkl_control_7}> : (!runtime.scope) -> !exec.outcome<>
      %1025 = "runtime.exit_scope"(%1023, %1024) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%1025)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb12(%1026: !runtime.transfer<>):  // pred: ^bb11
      %1027 = "runtime.accept_transfer"(%arg448, %1026) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%1027)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb13:  // pred: ^bb12
      "cf.br"()[^bb7] : () -> ()
    ^bb14(%1028: ui64):  // pred: ^bb7
      %1029 = "exec.apply"(%arg448) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s5"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1029)[^bb15, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb15(%1030: ui64):  // pred: ^bb14
      %1031 = "exec.range"(%arg448, %1030, %arg449) <{site = "s6"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%1031)[^bb16, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i64, i64)>) -> ()
    ^bb16(%1032: i64, %1033: i64):  // pred: ^bb15
      %1034 = "runtime.borrow_transfer"(%arg448, %1028) : (!runtime.scope, ui64) -> !runtime.transfer<(ui64)>
      "cf.br"(%1032, %1034)[^bb17] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb17(%1035: i64, %1036: !runtime.transfer<(ui64)>):  // 2 preds: ^bb16, ^bb20
      %1037 = "arith.cmpi"(%1035, %1033) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%1037, %1036)[^bb18, ^bb19] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(ui64)>) -> ()
    ^bb18:  // pred: ^bb17
      %1038 = "runtime.iteration"(%arg448, %1035) <{site = "s6"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1038)[^bb22, ^bb21] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb19(%1039: !runtime.transfer<(ui64)>):  // pred: ^bb17
      %1040 = "runtime.accept_transfer"(%arg448, %1039) : (!runtime.scope, !runtime.transfer<(ui64)>) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1040)[^bb25, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb20(%1041: !runtime.transfer<(ui64)>):  // pred: ^bb24
      %1042 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %1043 = "arith.addi"(%1035, %1042) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%1043, %1041)[^bb17] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb21(%1044: !exec.stop):  // 3 preds: ^bb18, ^bb22, ^bb23
      "runtime.release_transfer"(%1036) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%1044)[^bb2] : (!exec.stop) -> ()
    ^bb22(%1045: ui64):  // pred: ^bb18
      %1046 = "runtime.transfer_values"(%1036) : (!runtime.transfer<(ui64)>) -> ui64
      %1047 = "runtime.enter_scope"(%arg448, %1035, %1045, %1046) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 2>, site = "s6"}> : (!runtime.scope, i64, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1047)[^bb23, ^bb21] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb23(%1048: !runtime.scope):  // pred: ^bb22
      %1049 = "func.call"(%1048, %1045, %1046) <{callee = @zkl_control_8}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      %1050 = "runtime.exit_scope"(%1048, %1049) : (!runtime.scope, !exec.outcome<(ui64)>) -> !exec.outcome<(!runtime.transfer<(ui64)>)>
      "exec.dispatch"(%1050)[^bb24, ^bb21] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(ui64)>)>) -> ()
    ^bb24(%1051: !runtime.transfer<(ui64)>):  // pred: ^bb23
      "runtime.release_transfer"(%1036) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%1051)[^bb20] : (!runtime.transfer<(ui64)>) -> ()
    ^bb25(%1052: ui64):  // pred: ^bb19
      %1053 = "exec.returned"(%1052) : (ui64) -> !exec.outcome<(ui64)>
      "func.return"(%1053) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561724h726f7773", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_6", sym_visibility = "private"}> ({
    ^bb0(%arg447: !runtime.scope):
      %1006 = "exec.complete"(%arg447) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%1006) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_7", sym_visibility = "private"}> ({
    ^bb0(%arg446: !runtime.scope):
      %1003 = "exec.reject"(%arg446) <{reason = "reject", site = "s2_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%1003)[^bb1] : (!exec.stop) -> ()
    ^bb1(%1004: !exec.stop):  // pred: ^bb0
      %1005 = "exec.failed"(%1004) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%1005) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "zkl_control_8", sym_visibility = "private"}> ({
    ^bb0(%arg443: !runtime.scope, %arg444: ui64, %arg445: ui64):
      %996 = "exec.apply"(%arg443) <{binding = @zkl_binding_1, parameters = [2 : ui64], site = "s7"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%996)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%997: ui64):  // pred: ^bb0
      %998 = "exec.apply"(%arg443, %arg445, %997) <{binding = @zkl_binding_6, parameters = [], site = "s8"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%998)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%999: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %1000 = "exec.failed"(%999) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%1000) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%1001: ui64):  // pred: ^bb1
      %1002 = "exec.complete"(%arg443, %1001) : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "func.return"(%1002) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "s3h7a6b637h7072656c7564659h696e6465785f616464", sym_visibility = "private"}> ({
    ^bb0(%arg440: !runtime.scope, %arg441: ui64, %arg442: ui64):
      %991 = "exec.apply"(%arg440, %arg441, %arg442) <{binding = @zkl_binding_7, parameters = [], site = "s0"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%991)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%992: ui64):  // pred: ^bb0
      %993 = "exec.returned"(%992) : (ui64) -> !exec.outcome<(ui64)>
      "func.return"(%993) : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%994: !exec.stop):  // pred: ^bb0
      %995 = "exec.failed"(%994) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%995) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b637h7072656c7564659h696e6465785f616464", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "s3h676b7212h706f7765725f6f665f74776f", sym_visibility = "private"}> ({
    ^bb0(%arg438: !runtime.scope, %arg439: ui64):
      %962 = "exec.apply"(%arg438) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%962)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%963: ui64):  // pred: ^bb0
      %964 = "exec.apply"(%arg438) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s2"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%964)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%965: !exec.stop):  // 5 preds: ^bb0, ^bb1, ^bb3, ^bb7, ^bb9
      %966 = "exec.failed"(%965) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%966) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%967: ui64):  // pred: ^bb1
      %968 = "exec.range"(%arg438, %967, %arg439) <{site = "s3"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%968)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i64, i64)>) -> ()
    ^bb4(%969: i64, %970: i64):  // pred: ^bb3
      %971 = "runtime.borrow_transfer"(%arg438, %963) : (!runtime.scope, ui64) -> !runtime.transfer<(ui64)>
      "cf.br"(%969, %971)[^bb5] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb5(%972: i64, %973: !runtime.transfer<(ui64)>):  // 2 preds: ^bb4, ^bb8
      %974 = "arith.cmpi"(%972, %970) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%974, %973)[^bb6, ^bb7] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(ui64)>) -> ()
    ^bb6:  // pred: ^bb5
      %975 = "runtime.iteration"(%arg438, %972) <{site = "s3"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%975)[^bb10, ^bb9] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb7(%976: !runtime.transfer<(ui64)>):  // pred: ^bb5
      %977 = "runtime.accept_transfer"(%arg438, %976) : (!runtime.scope, !runtime.transfer<(ui64)>) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%977)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb8(%978: !runtime.transfer<(ui64)>):  // pred: ^bb12
      %979 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %980 = "arith.addi"(%972, %979) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%980, %978)[^bb5] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb9(%981: !exec.stop):  // 3 preds: ^bb6, ^bb10, ^bb11
      "runtime.release_transfer"(%973) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%981)[^bb2] : (!exec.stop) -> ()
    ^bb10(%982: ui64):  // pred: ^bb6
      %983 = "runtime.transfer_values"(%973) : (!runtime.transfer<(ui64)>) -> ui64
      %984 = "runtime.enter_scope"(%arg438, %972, %982, %983) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 2>, site = "s3"}> : (!runtime.scope, i64, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%984)[^bb11, ^bb9] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb11(%985: !runtime.scope):  // pred: ^bb10
      %986 = "func.call"(%985, %982, %983) <{callee = @zkl_control_9}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      %987 = "runtime.exit_scope"(%985, %986) : (!runtime.scope, !exec.outcome<(ui64)>) -> !exec.outcome<(!runtime.transfer<(ui64)>)>
      "exec.dispatch"(%987)[^bb12, ^bb9] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(ui64)>)>) -> ()
    ^bb12(%988: !runtime.transfer<(ui64)>):  // pred: ^bb11
      "runtime.release_transfer"(%973) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%988)[^bb8] : (!runtime.transfer<(ui64)>) -> ()
    ^bb13(%989: ui64):  // pred: ^bb7
      %990 = "exec.returned"(%989) : (ui64) -> !exec.outcome<(ui64)>
      "func.return"(%990) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.origin = ["s3h676b7212h706f7765725f6f665f74776f", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "zkl_control_9", sym_visibility = "private"}> ({
    ^bb0(%arg435: !runtime.scope, %arg436: ui64, %arg437: ui64):
      %955 = "exec.apply"(%arg435) <{binding = @zkl_binding_1, parameters = [2 : ui64], site = "s4"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%955)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%956: ui64):  // pred: ^bb0
      %957 = "exec.apply"(%arg435, %arg437, %956) <{binding = @zkl_binding_6, parameters = [], site = "s5"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%957)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%958: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %959 = "exec.failed"(%958) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%959) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%960: ui64):  // pred: ^bb1
      %961 = "exec.complete"(%arg435, %960) : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "func.return"(%961) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", sym_visibility = "private"}> ({
    ^bb0(%arg434: !runtime.scope):
      %950 = "exec.apply"(%arg434) <{binding = @zkl_binding_8, parameters = [], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%950)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%951: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %952 = "exec.returned"(%951) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%952) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%953: !exec.stop):  // pred: ^bb0
      %954 = "exec.failed"(%953) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%954) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6310h7072696d6974697665736h766563746f725h656d707479", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", sym_visibility = "private"}> ({
    ^bb0(%arg431: !runtime.scope, %arg432: !algebra.field_vector<"bls12-381.fr">, %arg433: !algebra.field<"bls12-381.fr">):
      %945 = "exec.apply"(%arg431, %arg432, %arg433) <{binding = @zkl_binding_9, parameters = [], site = "s0"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%945)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%946: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %947 = "exec.returned"(%946) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%947) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%948: !exec.stop):  // pred: ^bb0
      %949 = "exec.failed"(%948) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%949) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6310h7072696d6974697665736h766563746f726h617070656e64", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_28c1498dbf9d83fc38ed7b21a89d56146297abcbf1ac78968a8b454c9eef5496", sym_visibility = "private"}> ({
    ^bb0(%arg428: !runtime.scope, %arg429: !algebra.field_vector<"bls12-381.fr">, %arg430: !algebra.field_vector<"bls12-381.fr">):
      %926 = "exec.apply"(%arg428, %arg430) <{binding = @zkl_binding_2, parameters = [], site = "s0"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%926)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%927: ui64):  // pred: ^bb0
      %928 = "exec.apply"(%arg428) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s1"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%928)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%929: !exec.stop):  // 6 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6
      %930 = "exec.failed"(%929) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%930) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb3(%931: ui64):  // pred: ^bb1
      %932 = "func.call"(%arg428, %arg429, %927, %931) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a}> {runtime.site = "s2"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%932)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb4(%933: !algebra.field_vector<"bls12-381.fr">, %934: ui64, %935: ui64):  // pred: ^bb3
      %936 = "func.call"(%arg428, %933, %934, %935, %arg430) <{callee = @zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be}> {runtime.site = "s4"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%936)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb5(%937: !algebra.field_vector<"bls12-381.fr">, %938: ui64, %939: ui64):  // pred: ^bb4
      %940 = "exec.compute"(%arg428, %937, %938, %939) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33, site = "s5"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%940)[^bb6, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb6(%941: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb5
      %942 = "exec.apply"(%arg428, %941) <{binding = @zkl_binding_10, parameters = [], site = "s6"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%942)[^bb7, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb7(%943: !algebra.field<"bls12-381.fr">):  // pred: ^bb6
      %944 = "exec.returned"(%943) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%944) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b728h6576616c75617465", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", sym_visibility = "private"}> ({
    ^bb0(%arg424: !runtime.scope, %arg425: !algebra.field_vector<"bls12-381.fr">, %arg426: ui64, %arg427: ui64):
      %907 = "func.call"(%arg424, %arg425, %arg426, %arg427) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655}> {runtime.site = "s0"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%907)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%908: i1):  // pred: ^bb0
      %909 = "exec.test"(%arg424, %908) <{site = "s1"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%909)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%910: !exec.stop):  // 8 preds: ^bb0, ^bb1, ^bb4, ^bb5, ^bb7, ^bb8, ^bb10, ^bb11
      %911 = "exec.failed"(%910) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%911) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb3(%912: i1):  // pred: ^bb1
      "cf.cond_br"(%912)[^bb4, ^bb5] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb4:  // pred: ^bb3
      %913 = "runtime.enter_scope"(%arg424) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%913)[^bb7, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb5:  // pred: ^bb3
      %914 = "runtime.enter_scope"(%arg424) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%914)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // 2 preds: ^bb9, ^bb12
      %915 = "exec.returned"(%arg425, %arg426, %arg427) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%915) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb7(%916: !runtime.scope):  // pred: ^bb4
      %917 = "func.call"(%916) <{callee = @zkl_control_10}> : (!runtime.scope) -> !exec.outcome<>
      %918 = "runtime.exit_scope"(%916, %917) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%918)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb8(%919: !runtime.transfer<>):  // pred: ^bb7
      %920 = "runtime.accept_transfer"(%arg424, %919) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%920)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb9:  // pred: ^bb8
      "cf.br"()[^bb6] : () -> ()
    ^bb10(%921: !runtime.scope):  // pred: ^bb5
      %922 = "func.call"(%921) <{callee = @zkl_control_11}> : (!runtime.scope) -> !exec.outcome<>
      %923 = "runtime.exit_scope"(%921, %922) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%923)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb11(%924: !runtime.transfer<>):  // pred: ^bb10
      %925 = "runtime.accept_transfer"(%arg424, %924) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%925)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb12:  // pred: ^bb11
      "cf.br"()[^bb6] : () -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561725h7461626c65", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_10", sym_visibility = "private"}> ({
    ^bb0(%arg423: !runtime.scope):
      %906 = "exec.complete"(%arg423) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%906) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_11", sym_visibility = "private"}> ({
    ^bb0(%arg422: !runtime.scope):
      %903 = "exec.reject"(%arg422) <{reason = "reject", site = "s1_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%903)[^bb1] : (!exec.stop) -> ()
    ^bb1(%904: !exec.stop):  // pred: ^bb0
      %905 = "exec.failed"(%904) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%905) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be", sym_visibility = "private"}> ({
    ^bb0(%arg417: !runtime.scope, %arg418: !algebra.field_vector<"bls12-381.fr">, %arg419: ui64, %arg420: ui64, %arg421: !algebra.field_vector<"bls12-381.fr">):
      %896 = "func.call"(%arg417, %arg418, %arg419, %arg420, %arg421) <{callee = @zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2}> {runtime.site = "s0"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%896)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb1(%897: !algebra.field_vector<"bls12-381.fr">, %898: ui64, %899: ui64):  // pred: ^bb0
      %900 = "exec.returned"(%897, %898, %899) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%900) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb2(%901: !exec.stop):  // pred: ^bb0
      %902 = "exec.failed"(%901) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%902) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e65617210h6669785f707265666978", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_195a79478f48dffc2a6917273d8317df0fabae786920a46fa2ac6b2737144299", sym_visibility = "private"}> ({
    ^bb0(%arg412: !runtime.scope, %arg413: !algebra.field_vector<"bls12-381.fr">, %arg414: ui64, %arg415: ui64, %arg416: !algebra.field<"bls12-381.fr">):
      %889 = "func.call"(%arg412, %arg413, %arg414, %arg415, %arg416) <{callee = @zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d}> {runtime.site = "s2"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%889)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb1(%890: !algebra.field_vector<"bls12-381.fr">, %891: ui64, %892: ui64):  // pred: ^bb0
      %893 = "exec.returned"(%890, %891, %892) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%893) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb2(%894: !exec.stop):  // pred: ^bb0
      %895 = "exec.failed"(%894) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%895) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["zks_50b2228592370f9a2bce2e71277fbb9bf36d691d6ece4416923708e3a0c063ae", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d", sym_visibility = "private"}> ({
    ^bb0(%arg407: !runtime.scope, %arg408: !algebra.field_vector<"bls12-381.fr">, %arg409: ui64, %arg410: ui64, %arg411: !algebra.field<"bls12-381.fr">):
      %877 = "func.call"(%arg407, %arg408, %arg409, %arg410) <{callee = @zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087}> {runtime.site = "s0"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%877)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%878: !algebra.field_vector<"bls12-381.fr">, %879: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %880 = "exec.collect"(%arg407, %878, %879, %arg411) <{body = @zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body, domain = @zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_domain, site = "s4"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%880)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%881: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %882 = "exec.failed"(%881) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%882) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb3(%883: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb1
      %884 = "exec.apply"(%arg407) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s7"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%884)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%885: ui64):  // pred: ^bb3
      %886 = "exec.apply"(%arg407, %arg409, %885) <{binding = @zkl_binding_11, parameters = [], site = "s8"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%886)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%887: ui64):  // pred: ^bb4
      %888 = "exec.returned"(%883, %887, %arg410) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%888) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561729h6669785f6669727374", []]} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, sym_name = "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_domain", sym_visibility = "private"}> ({
    ^bb0(%arg405: !algebra.field_vector<"bls12-381.fr">, %arg406: !algebra.field_vector<"bls12-381.fr">):
      %874 = "data.domain_elements"(%arg405) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %875 = "data.domain_elements"(%arg406) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %876 = "data.domain_zip"(%874, %875) : (!data.domain<!algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%876) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body", sym_visibility = "private"}> ({
    ^bb0(%arg399: !runtime.scope, %arg400: !algebra.field<"bls12-381.fr">, %arg401: !algebra.field<"bls12-381.fr">, %arg402: !algebra.field_vector<"bls12-381.fr">, %arg403: !algebra.field_vector<"bls12-381.fr">, %arg404: !algebra.field<"bls12-381.fr">):
      %869 = "exec.compute"(%arg399, %arg400, %arg401, %arg404) <{callee = @zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5, site = "body"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%869)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%870: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %871 = "exec.returned"(%870) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%871) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%872: !exec.stop):  // pred: ^bb0
      %873 = "exec.failed"(%872) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%873) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087", sym_visibility = "private"}> ({
    ^bb0(%arg395: !runtime.scope, %arg396: !algebra.field_vector<"bls12-381.fr">, %arg397: ui64, %arg398: ui64):
      %845 = "exec.apply"(%arg395) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%845)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%846: ui64):  // pred: ^bb0
      %847 = "func.call"(%arg395, %846, %arg397) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s2"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%847)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%848: !exec.stop):  // 10 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12
      %849 = "exec.failed"(%848) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%849) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%850: i1):  // pred: ^bb1
      %851 = "exec.test"(%arg395, %850) <{site = "s3"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%851)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb4(%852: i1):  // pred: ^bb3
      "cf.cond_br"(%852)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %853 = "runtime.enter_scope"(%arg395) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s3"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%853)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %854 = "runtime.enter_scope"(%arg395) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s3"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%854)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // 2 preds: ^bb10, ^bb13
      %855 = "exec.apply"(%arg395, %arg396) <{binding = @zkl_binding_12, parameters = [], site = "s5"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%855)[^bb14, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%856: !runtime.scope):  // pred: ^bb5
      %857 = "func.call"(%856) <{callee = @zkl_control_12}> : (!runtime.scope) -> !exec.outcome<>
      %858 = "runtime.exit_scope"(%856, %857) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%858)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb9(%859: !runtime.transfer<>):  // pred: ^bb8
      %860 = "runtime.accept_transfer"(%arg395, %859) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%860)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb10:  // pred: ^bb9
      "cf.br"()[^bb7] : () -> ()
    ^bb11(%861: !runtime.scope):  // pred: ^bb6
      %862 = "func.call"(%861) <{callee = @zkl_control_13}> : (!runtime.scope) -> !exec.outcome<>
      %863 = "runtime.exit_scope"(%861, %862) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%863)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb12(%864: !runtime.transfer<>):  // pred: ^bb11
      %865 = "runtime.accept_transfer"(%arg395, %864) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%865)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb13:  // pred: ^bb12
      "cf.br"()[^bb7] : () -> ()
    ^bb14(%866: !algebra.field_vector<"bls12-381.fr">, %867: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb7
      %868 = "exec.returned"(%866, %867) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%868) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561726h68616c766573", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_12", sym_visibility = "private"}> ({
    ^bb0(%arg394: !runtime.scope):
      %844 = "exec.complete"(%arg394) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%844) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_13", sym_visibility = "private"}> ({
    ^bb0(%arg393: !runtime.scope):
      %841 = "exec.reject"(%arg393) <{reason = "reject", site = "s3_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%841)[^bb1] : (!exec.stop) -> ()
    ^bb1(%842: !exec.stop):  // pred: ^bb0
      %843 = "exec.failed"(%842) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%843) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5", sym_visibility = "private"}> ({
    ^bb0(%arg390: !algebra.field<"bls12-381.fr">, %arg391: !algebra.field<"bls12-381.fr">, %arg392: !algebra.field<"bls12-381.fr">):
      %838 = "algebra.field_subtract"(%arg391, %arg390) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %839 = "algebra.field_multiply"(%838, %arg392) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %840 = "algebra.field_add"(%arg390, %839) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%840) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2", sym_visibility = "private"}> ({
    ^bb0(%arg385: !runtime.scope, %arg386: !algebra.field_vector<"bls12-381.fr">, %arg387: ui64, %arg388: ui64, %arg389: !algebra.field_vector<"bls12-381.fr">):
      %831 = "exec.fold"(%arg385, %arg389, %arg386, %arg387, %arg388) <{domain = @finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_domain, site = "s0", step = @finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%831)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb1(%832: !algebra.field_vector<"bls12-381.fr">, %833: ui64, %834: ui64):  // pred: ^bb0
      %835 = "exec.returned"(%832, %833, %834) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%835) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb2(%836: !exec.stop):  // pred: ^bb0
      %837 = "exec.failed"(%836) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%837) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg384: !algebra.field_vector<"bls12-381.fr">):
      %830 = "data.domain_elements"(%arg384) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%830) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg378: !runtime.scope, %arg379: !algebra.field_vector<"bls12-381.fr">, %arg380: ui64, %arg381: ui64, %arg382: !algebra.field<"bls12-381.fr">, %arg383: !algebra.field_vector<"bls12-381.fr">):
      %823 = "func.call"(%arg378, %arg379, %arg380, %arg381, %arg382) <{callee = @zkl_195a79478f48dffc2a6917273d8317df0fabae786920a46fa2ac6b2737144299}> {runtime.site = "body"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%823)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb1(%824: !algebra.field_vector<"bls12-381.fr">, %825: ui64, %826: ui64):  // pred: ^bb0
      %827 = "exec.returned"(%824, %825, %826) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%827) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb2(%828: !exec.stop):  // pred: ^bb0
      %829 = "exec.failed"(%828) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%829) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">, sym_name = "zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", sym_visibility = "private"}> ({
    ^bb0(%arg375: !algebra.field_vector<"bls12-381.fr">, %arg376: ui64, %arg377: ui64):
      "func.return"(%arg375) : (!algebra.field_vector<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_7b9dfa97fa3e158d428459ec12d8a2d5aa171a060ab79f314eeccc53ee772b17", sym_visibility = "private"}> ({
    ^bb0(%arg372: !runtime.scope, %arg373: !algebra.field_vector<"bls12-381.fr">, %arg374: !algebra.field<"bls12-381.fr">):
      %822 = "exec.returned"(%arg373, %arg374) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%822) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7211h6c617965725f636c61696d", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_e0f7a4e58ae24eb13e9b2033c42c179b2766ff6cdb4ae1470bf7ef9b1721d646", sym_visibility = "private"}> ({
    ^bb0(%arg369: !runtime.scope, %arg370: !algebra.field_vector<"bls12-381.fr">, %arg371: !algebra.field<"bls12-381.fr">):
      %821 = "exec.returned"(%arg370, %arg371) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%821) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7210h6f70656e5f6c61796572", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_8c63ad97d926a7762c597860addde408bcd2077ea9cda1b99df123dc13e64af6", sym_visibility = "private"}> ({
    ^bb0(%arg361: !runtime.scope, %arg362: !algebra.field_vector<"bls12-381.fr">, %arg363: !algebra.field_vector<"bls12-381.fr">, %arg364: !algebra.field_vector<"bls12-381.fr">, %arg365: ui64, %arg366: ui64, %arg367: ui64, %arg368: ui64):
      %787 = "exec.apply"(%arg361) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s2"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%787)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%788: ui64):  // pred: ^bb0
      %789 = "exec.apply"(%arg361, %arg365, %arg368) <{binding = @zkl_binding_11, parameters = [], site = "s3"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%789)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%790: !exec.stop):  // 7 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb9, ^bb11
      %791 = "exec.failed"(%790) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%791) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%792: ui64):  // pred: ^bb1
      %793 = "exec.apply"(%arg361) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s4"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%793)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%794: ui64):  // pred: ^bb3
      %795 = "exec.apply"(%arg361, %792, %794) <{binding = @zkl_binding_11, parameters = [], site = "s5"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%795)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%796: ui64):  // pred: ^bb4
      %797 = "exec.range"(%arg361, %788, %796) <{site = "s10"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%797)[^bb6, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i64, i64)>) -> ()
    ^bb6(%798: i64, %799: i64):  // pred: ^bb5
      %800 = "runtime.borrow_transfer"(%arg361, %arg364, %arg365) : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>
      "cf.br"(%798, %800)[^bb7] : (i64, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb7(%801: i64, %802: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>):  // 2 preds: ^bb6, ^bb10
      %803 = "arith.cmpi"(%801, %799) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%803, %802)[^bb8, ^bb9] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb8:  // pred: ^bb7
      %804 = "runtime.iteration"(%arg361, %801) <{site = "s10"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%804)[^bb12, ^bb11] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb9(%805: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>):  // pred: ^bb7
      %806 = "runtime.accept_transfer"(%arg361, %805) : (!runtime.scope, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>
      "exec.dispatch"(%806)[^bb15, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb10(%807: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>):  // pred: ^bb14
      %808 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %809 = "arith.addi"(%801, %808) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%809, %807)[^bb7] : (i64, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb11(%810: !exec.stop):  // 3 preds: ^bb8, ^bb12, ^bb13
      "runtime.release_transfer"(%802) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
      "cf.br"(%810)[^bb2] : (!exec.stop) -> ()
    ^bb12(%811: ui64):  // pred: ^bb8
      %812:2 = "runtime.transfer_values"(%802) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> (!algebra.field_vector<"bls12-381.fr">, ui64)
      %813 = "runtime.enter_scope"(%arg361, %801, %811, %812#0, %812#1, %arg362, %arg363, %arg366, %arg367) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 7>, site = "s10"}> : (!runtime.scope, i64, ui64, !algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%813)[^bb13, ^bb11] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb13(%814: !runtime.scope):  // pred: ^bb12
      %815 = "func.call"(%814, %811, %812#0, %812#1, %arg362, %arg363, %arg366, %arg367) <{callee = @zkl_control_14}> : (!runtime.scope, ui64, !algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>
      %816 = "runtime.exit_scope"(%814, %815) : (!runtime.scope, !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> !exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>)>
      "exec.dispatch"(%816)[^bb14, ^bb11] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>)>) -> ()
    ^bb14(%817: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>):  // pred: ^bb13
      "runtime.release_transfer"(%802) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
      "cf.br"(%817)[^bb10] : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb15(%818: !algebra.field_vector<"bls12-381.fr">, %819: ui64):  // pred: ^bb9
      %820 = "exec.returned"(%818) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%820) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7212h76616c7565735f62656c6f77", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, !algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>, no_inline, sym_name = "zkl_control_14", sym_visibility = "private"}> ({
    ^bb0(%arg353: !runtime.scope, %arg354: ui64, %arg355: !algebra.field_vector<"bls12-381.fr">, %arg356: ui64, %arg357: !algebra.field_vector<"bls12-381.fr">, %arg358: !algebra.field_vector<"bls12-381.fr">, %arg359: ui64, %arg360: ui64):
      %774 = "exec.apply"(%arg353) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s11"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%774)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%775: ui64):  // pred: ^bb0
      %776 = "exec.apply"(%arg353, %arg356, %775) <{binding = @zkl_binding_11, parameters = [], site = "s12"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%776)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%777: !exec.stop):  // 5 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5
      %778 = "exec.failed"(%777) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>
      "func.return"(%778) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb3(%779: ui64):  // pred: ^bb1
      %780 = "func.call"(%arg353, %arg357, %779, %arg359) <{callee = @zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e}> {runtime.site = "s14"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%780)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb4(%781: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb3
      %782 = "func.call"(%arg353, %arg358, %779, %arg359) <{callee = @zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e}> {runtime.site = "s15"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%782)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb5(%783: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb4
      %784 = "func.call"(%arg353, %781, %783, %arg355, %arg360) <{callee = @zkl_3a99bc0fa1dab7cb27c9ec80754c3782b0a32e76ddc961a50e12c24c6cbff683}> {runtime.site = "s16"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%784)[^bb6, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb6(%785: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb5
      %786 = "exec.complete"(%arg353, %785, %779) : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>
      "func.return"(%786) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", sym_visibility = "private"}> ({
    ^bb0(%arg349: !runtime.scope, %arg350: !algebra.field_vector<"bls12-381.fr">, %arg351: ui64, %arg352: ui64):
      %746 = "exec.apply"(%arg349) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s2"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%746)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%747: ui64):  // pred: ^bb0
      %748 = "exec.range"(%arg349, %747, %arg352) <{site = "s4"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%748)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i64, i64)>) -> ()
    ^bb2(%749: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb6, ^bb8
      %750 = "exec.failed"(%749) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%750) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%751: i64, %752: i64):  // pred: ^bb1
      %753 = "runtime.borrow_transfer"(%arg349, %arg350, %arg352) : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>
      "cf.br"(%751, %753)[^bb4] : (i64, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb4(%754: i64, %755: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>):  // 2 preds: ^bb3, ^bb7
      %756 = "arith.cmpi"(%754, %752) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%756, %755)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb5:  // pred: ^bb4
      %757 = "runtime.iteration"(%arg349, %754) <{site = "s4"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%757)[^bb9, ^bb8] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb6(%758: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>):  // pred: ^bb4
      %759 = "runtime.accept_transfer"(%arg349, %758) : (!runtime.scope, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>
      "exec.dispatch"(%759)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb7(%760: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>):  // pred: ^bb11
      %761 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %762 = "arith.addi"(%754, %761) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%762, %760)[^bb4] : (i64, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb8(%763: !exec.stop):  // 3 preds: ^bb5, ^bb9, ^bb10
      "runtime.release_transfer"(%755) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
      "cf.br"(%763)[^bb2] : (!exec.stop) -> ()
    ^bb9(%764: ui64):  // pred: ^bb5
      %765:2 = "runtime.transfer_values"(%755) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> (!algebra.field_vector<"bls12-381.fr">, ui64)
      %766 = "runtime.enter_scope"(%arg349, %754, %764, %765#0, %765#1, %arg351) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 4>, site = "s4"}> : (!runtime.scope, i64, ui64, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%766)[^bb10, ^bb8] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb10(%767: !runtime.scope):  // pred: ^bb9
      %768 = "func.call"(%767, %764, %765#0, %765#1, %arg351) <{callee = @zkl_control_15}> : (!runtime.scope, ui64, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>
      %769 = "runtime.exit_scope"(%767, %768) : (!runtime.scope, !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> !exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>)>
      "exec.dispatch"(%769)[^bb11, ^bb8] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>)>) -> ()
    ^bb11(%770: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>):  // pred: ^bb10
      "runtime.release_transfer"(%755) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
      "cf.br"(%770)[^bb7] : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb12(%771: !algebra.field_vector<"bls12-381.fr">, %772: ui64):  // pred: ^bb6
      %773 = "exec.returned"(%771) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%773) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7212h73656c6563745f626c6f636b", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>, no_inline, sym_name = "zkl_control_15", sym_visibility = "private"}> ({
    ^bb0(%arg344: !runtime.scope, %arg345: ui64, %arg346: !algebra.field_vector<"bls12-381.fr">, %arg347: ui64, %arg348: ui64):
      %707 = "exec.apply"(%arg344) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s5"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%707)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%708: ui64):  // pred: ^bb0
      %709 = "exec.apply"(%arg344, %arg347, %708) <{binding = @zkl_binding_11, parameters = [], site = "s6"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%709)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%710: !exec.stop):  // 16 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb10, ^bb12, ^bb13, ^bb15, ^bb16, ^bb18, ^bb19
      %711 = "exec.failed"(%710) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>
      "func.return"(%711) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb3(%712: ui64):  // pred: ^bb1
      %713 = "func.call"(%arg344, %712) <{callee = @s3h676b7212h706f7765725f6f665f74776f}> {runtime.site = "s8"} : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%713)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%714: ui64):  // pred: ^bb3
      %715 = "exec.apply"(%arg344, %arg348, %714) <{binding = @zkl_binding_5, parameters = [], site = "s9"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%715)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%716: ui64):  // pred: ^bb4
      %717 = "exec.apply"(%arg344) <{binding = @zkl_binding_1, parameters = [2 : ui64], site = "s10"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%717)[^bb6, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb6(%718: ui64):  // pred: ^bb5
      %719 = "exec.apply"(%arg344, %716, %718) <{binding = @zkl_binding_3, parameters = [], site = "s11"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%719)[^bb7, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb7(%720: ui64):  // pred: ^bb6
      %721 = "exec.apply"(%arg344, %arg346) <{binding = @zkl_binding_12, parameters = [], site = "s13"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%721)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%722: !algebra.field_vector<"bls12-381.fr">, %723: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb7
      %724 = "exec.apply"(%arg344) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s15"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%724)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb9(%725: ui64):  // pred: ^bb8
      %726 = "exec.apply"(%arg344, %720, %725) <{binding = @zkl_binding_4, parameters = [], site = "s16"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%726)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb10(%727: i1):  // pred: ^bb9
      %728 = "exec.test"(%arg344, %727) <{site = "s19"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%728)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb11(%729: i1):  // pred: ^bb10
      "cf.cond_br"(%729)[^bb12, ^bb13] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb12:  // pred: ^bb11
      %730 = "runtime.enter_scope"(%arg344, %722, %723) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "then", site = "s19"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%730)[^bb15, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb13:  // pred: ^bb11
      %731 = "runtime.enter_scope"(%arg344, %722, %723) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "else", site = "s19"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%731)[^bb18, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb14(%732: !algebra.field_vector<"bls12-381.fr">):  // 2 preds: ^bb17, ^bb20
      %733 = "exec.complete"(%arg344, %732, %712) : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>
      "func.return"(%733) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb15(%734: !runtime.scope):  // pred: ^bb12
      %735 = "func.call"(%734, %722, %723) <{callee = @zkl_control_16}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      %736 = "runtime.exit_scope"(%734, %735) : (!runtime.scope, !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>)>
      "exec.dispatch"(%736)[^bb16, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>)>) -> ()
    ^bb16(%737: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>):  // pred: ^bb15
      %738 = "runtime.accept_transfer"(%arg344, %737) : (!runtime.scope, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%738)[^bb17, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb17(%739: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb16
      "cf.br"(%739)[^bb14] : (!algebra.field_vector<"bls12-381.fr">) -> ()
    ^bb18(%740: !runtime.scope):  // pred: ^bb13
      %741 = "func.call"(%740, %722, %723) <{callee = @zkl_control_17}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      %742 = "runtime.exit_scope"(%740, %741) : (!runtime.scope, !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>)>
      "exec.dispatch"(%742)[^bb19, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>)>) -> ()
    ^bb19(%743: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>):  // pred: ^bb18
      %744 = "runtime.accept_transfer"(%arg344, %743) : (!runtime.scope, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%744)[^bb20, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb20(%745: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb19
      "cf.br"(%745)[^bb14] : (!algebra.field_vector<"bls12-381.fr">) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_16", sym_visibility = "private"}> ({
    ^bb0(%arg341: !runtime.scope, %arg342: !algebra.field_vector<"bls12-381.fr">, %arg343: !algebra.field_vector<"bls12-381.fr">):
      %706 = "exec.complete"(%arg341, %arg343) : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%706) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_17", sym_visibility = "private"}> ({
    ^bb0(%arg338: !runtime.scope, %arg339: !algebra.field_vector<"bls12-381.fr">, %arg340: !algebra.field_vector<"bls12-381.fr">):
      %705 = "exec.complete"(%arg338, %arg339) : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%705) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_3a99bc0fa1dab7cb27c9ec80754c3782b0a32e76ddc961a50e12c24c6cbff683", sym_visibility = "private"}> ({
    ^bb0(%arg333: !runtime.scope, %arg334: !algebra.field_vector<"bls12-381.fr">, %arg335: !algebra.field_vector<"bls12-381.fr">, %arg336: !algebra.field_vector<"bls12-381.fr">, %arg337: ui64):
      %670 = "func.call"(%arg333, %arg337) <{callee = @s3h676b7212h706f7765725f6f665f74776f}> {runtime.site = "s0"} : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%670)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%671: ui64):  // pred: ^bb0
      %672 = "func.call"(%arg333, %arg336, %671) <{callee = @zkl_afd97de07c9ccae9db68186ebf66098aed7daffb4b11c598d0da5cd116df8490}> {runtime.site = "s2"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%672)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%673: !exec.stop):  // 8 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb10, ^bb12
      %674 = "exec.failed"(%673) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%674) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%675: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb1
      %676 = "func.call"(%arg333, %arg336, %671) <{callee = @zkl_33f3047479634e63ecd16a0855f88ad8af019c37d677a4ffe6f5bacc63307947}> {runtime.site = "s4"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%676)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb4(%677: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb3
      %678 = "exec.apply"(%arg333) <{binding = @zkl_binding_8, parameters = [], site = "s6"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%678)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb5(%679: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb4
      %680 = "exec.apply"(%arg333) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s8"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%680)[^bb6, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb6(%681: ui64):  // pred: ^bb5
      %682 = "exec.range"(%arg333, %681, %671) <{site = "s14"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%682)[^bb7, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i64, i64)>) -> ()
    ^bb7(%683: i64, %684: i64):  // pred: ^bb6
      %685 = "runtime.borrow_transfer"(%arg333, %679) : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>
      "cf.br"(%683, %685)[^bb8] : (i64, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%686: i64, %687: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>):  // 2 preds: ^bb7, ^bb11
      %688 = "arith.cmpi"(%686, %684) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%688, %687)[^bb9, ^bb10] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb9:  // pred: ^bb8
      %689 = "runtime.iteration"(%arg333, %686) <{site = "s14"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%689)[^bb13, ^bb12] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb10(%690: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>):  // pred: ^bb8
      %691 = "runtime.accept_transfer"(%arg333, %690) : (!runtime.scope, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%691)[^bb16, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb11(%692: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>):  // pred: ^bb15
      %693 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %694 = "arith.addi"(%686, %693) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%694, %692)[^bb8] : (i64, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb12(%695: !exec.stop):  // 3 preds: ^bb9, ^bb13, ^bb14
      "runtime.release_transfer"(%687) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
      "cf.br"(%695)[^bb2] : (!exec.stop) -> ()
    ^bb13(%696: ui64):  // pred: ^bb9
      %697 = "runtime.transfer_values"(%687) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> !algebra.field_vector<"bls12-381.fr">
      %698 = "runtime.enter_scope"(%arg333, %686, %696, %697, %arg334, %arg335, %arg337, %675, %677) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 7>, site = "s14"}> : (!runtime.scope, i64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%698)[^bb14, ^bb12] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb14(%699: !runtime.scope):  // pred: ^bb13
      %700 = "func.call"(%699, %696, %697, %arg334, %arg335, %arg337, %675, %677) <{callee = @zkl_control_18}> : (!runtime.scope, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      %701 = "runtime.exit_scope"(%699, %700) : (!runtime.scope, !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>)>
      "exec.dispatch"(%701)[^bb15, ^bb12] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>)>) -> ()
    ^bb15(%702: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>):  // pred: ^bb14
      "runtime.release_transfer"(%687) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
      "cf.br"(%702)[^bb11] : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb16(%703: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb10
      %704 = "exec.returned"(%703) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%704) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7212h6c617965725f76616c756573", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_18", sym_visibility = "private"}> ({
    ^bb0(%arg325: !runtime.scope, %arg326: ui64, %arg327: !algebra.field_vector<"bls12-381.fr">, %arg328: !algebra.field_vector<"bls12-381.fr">, %arg329: !algebra.field_vector<"bls12-381.fr">, %arg330: ui64, %arg331: !algebra.field_vector<"bls12-381.fr">, %arg332: !algebra.field_vector<"bls12-381.fr">):
      %657 = "func.call"(%arg325, %arg328, %arg326, %arg330) <{callee = @zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e}> {runtime.site = "s15"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%657)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%658: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %659 = "func.call"(%arg325, %arg329, %arg326, %arg330) <{callee = @zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e}> {runtime.site = "s17"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%659)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%660: !exec.stop):  // 5 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5
      %661 = "exec.failed"(%660) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%661) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%662: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb1
      %663 = "exec.collect"(%arg325, %658, %662, %arg331, %arg332) <{body = @zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_body, domain = @zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_domain, site = "s19"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%663)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb4(%664: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb3
      %665 = "exec.apply"(%arg325, %664) <{binding = @zkl_binding_10, parameters = [], site = "s20"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%665)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb5(%666: !algebra.field<"bls12-381.fr">):  // pred: ^bb4
      %667 = "exec.apply"(%arg325, %arg327, %666) <{binding = @zkl_binding_9, parameters = [], site = "s21"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%667)[^bb6, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb6(%668: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb5
      %669 = "exec.complete"(%arg325, %668) : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%669) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, sym_name = "zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_domain", sym_visibility = "private"}> ({
    ^bb0(%arg321: !algebra.field_vector<"bls12-381.fr">, %arg322: !algebra.field_vector<"bls12-381.fr">, %arg323: !algebra.field_vector<"bls12-381.fr">, %arg324: !algebra.field_vector<"bls12-381.fr">):
      %650 = "data.domain_elements"(%arg321) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %651 = "data.domain_elements"(%arg322) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %652 = "data.domain_zip"(%650, %651) : (!data.domain<!algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      %653 = "data.domain_elements"(%arg323) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %654 = "data.domain_zip"(%652, %653) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      %655 = "data.domain_elements"(%arg324) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %656 = "data.domain_zip"(%654, %655) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%656) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_body", sym_visibility = "private"}> ({
    ^bb0(%arg312: !runtime.scope, %arg313: !algebra.field<"bls12-381.fr">, %arg314: !algebra.field<"bls12-381.fr">, %arg315: !algebra.field<"bls12-381.fr">, %arg316: !algebra.field<"bls12-381.fr">, %arg317: !algebra.field_vector<"bls12-381.fr">, %arg318: !algebra.field_vector<"bls12-381.fr">, %arg319: !algebra.field_vector<"bls12-381.fr">, %arg320: !algebra.field_vector<"bls12-381.fr">):
      %645 = "exec.compute"(%arg312, %arg313, %arg314, %arg315, %arg316) <{callee = @zkl_6b3d366572d1ba53650a202f39ff52a2f298a1591829443fbeaa34ef3974f084, site = "body"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%645)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%646: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %647 = "exec.returned"(%646) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%647) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%648: !exec.stop):  // pred: ^bb0
      %649 = "exec.failed"(%648) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%649) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_body", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_afd97de07c9ccae9db68186ebf66098aed7daffb4b11c598d0da5cd116df8490", sym_visibility = "private"}> ({
    ^bb0(%arg309: !runtime.scope, %arg310: !algebra.field_vector<"bls12-381.fr">, %arg311: ui64):
      %638 = "exec.apply"(%arg309) <{binding = @zkl_binding_8, parameters = [], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%638)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%639: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %640 = "func.call"(%arg309, %639, %arg311, %arg310) <{callee = @zkl_33e26704899171b0d3e366f86377dfc6602b55f53021ce20930f7ae9e8061294}> {runtime.site = "s2"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%640)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%641: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %642 = "exec.failed"(%641) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%642) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%643: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb1
      %644 = "exec.returned"(%643) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%644) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b729h7265706c6963617465", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_e7a7efcd14676d32c0e577ff1097f611a3dc84c74ecaa8bfdbebb25968971255", sym_visibility = "private"}> ({
    ^bb0(%arg305: !runtime.scope, %arg306: !algebra.field_vector<"bls12-381.fr">, %arg307: !algebra.field<"bls12-381.fr">, %arg308: ui64):
      %633 = "func.call"(%arg305, %arg306, %arg307, %arg308) <{callee = @zkl_fbd2531b804047766f8107241edd0ea81368b70795e44e4d8e07484d142783bb}> {runtime.site = "s2"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%633)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%634: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %635 = "exec.returned"(%634) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%635) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%636: !exec.stop):  // pred: ^bb0
      %637 = "exec.failed"(%636) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%637) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zks_99cdc30b104640f79094177f26387b3c04df24c083a5fa7125a3fd69fc1eb459", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_fbd2531b804047766f8107241edd0ea81368b70795e44e4d8e07484d142783bb", sym_visibility = "private"}> ({
    ^bb0(%arg301: !runtime.scope, %arg302: !algebra.field_vector<"bls12-381.fr">, %arg303: !algebra.field<"bls12-381.fr">, %arg304: ui64):
      %606 = "exec.apply"(%arg301) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s1"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%606)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%607: ui64):  // pred: ^bb0
      %608 = "exec.range"(%arg301, %607, %arg304) <{site = "s3"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%608)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i64, i64)>) -> ()
    ^bb2(%609: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb6, ^bb8
      %610 = "exec.failed"(%609) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%610) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%611: i64, %612: i64):  // pred: ^bb1
      %613 = "runtime.borrow_transfer"(%arg301, %arg302) : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>
      "cf.br"(%611, %613)[^bb4] : (i64, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb4(%614: i64, %615: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>):  // 2 preds: ^bb3, ^bb7
      %616 = "arith.cmpi"(%614, %612) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%616, %615)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb5:  // pred: ^bb4
      %617 = "runtime.iteration"(%arg301, %614) <{site = "s3"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%617)[^bb9, ^bb8] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb6(%618: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>):  // pred: ^bb4
      %619 = "runtime.accept_transfer"(%arg301, %618) : (!runtime.scope, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%619)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb7(%620: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>):  // pred: ^bb11
      %621 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %622 = "arith.addi"(%614, %621) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%622, %620)[^bb4] : (i64, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%623: !exec.stop):  // 3 preds: ^bb5, ^bb9, ^bb10
      "runtime.release_transfer"(%615) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
      "cf.br"(%623)[^bb2] : (!exec.stop) -> ()
    ^bb9(%624: ui64):  // pred: ^bb5
      %625 = "runtime.transfer_values"(%615) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> !algebra.field_vector<"bls12-381.fr">
      %626 = "runtime.enter_scope"(%arg301, %614, %624, %625, %arg303) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 3>, site = "s3"}> : (!runtime.scope, i64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%626)[^bb10, ^bb8] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb10(%627: !runtime.scope):  // pred: ^bb9
      %628 = "func.call"(%627, %624, %625, %arg303) <{callee = @zkl_control_19}> : (!runtime.scope, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      %629 = "runtime.exit_scope"(%627, %628) : (!runtime.scope, !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>)>
      "exec.dispatch"(%629)[^bb11, ^bb8] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>)>) -> ()
    ^bb11(%630: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>):  // pred: ^bb10
      "runtime.release_transfer"(%615) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
      "cf.br"(%630)[^bb7] : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb12(%631: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb6
      %632 = "exec.returned"(%631) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%632) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7212h7265706561745f76616c7565", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_19", sym_visibility = "private"}> ({
    ^bb0(%arg297: !runtime.scope, %arg298: ui64, %arg299: !algebra.field_vector<"bls12-381.fr">, %arg300: !algebra.field<"bls12-381.fr">):
      %601 = "exec.apply"(%arg297, %arg299, %arg300) <{binding = @zkl_binding_9, parameters = [], site = "s4"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%601)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%602: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %603 = "exec.complete"(%arg297, %602) : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%603) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%604: !exec.stop):  // pred: ^bb0
      %605 = "exec.failed"(%604) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%605) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_33e26704899171b0d3e366f86377dfc6602b55f53021ce20930f7ae9e8061294", sym_visibility = "private"}> ({
    ^bb0(%arg293: !runtime.scope, %arg294: !algebra.field_vector<"bls12-381.fr">, %arg295: ui64, %arg296: !algebra.field_vector<"bls12-381.fr">):
      %596 = "exec.fold"(%arg293, %arg296, %arg294, %arg295) <{domain = @finite_zkl_33e26704899171b0d3e366f86377dfc6602b55f53021ce20930f7ae9e8061294_s0_domain, site = "s0", step = @finite_zkl_33e26704899171b0d3e366f86377dfc6602b55f53021ce20930f7ae9e8061294_s0_body}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%596)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%597: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %598 = "exec.returned"(%597) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%598) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%599: !exec.stop):  // pred: ^bb0
      %600 = "exec.failed"(%599) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%600) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_33e26704899171b0d3e366f86377dfc6602b55f53021ce20930f7ae9e8061294_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg292: !algebra.field_vector<"bls12-381.fr">):
      %595 = "data.domain_elements"(%arg292) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%595) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "finite_zkl_33e26704899171b0d3e366f86377dfc6602b55f53021ce20930f7ae9e8061294_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg287: !runtime.scope, %arg288: !algebra.field_vector<"bls12-381.fr">, %arg289: !algebra.field<"bls12-381.fr">, %arg290: !algebra.field_vector<"bls12-381.fr">, %arg291: ui64):
      %590 = "func.call"(%arg287, %arg288, %arg289, %arg291) <{callee = @zkl_e7a7efcd14676d32c0e577ff1097f611a3dc84c74ecaa8bfdbebb25968971255}> {runtime.site = "body"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%590)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%591: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %592 = "exec.returned"(%591) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%592) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%593: !exec.stop):  // pred: ^bb0
      %594 = "exec.failed"(%593) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%594) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["finite_zkl_33e26704899171b0d3e366f86377dfc6602b55f53021ce20930f7ae9e8061294_s0_body", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_33f3047479634e63ecd16a0855f88ad8af019c37d677a4ffe6f5bacc63307947", sym_visibility = "private"}> ({
    ^bb0(%arg284: !runtime.scope, %arg285: !algebra.field_vector<"bls12-381.fr">, %arg286: ui64):
      %561 = "exec.apply"(%arg284) <{binding = @zkl_binding_8, parameters = [], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%561)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%562: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %563 = "exec.apply"(%arg284) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s2"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%563)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%564: !exec.stop):  // 5 preds: ^bb0, ^bb1, ^bb3, ^bb7, ^bb9
      %565 = "exec.failed"(%564) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%565) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%566: ui64):  // pred: ^bb1
      %567 = "exec.range"(%arg284, %566, %arg286) <{site = "s4"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%567)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i64, i64)>) -> ()
    ^bb4(%568: i64, %569: i64):  // pred: ^bb3
      %570 = "runtime.borrow_transfer"(%arg284, %562) : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>
      "cf.br"(%568, %570)[^bb5] : (i64, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb5(%571: i64, %572: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>):  // 2 preds: ^bb4, ^bb8
      %573 = "arith.cmpi"(%571, %569) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%573, %572)[^bb6, ^bb7] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb6:  // pred: ^bb5
      %574 = "runtime.iteration"(%arg284, %571) <{site = "s4"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%574)[^bb10, ^bb9] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb7(%575: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>):  // pred: ^bb5
      %576 = "runtime.accept_transfer"(%arg284, %575) : (!runtime.scope, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%576)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%577: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>):  // pred: ^bb12
      %578 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %579 = "arith.addi"(%571, %578) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%579, %577)[^bb5] : (i64, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb9(%580: !exec.stop):  // 3 preds: ^bb6, ^bb10, ^bb11
      "runtime.release_transfer"(%572) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
      "cf.br"(%580)[^bb2] : (!exec.stop) -> ()
    ^bb10(%581: ui64):  // pred: ^bb6
      %582 = "runtime.transfer_values"(%572) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> !algebra.field_vector<"bls12-381.fr">
      %583 = "runtime.enter_scope"(%arg284, %571, %581, %582, %arg285) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 3>, site = "s4"}> : (!runtime.scope, i64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%583)[^bb11, ^bb9] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb11(%584: !runtime.scope):  // pred: ^bb10
      %585 = "func.call"(%584, %581, %582, %arg285) <{callee = @zkl_control_20}> : (!runtime.scope, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      %586 = "runtime.exit_scope"(%584, %585) : (!runtime.scope, !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>)>
      "exec.dispatch"(%586)[^bb12, ^bb9] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>)>) -> ()
    ^bb12(%587: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>):  // pred: ^bb11
      "runtime.release_transfer"(%572) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
      "cf.br"(%587)[^bb8] : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb13(%588: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb7
      %589 = "exec.returned"(%588) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%589) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b724h74696c65", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_20", sym_visibility = "private"}> ({
    ^bb0(%arg280: !runtime.scope, %arg281: ui64, %arg282: !algebra.field_vector<"bls12-381.fr">, %arg283: !algebra.field_vector<"bls12-381.fr">):
      %556 = "func.call"(%arg280, %arg282, %arg283) <{callee = @zkl_5939bc7a1ddcd11f8e2153f23b3ed89c16434b9b99db1512543ee10e7b59b248}> {runtime.site = "s5"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%556)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%557: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %558 = "exec.complete"(%arg280, %557) : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%558) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%559: !exec.stop):  // pred: ^bb0
      %560 = "exec.failed"(%559) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%560) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_ac1d3513b06c1d4950d126f678b9482e4ca13944fc4b35442d1a33796d064b0c", sym_visibility = "private"}> ({
    ^bb0(%arg277: !runtime.scope, %arg278: !algebra.field_vector<"bls12-381.fr">, %arg279: !algebra.field<"bls12-381.fr">):
      %551 = "exec.apply"(%arg277, %arg278, %arg279) <{binding = @zkl_binding_9, parameters = [], site = "s2"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%551)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%552: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %553 = "exec.returned"(%552) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%553) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%554: !exec.stop):  // pred: ^bb0
      %555 = "exec.failed"(%554) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%555) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zks_42e44eec4fd7419218a6cf70cf462d528dfc3e199764475009d12bc09d4ada97", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_5939bc7a1ddcd11f8e2153f23b3ed89c16434b9b99db1512543ee10e7b59b248", sym_visibility = "private"}> ({
    ^bb0(%arg274: !runtime.scope, %arg275: !algebra.field_vector<"bls12-381.fr">, %arg276: !algebra.field_vector<"bls12-381.fr">):
      %546 = "exec.fold"(%arg274, %arg276, %arg275) <{domain = @finite_zkl_5939bc7a1ddcd11f8e2153f23b3ed89c16434b9b99db1512543ee10e7b59b248_s0_domain, site = "s0", step = @finite_zkl_5939bc7a1ddcd11f8e2153f23b3ed89c16434b9b99db1512543ee10e7b59b248_s0_body}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%546)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%547: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %548 = "exec.returned"(%547) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%548) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%549: !exec.stop):  // pred: ^bb0
      %550 = "exec.failed"(%549) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%550) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_5939bc7a1ddcd11f8e2153f23b3ed89c16434b9b99db1512543ee10e7b59b248_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg273: !algebra.field_vector<"bls12-381.fr">):
      %545 = "data.domain_elements"(%arg273) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%545) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "finite_zkl_5939bc7a1ddcd11f8e2153f23b3ed89c16434b9b99db1512543ee10e7b59b248_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg269: !runtime.scope, %arg270: !algebra.field_vector<"bls12-381.fr">, %arg271: !algebra.field<"bls12-381.fr">, %arg272: !algebra.field_vector<"bls12-381.fr">):
      %540 = "func.call"(%arg269, %arg270, %arg271) <{callee = @zkl_ac1d3513b06c1d4950d126f678b9482e4ca13944fc4b35442d1a33796d064b0c}> {runtime.site = "body"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%540)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%541: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %542 = "exec.returned"(%541) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%542) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%543: !exec.stop):  // pred: ^bb0
      %544 = "exec.failed"(%543) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%544) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["finite_zkl_5939bc7a1ddcd11f8e2153f23b3ed89c16434b9b99db1512543ee10e7b59b248_s0_body", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_6b3d366572d1ba53650a202f39ff52a2f298a1591829443fbeaa34ef3974f084", sym_visibility = "private"}> ({
    ^bb0(%arg265: !algebra.field<"bls12-381.fr">, %arg266: !algebra.field<"bls12-381.fr">, %arg267: !algebra.field<"bls12-381.fr">, %arg268: !algebra.field<"bls12-381.fr">):
      %535 = "algebra.field_add"(%arg267, %arg268) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %536 = "algebra.field_multiply"(%arg265, %535) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %537 = "algebra.field_multiply"(%arg266, %arg267) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %538 = "algebra.field_multiply"(%537, %arg268) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %539 = "algebra.field_add"(%536, %538) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%539) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_d1f2756b99b17aad26e4b85a966eec4c9419609618b22e3ee7f8a3349cb1e33b", sym_visibility = "private"}> ({
    ^bb0(%arg259: !runtime.scope, %arg260: !algebra.field_vector<"bls12-381.fr">, %arg261: !algebra.field_vector<"bls12-381.fr">, %arg262: !algebra.field_vector<"bls12-381.fr">, %arg263: !algebra.field_vector<"bls12-381.fr">, %arg264: ui64):
      %516 = "func.call"(%arg259, %arg264) <{callee = @s3h676b7212h706f7765725f6f665f74776f}> {runtime.site = "s0"} : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%516)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%517: ui64):  // pred: ^bb0
      %518 = "exec.apply"(%arg259, %arg262) <{binding = @zkl_binding_2, parameters = [], site = "s2"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%518)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%519: !exec.stop):  // 8 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb8
      %520 = "exec.failed"(%519) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%520) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%521: ui64):  // pred: ^bb1
      %522 = "exec.apply"(%arg259, %521, %arg264) <{binding = @zkl_binding_7, parameters = [], site = "s3"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%522)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%523: ui64):  // pred: ^bb3
      %524 = "exec.apply"(%arg259, %523, %arg264) <{binding = @zkl_binding_7, parameters = [], site = "s4"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%524)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%525: ui64):  // pred: ^bb4
      %526 = "func.call"(%arg259, %arg260, %525, %arg262) <{callee = @zkl_b16c159516733e0a19ce242015622636ee99dc6084d8c851dfb43c25cee57b59}> {runtime.site = "s6"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%526)[^bb6, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb6(%527: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb5
      %528 = "func.call"(%arg259, %arg261, %525, %arg262) <{callee = @zkl_b16c159516733e0a19ce242015622636ee99dc6084d8c851dfb43c25cee57b59}> {runtime.site = "s7"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%528)[^bb7, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb7(%529: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb6
      %530 = "func.call"(%arg259, %arg263, %517) <{callee = @zkl_afd97de07c9ccae9db68186ebf66098aed7daffb4b11c598d0da5cd116df8490}> {runtime.site = "s8"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%530)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%531: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb7
      %532 = "func.call"(%arg259, %arg263, %517) <{callee = @zkl_33f3047479634e63ecd16a0855f88ad8af019c37d677a4ffe6f5bacc63307947}> {runtime.site = "s9"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%532)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb9(%533: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb8
      %534 = "exec.returned"(%527, %529, %531, %533) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%534) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7211h6c617965725f6761746573", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_b16c159516733e0a19ce242015622636ee99dc6084d8c851dfb43c25cee57b59", sym_visibility = "private"}> ({
    ^bb0(%arg255: !runtime.scope, %arg256: !algebra.field_vector<"bls12-381.fr">, %arg257: ui64, %arg258: !algebra.field_vector<"bls12-381.fr">):
      %501 = "exec.apply"(%arg255) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%501)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%502: ui64):  // pred: ^bb0
      %503 = "func.call"(%arg255, %arg256, %arg257, %502) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a}> {runtime.site = "s1"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%503)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb2(%504: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %505 = "exec.failed"(%504) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%505) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%506: !algebra.field_vector<"bls12-381.fr">, %507: ui64, %508: ui64):  // pred: ^bb1
      %509 = "func.call"(%arg255, %506, %507, %508, %arg258) <{callee = @zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be}> {runtime.site = "s2"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%509)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb4(%510: !algebra.field_vector<"bls12-381.fr">, %511: ui64, %512: ui64):  // pred: ^bb3
      %513 = "exec.compute"(%arg255, %510, %511, %512) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33, site = "s3"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%513)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb5(%514: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb4
      %515 = "exec.returned"(%514) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%515) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b728h7265737472696374", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_e1405e1bb4604e60f337203132c746492bf7c31b55302426ae19c2c021c2da1a", sym_visibility = "private"}> ({
    ^bb0(%arg253: !runtime.scope, %arg254: !algebra.field<"bls12-381.fr">):
      %496 = "exec.apply"(%arg253) <{binding = @zkl_binding_8, parameters = [], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%496)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%497: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %498 = "exec.returned"(%497, %arg254) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%498) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%499: !exec.stop):  // pred: ^bb0
      %500 = "exec.failed"(%499) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%500) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b727h70656e64696e67", []]} : () -> ()
    "protocol.func"() <{contracts = [["input", "shape", [@zkl_30326558223483c2b755cae1fef2fb9e26e5ee8894b87d6977fe6482997b20fd, [["input", 0, "role00000000"], ["input", 1, "role00000000"], ["input", 2, "role00000000"], ["input", 3, "role00000000"]]], unit, unit], ["continuation", "gate_sum", [@zkl_e276fa0fd61d1145b2034d7e5681d41484daeb4a120f83771eba638587b04670, [["input", 0, "role00000000"], ["input", 1, "role00000000"], ["input", 2, "role00000000"], ["input", 3, "role00000000"], ["input", 4, "role00000001"], ["input", 5, "role00000001"]]], [@zkl_e276fa0fd61d1145b2034d7e5681d41484daeb4a120f83771eba638587b04670, [["input", 0, "role00000000"], ["input", 1, "role00000000"], ["input", 2, "role00000000"], ["input", 3, "role00000000"], ["output", 5, "role00000001"], ["output", 6, "role00000001"]]], unit]], function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), input_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"], ["role00000000", "role00000001"], ["role00000001"]], origin = ["gkr::Rounds", [["F", ["field", "bls12-381.fr"]], ["Max", ["nat", "4"]]]], output_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba"}> ({
    ^bb0(%arg236: !algebra.field_vector<"bls12-381.fr">, %arg237: !algebra.field_vector<"bls12-381.fr">, %arg238: !algebra.field_vector<"bls12-381.fr">, %arg239: !algebra.field_vector<"bls12-381.fr">, %arg240: !algebra.field_vector<"bls12-381.fr">, %arg241: !algebra.field<"bls12-381.fr">, %arg242: ui64, %arg243: !protocol.service_ref<"random.bls12-381.fr/0">):
      %471 = "protocol.local_call"() <{callee = @zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f, role = "role00000000", site = "s1"}> : () -> !algebra.field_vector<"bls12-381.fr">
      %472:2 = "protocol.local_call"(%arg240, %arg241) <{callee = @zkl_bd4f0d76e787de675c5732a4a96fc396d45486f32b3dcda5182ccc324969c825, role = "role00000001", site = "s3"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %473:7 = "protocol.repeat"(%arg242, %arg236, %arg237, %arg238, %arg239, %471, %472#0, %472#1, %arg243) <{carried = 7 : i64, carried_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"]], maximum = 4 : i64, roles = ["role00000000", "role00000001"], site = "s9"}> ({
      ^bb0(%arg244: ui64, %arg245: !algebra.field_vector<"bls12-381.fr">, %arg246: !algebra.field_vector<"bls12-381.fr">, %arg247: !algebra.field_vector<"bls12-381.fr">, %arg248: !algebra.field_vector<"bls12-381.fr">, %arg249: !algebra.field_vector<"bls12-381.fr">, %arg250: !algebra.field_vector<"bls12-381.fr">, %arg251: !algebra.field<"bls12-381.fr">, %arg252: !protocol.service_ref<"random.bls12-381.fr/0">):
        %475:3 = "protocol.local_call"(%arg245, %arg246, %arg247, %arg248) <{callee = @zkl_e2f65d17b480da5da0270346faa1bd036c7a5f879e30f4b2b6bac1224b05e394, role = "role00000000", site = "s10"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %476 = "protocol.exchange"(%475#0) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %477 = "protocol.restrict_roles"(%476) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %478 = "protocol.exchange"(%475#1) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_1"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %479 = "protocol.restrict_roles"(%478) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %480 = "protocol.exchange"(%475#2) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_2"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %481 = "protocol.restrict_roles"(%480) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %482 = "algebra.field_add"(%477, %477) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %483 = "algebra.field_add"(%482, %479) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %484 = "algebra.field_add"(%483, %481) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %485 = "algebra.field_equal"(%arg251, %484) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
        "protocol.guard"(%485) <{owner = "role00000001", site = "s21"}> : (i1) -> ()
        %486 = "protocol.query"(%arg252) <{method = "draw", owner = "role00000001", site = "label_6368616c6c656e6765"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
        %487 = "protocol.exchange"(%486) <{receiver = "role00000000", sender = "role00000001", site = "label_64656c6976657279_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %488 = "protocol.restrict_roles"(%487) <{roles = ["role00000000"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %489:4 = "protocol.local_call"(%arg245, %arg246, %arg247, %arg248, %488) <{callee = @zkl_36caebca415236dd6aac1763c9a581b89c25a00e62432b484ec92ae08e6a0099, role = "role00000000", site = "s26"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)
        %490 = "protocol.local_call"(%arg249, %488) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000000", site = "s28"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
        %491 = "protocol.local_call"(%arg250, %486) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000001", site = "s30"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
        %492 = "algebra.field_multiply"(%486, %481) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %493 = "algebra.field_add"(%479, %492) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %494 = "algebra.field_multiply"(%486, %493) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %495 = "algebra.field_add"(%477, %494) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        "protocol.yield"(%489#0, %489#1, %489#2, %489#3, %490, %491, %495) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
      }) : (ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %474:2 = "protocol.local_call"(%473#5, %473#6) <{callee = @zkl_bcddf8825098d44ae9ce732a7b45754c16637e2a47a4c9f29ef9a21612daeaa3, role = "role00000001", site = "s42"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      "protocol.return"(%473#4, %473#0, %473#1, %473#2, %473#3, %474#0, %474#1) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> i1, sym_name = "zkf_029bdd6bcc5b1485783f1674f8c6e15543fd2d268649f211eab729158162c828", sym_visibility = "private"}> ({
    ^bb0(%arg232: !algebra.field_vector<"bls12-381.fr">, %arg233: !algebra.field_vector<"bls12-381.fr">, %arg234: !algebra.field_vector<"bls12-381.fr">, %arg235: !algebra.field_vector<"bls12-381.fr">):
      %460 = "data.dim"(%arg232) <{axis = 0 : i64}> : (!algebra.field_vector<"bls12-381.fr">) -> ui64
      %461 = "data.dim"(%arg233) <{axis = 0 : i64}> : (!algebra.field_vector<"bls12-381.fr">) -> ui64
      %462 = "data.index_equal"(%460, %461) : (ui64, ui64) -> i1
      %463 = "data.dim"(%arg232) <{axis = 0 : i64}> : (!algebra.field_vector<"bls12-381.fr">) -> ui64
      %464 = "data.dim"(%arg234) <{axis = 0 : i64}> : (!algebra.field_vector<"bls12-381.fr">) -> ui64
      %465 = "data.index_equal"(%463, %464) : (ui64, ui64) -> i1
      %466 = "arith.andi"(%462, %465) : (i1, i1) -> i1
      %467 = "data.dim"(%arg232) <{axis = 0 : i64}> : (!algebra.field_vector<"bls12-381.fr">) -> ui64
      %468 = "data.dim"(%arg235) <{axis = 0 : i64}> : (!algebra.field_vector<"bls12-381.fr">) -> ui64
      %469 = "data.index_equal"(%467, %468) : (ui64, ui64) -> i1
      %470 = "arith.andi"(%466, %469) : (i1, i1) -> i1
      "func.return"(%470) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_bd4f0d76e787de675c5732a4a96fc396d45486f32b3dcda5182ccc324969c825", sym_visibility = "private"}> ({
    ^bb0(%arg229: !runtime.scope, %arg230: !algebra.field_vector<"bls12-381.fr">, %arg231: !algebra.field<"bls12-381.fr">):
      %459 = "exec.returned"(%arg230, %arg231) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%459) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7211h6f70656e5f726f756e6473", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_e2f65d17b480da5da0270346faa1bd036c7a5f879e30f4b2b6bac1224b05e394", sym_visibility = "private"}> ({
    ^bb0(%arg224: !runtime.scope, %arg225: !algebra.field_vector<"bls12-381.fr">, %arg226: !algebra.field_vector<"bls12-381.fr">, %arg227: !algebra.field_vector<"bls12-381.fr">, %arg228: !algebra.field_vector<"bls12-381.fr">):
      %430 = "exec.apply"(%arg224, %arg225) <{binding = @zkl_binding_12, parameters = [], site = "s1"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%430)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%431: !algebra.field_vector<"bls12-381.fr">, %432: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %433 = "exec.apply"(%arg224, %arg226) <{binding = @zkl_binding_12, parameters = [], site = "s4"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%433)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%434: !exec.stop):  // 11 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb10, ^bb11
      %435 = "exec.failed"(%434) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%435) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb3(%436: !algebra.field_vector<"bls12-381.fr">, %437: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb1
      %438 = "exec.apply"(%arg224, %arg227) <{binding = @zkl_binding_12, parameters = [], site = "s7"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%438)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb4(%439: !algebra.field_vector<"bls12-381.fr">, %440: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb3
      %441 = "exec.apply"(%arg224, %arg228) <{binding = @zkl_binding_12, parameters = [], site = "s10"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%441)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb5(%442: !algebra.field_vector<"bls12-381.fr">, %443: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb4
      %444 = "exec.collect"(%arg224, %431, %436, %439, %442) <{body = @zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_body, domain = @zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_domain, site = "s16"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%444)[^bb6, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb6(%445: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb5
      %446 = "exec.apply"(%arg224, %445) <{binding = @zkl_binding_10, parameters = [], site = "s17"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%446)[^bb7, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb7(%447: !algebra.field<"bls12-381.fr">):  // pred: ^bb6
      %448 = "exec.collect"(%arg224, %432, %437, %440, %443) <{body = @zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_body, domain = @zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_domain, site = "s23"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%448)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%449: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb7
      %450 = "exec.apply"(%arg224, %449) <{binding = @zkl_binding_10, parameters = [], site = "s24"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%450)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb9(%451: !algebra.field<"bls12-381.fr">):  // pred: ^bb8
      %452 = "exec.collect"(%arg224, %431, %432, %436, %437, %439, %440, %442, %443) <{body = @zkl_map_b02c6bec831af4d953cc5d5558b1dfebb2f6666e509fde68f0a09745680b6577_body, domain = @zkl_map_b02c6bec831af4d953cc5d5558b1dfebb2f6666e509fde68f0a09745680b6577_domain, site = "s34"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%452)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb10(%453: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb9
      %454 = "exec.apply"(%arg224, %453) <{binding = @zkl_binding_10, parameters = [], site = "s35"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%454)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb11(%455: !algebra.field<"bls12-381.fr">):  // pred: ^bb10
      %456 = "exec.compute"(%arg224, %447, %451, %455) <{callee = @zkl_ae0ec2b882ea51d896368927e811be493e3af32def2e5ada1525e385646e6229, site = "s37"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%456)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb12(%457: !algebra.field<"bls12-381.fr">):  // pred: ^bb11
      %458 = "exec.returned"(%447, %457, %455) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%458) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7213h726f756e645f6d657373616765", []]} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, sym_name = "zkl_map_b02c6bec831af4d953cc5d5558b1dfebb2f6666e509fde68f0a09745680b6577_domain", sym_visibility = "private"}> ({
    ^bb0(%arg216: !algebra.field_vector<"bls12-381.fr">, %arg217: !algebra.field_vector<"bls12-381.fr">, %arg218: !algebra.field_vector<"bls12-381.fr">, %arg219: !algebra.field_vector<"bls12-381.fr">, %arg220: !algebra.field_vector<"bls12-381.fr">, %arg221: !algebra.field_vector<"bls12-381.fr">, %arg222: !algebra.field_vector<"bls12-381.fr">, %arg223: !algebra.field_vector<"bls12-381.fr">):
      %415 = "data.domain_elements"(%arg216) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %416 = "data.domain_elements"(%arg217) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %417 = "data.domain_zip"(%415, %416) : (!data.domain<!algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      %418 = "data.domain_elements"(%arg218) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %419 = "data.domain_zip"(%417, %418) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      %420 = "data.domain_elements"(%arg219) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %421 = "data.domain_zip"(%419, %420) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      %422 = "data.domain_elements"(%arg220) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %423 = "data.domain_zip"(%421, %422) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      %424 = "data.domain_elements"(%arg221) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %425 = "data.domain_zip"(%423, %424) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      %426 = "data.domain_elements"(%arg222) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %427 = "data.domain_zip"(%425, %426) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      %428 = "data.domain_elements"(%arg223) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %429 = "data.domain_zip"(%427, %428) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%429) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_map_b02c6bec831af4d953cc5d5558b1dfebb2f6666e509fde68f0a09745680b6577_body", sym_visibility = "private"}> ({
    ^bb0(%arg199: !runtime.scope, %arg200: !algebra.field<"bls12-381.fr">, %arg201: !algebra.field<"bls12-381.fr">, %arg202: !algebra.field<"bls12-381.fr">, %arg203: !algebra.field<"bls12-381.fr">, %arg204: !algebra.field<"bls12-381.fr">, %arg205: !algebra.field<"bls12-381.fr">, %arg206: !algebra.field<"bls12-381.fr">, %arg207: !algebra.field<"bls12-381.fr">, %arg208: !algebra.field_vector<"bls12-381.fr">, %arg209: !algebra.field_vector<"bls12-381.fr">, %arg210: !algebra.field_vector<"bls12-381.fr">, %arg211: !algebra.field_vector<"bls12-381.fr">, %arg212: !algebra.field_vector<"bls12-381.fr">, %arg213: !algebra.field_vector<"bls12-381.fr">, %arg214: !algebra.field_vector<"bls12-381.fr">, %arg215: !algebra.field_vector<"bls12-381.fr">):
      %410 = "exec.compute"(%arg199, %arg200, %arg201, %arg202, %arg203, %arg204, %arg205, %arg206, %arg207) <{callee = @zkl_f5e0b2f9a4003d8d806a7a288580cf1f30d07d383f870564beff948ccf011d6b, site = "body"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%410)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%411: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %412 = "exec.returned"(%411) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%412) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%413: !exec.stop):  // pred: ^bb0
      %414 = "exec.failed"(%413) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%414) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zkl_map_b02c6bec831af4d953cc5d5558b1dfebb2f6666e509fde68f0a09745680b6577_body", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_f5e0b2f9a4003d8d806a7a288580cf1f30d07d383f870564beff948ccf011d6b", sym_visibility = "private"}> ({
    ^bb0(%arg191: !algebra.field<"bls12-381.fr">, %arg192: !algebra.field<"bls12-381.fr">, %arg193: !algebra.field<"bls12-381.fr">, %arg194: !algebra.field<"bls12-381.fr">, %arg195: !algebra.field<"bls12-381.fr">, %arg196: !algebra.field<"bls12-381.fr">, %arg197: !algebra.field<"bls12-381.fr">, %arg198: !algebra.field<"bls12-381.fr">):
      %396 = "algebra.field_subtract"(%arg192, %arg191) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %397 = "algebra.field_subtract"(%arg194, %arg193) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %398 = "algebra.field_subtract"(%arg196, %arg195) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %399 = "algebra.field_subtract"(%arg198, %arg197) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %400 = "algebra.field_add"(%398, %399) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %401 = "algebra.field_multiply"(%396, %400) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %402 = "algebra.field_multiply"(%398, %arg197) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %403 = "algebra.field_multiply"(%arg195, %399) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %404 = "algebra.field_add"(%402, %403) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %405 = "algebra.field_multiply"(%397, %404) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %406 = "algebra.field_add"(%401, %405) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %407 = "algebra.field_multiply"(%arg193, %398) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %408 = "algebra.field_multiply"(%407, %399) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %409 = "algebra.field_add"(%406, %408) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%409) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_ae0ec2b882ea51d896368927e811be493e3af32def2e5ada1525e385646e6229", sym_visibility = "private"}> ({
    ^bb0(%arg188: !algebra.field<"bls12-381.fr">, %arg189: !algebra.field<"bls12-381.fr">, %arg190: !algebra.field<"bls12-381.fr">):
      %394 = "algebra.field_subtract"(%arg189, %arg188) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %395 = "algebra.field_subtract"(%394, %arg190) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%395) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_36caebca415236dd6aac1763c9a581b89c25a00e62432b484ec92ae08e6a0099", sym_visibility = "private"}> ({
    ^bb0(%arg182: !runtime.scope, %arg183: !algebra.field_vector<"bls12-381.fr">, %arg184: !algebra.field_vector<"bls12-381.fr">, %arg185: !algebra.field_vector<"bls12-381.fr">, %arg186: !algebra.field_vector<"bls12-381.fr">, %arg187: !algebra.field<"bls12-381.fr">):
      %383 = "func.call"(%arg182, %arg183, %arg187) <{callee = @zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac}> {runtime.site = "s1"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%383)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%384: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %385 = "func.call"(%arg182, %arg184, %arg187) <{callee = @zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac}> {runtime.site = "s3"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%385)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%386: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %387 = "exec.failed"(%386) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%387) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%388: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb1
      %389 = "func.call"(%arg182, %arg185, %arg187) <{callee = @zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac}> {runtime.site = "s5"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%389)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb4(%390: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb3
      %391 = "func.call"(%arg182, %arg186, %arg187) <{callee = @zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac}> {runtime.site = "s7"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%391)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb5(%392: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb4
      %393 = "exec.returned"(%384, %388, %390, %392) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%393) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b729h6669785f6761746573", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac", sym_visibility = "private"}> ({
    ^bb0(%arg179: !runtime.scope, %arg180: !algebra.field_vector<"bls12-381.fr">, %arg181: !algebra.field<"bls12-381.fr">):
      %375 = "exec.apply"(%arg179, %arg180) <{binding = @zkl_binding_12, parameters = [], site = "s0"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%375)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%376: !algebra.field_vector<"bls12-381.fr">, %377: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %378 = "exec.collect"(%arg179, %376, %377, %arg181) <{body = @zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_body, domain = @zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_domain, site = "s4"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%378)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%379: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %380 = "exec.failed"(%379) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%380) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%381: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb1
      %382 = "exec.returned"(%381) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%382) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b723h666978", []]} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, sym_name = "zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_domain", sym_visibility = "private"}> ({
    ^bb0(%arg177: !algebra.field_vector<"bls12-381.fr">, %arg178: !algebra.field_vector<"bls12-381.fr">):
      %372 = "data.domain_elements"(%arg177) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %373 = "data.domain_elements"(%arg178) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %374 = "data.domain_zip"(%372, %373) : (!data.domain<!algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%374) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_body", sym_visibility = "private"}> ({
    ^bb0(%arg171: !runtime.scope, %arg172: !algebra.field<"bls12-381.fr">, %arg173: !algebra.field<"bls12-381.fr">, %arg174: !algebra.field_vector<"bls12-381.fr">, %arg175: !algebra.field_vector<"bls12-381.fr">, %arg176: !algebra.field<"bls12-381.fr">):
      %367 = "exec.compute"(%arg171, %arg172, %arg173, %arg176) <{callee = @zkl_9de40b3e39acd7da53c8d9f1ec759779b60f4d0d3b7314f8741f798f050dbfd1, site = "body"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%367)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%368: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %369 = "exec.returned"(%368) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%369) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%370: !exec.stop):  // pred: ^bb0
      %371 = "exec.failed"(%370) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%371) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_body", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_9de40b3e39acd7da53c8d9f1ec759779b60f4d0d3b7314f8741f798f050dbfd1", sym_visibility = "private"}> ({
    ^bb0(%arg168: !algebra.field<"bls12-381.fr">, %arg169: !algebra.field<"bls12-381.fr">, %arg170: !algebra.field<"bls12-381.fr">):
      %364 = "algebra.field_subtract"(%arg169, %arg168) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %365 = "algebra.field_multiply"(%364, %arg170) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %366 = "algebra.field_add"(%arg168, %365) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%366) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_bcddf8825098d44ae9ce732a7b45754c16637e2a47a4c9f29ef9a21612daeaa3", sym_visibility = "private"}> ({
    ^bb0(%arg165: !runtime.scope, %arg166: !algebra.field_vector<"bls12-381.fr">, %arg167: !algebra.field<"bls12-381.fr">):
      %363 = "exec.returned"(%arg166, %arg167) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%363) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b729h61745f707265666978", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_cfcf40daaab145a916368cf7a01eccd9ba0e536fbbc30a06c4a25e7ec96ecbe7", sym_visibility = "private"}> ({
    ^bb0(%arg163: !runtime.scope, %arg164: !algebra.field_vector<"bls12-381.fr">):
      %334 = "exec.apply"(%arg163, %arg164) <{binding = @zkl_binding_2, parameters = [], site = "s0"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%334)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%335: ui64):  // pred: ^bb0
      %336 = "exec.apply"(%arg163) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s1"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%336)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%337: !exec.stop):  // 10 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb6, ^bb7, ^bb9, ^bb10, ^bb12, ^bb13
      %338 = "exec.failed"(%337) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%338) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%339: ui64):  // pred: ^bb1
      %340 = "exec.apply"(%arg163, %335, %339) <{binding = @zkl_binding_4, parameters = [], site = "s2"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%340)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb4(%341: i1):  // pred: ^bb3
      %342 = "exec.test"(%arg163, %341) <{site = "s4"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%342)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb5(%343: i1):  // pred: ^bb4
      "cf.cond_br"(%343)[^bb6, ^bb7] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb6:  // pred: ^bb5
      %344 = "runtime.enter_scope"(%arg163, %arg164) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "then", site = "s4"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%344)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // pred: ^bb5
      %345 = "runtime.enter_scope"(%arg163, %arg164) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "else", site = "s4"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%345)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb8(%346: !algebra.field_vector<"bls12-381.fr">, %347: !algebra.field_vector<"bls12-381.fr">):  // 2 preds: ^bb11, ^bb14
      %348 = "exec.returned"(%346, %347) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%348) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb9(%349: !runtime.scope):  // pred: ^bb6
      %350 = "func.call"(%349, %arg164) <{callee = @zkl_control_21}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      %351 = "runtime.exit_scope"(%349, %350) : (!runtime.scope, !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>)>
      "exec.dispatch"(%351)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>)>) -> ()
    ^bb10(%352: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>):  // pred: ^bb9
      %353 = "runtime.accept_transfer"(%arg163, %352) : (!runtime.scope, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%353)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb11(%354: !algebra.field_vector<"bls12-381.fr">, %355: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb10
      "cf.br"(%354, %355)[^bb8] : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> ()
    ^bb12(%356: !runtime.scope):  // pred: ^bb7
      %357 = "func.call"(%356, %arg164) <{callee = @zkl_control_22}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      %358 = "runtime.exit_scope"(%356, %357) : (!runtime.scope, !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>)>
      "exec.dispatch"(%358)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>)>) -> ()
    ^bb13(%359: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>):  // pred: ^bb12
      %360 = "runtime.accept_transfer"(%arg163, %359) : (!runtime.scope, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%360)[^bb14, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb14(%361: !algebra.field_vector<"bls12-381.fr">, %362: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb13
      "cf.br"(%361, %362)[^bb8] : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> ()
    }) {runtime.origin = ["s3h676b7211h73706c69745f706f696e74", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_21", sym_visibility = "private"}> ({
    ^bb0(%arg161: !runtime.scope, %arg162: !algebra.field_vector<"bls12-381.fr">):
      %333 = "exec.complete"(%arg161, %arg162, %arg162) : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%333) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_22", sym_visibility = "private"}> ({
    ^bb0(%arg159: !runtime.scope, %arg160: !algebra.field_vector<"bls12-381.fr">):
      %327 = "exec.apply"(%arg159, %arg160) <{binding = @zkl_binding_12, parameters = [], site = "s7"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%327)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%328: !algebra.field_vector<"bls12-381.fr">, %329: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %330 = "exec.complete"(%arg159, %328, %329) : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%330) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%331: !exec.stop):  // pred: ^bb0
      %332 = "exec.failed"(%331) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%332) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_91fe8ea73b5db3432f90fc8fe9725c8455fce8782b4cc4d2839d05826de71b8f", sym_visibility = "private"}> ({
    ^bb0(%arg154: !runtime.scope, %arg155: !algebra.field_vector<"bls12-381.fr">, %arg156: !algebra.field_vector<"bls12-381.fr">, %arg157: !algebra.field_vector<"bls12-381.fr">, %arg158: ui64):
      %289 = "exec.apply"(%arg154) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%289)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%290: ui64):  // pred: ^bb0
      %291 = "exec.apply"(%arg154, %arg158, %290) <{binding = @zkl_binding_7, parameters = [], site = "s1"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%291)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%292: !exec.stop):  // 9 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb11, ^bb13
      %293 = "exec.failed"(%292) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%293) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%294: ui64):  // pred: ^bb1
      %295 = "exec.apply"(%arg154) <{binding = @zkl_binding_8, parameters = [], site = "s3"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%295)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb4(%296: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb3
      %297 = "func.call"(%arg154, %296, %arg158, %arg155) <{callee = @zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35}> {runtime.site = "s5"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%297)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb5(%298: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb4
      %299 = "exec.apply"(%arg154) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s7"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%299)[^bb6, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb6(%300: ui64):  // pred: ^bb5
      %301 = "exec.apply"(%arg154) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s9"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%301)[^bb7, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb7(%302: ui64):  // pred: ^bb6
      %303 = "exec.range"(%arg154, %302, %arg158) <{site = "s13"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%303)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i64, i64)>) -> ()
    ^bb8(%304: i64, %305: i64):  // pred: ^bb7
      %306 = "runtime.borrow_transfer"(%arg154, %298, %300) : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>
      "cf.br"(%304, %306)[^bb9] : (i64, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb9(%307: i64, %308: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>):  // 2 preds: ^bb8, ^bb12
      %309 = "arith.cmpi"(%307, %305) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%309, %308)[^bb10, ^bb11] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb10:  // pred: ^bb9
      %310 = "runtime.iteration"(%arg154, %307) <{site = "s13"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%310)[^bb14, ^bb13] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb11(%311: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>):  // pred: ^bb9
      %312 = "runtime.accept_transfer"(%arg154, %311) : (!runtime.scope, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>
      "exec.dispatch"(%312)[^bb17, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb12(%313: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>):  // pred: ^bb16
      %314 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %315 = "arith.addi"(%307, %314) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%315, %313)[^bb9] : (i64, !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb13(%316: !exec.stop):  // 3 preds: ^bb10, ^bb14, ^bb15
      "runtime.release_transfer"(%308) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
      "cf.br"(%316)[^bb2] : (!exec.stop) -> ()
    ^bb14(%317: ui64):  // pred: ^bb10
      %318:2 = "runtime.transfer_values"(%308) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> (!algebra.field_vector<"bls12-381.fr">, ui64)
      %319 = "runtime.enter_scope"(%arg154, %307, %317, %318#0, %318#1, %arg156, %arg157, %294) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 6>, site = "s13"}> : (!runtime.scope, i64, ui64, !algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%319)[^bb15, ^bb13] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb15(%320: !runtime.scope):  // pred: ^bb14
      %321 = "func.call"(%320, %317, %318#0, %318#1, %arg156, %arg157, %294) <{callee = @zkl_control_23}> : (!runtime.scope, ui64, !algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>
      %322 = "runtime.exit_scope"(%320, %321) : (!runtime.scope, !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> !exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>)>
      "exec.dispatch"(%322)[^bb16, ^bb13] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>)>) -> ()
    ^bb16(%323: !runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>):  // pred: ^bb15
      "runtime.release_transfer"(%308) : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
      "cf.br"(%323)[^bb12] : (!runtime.transfer<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb17(%324: !algebra.field_vector<"bls12-381.fr">, %325: ui64):  // pred: ^bb11
      %326 = "exec.returned"(%324) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%326) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7217h6c696e655f636f656666696369656e7473", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, !algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>, no_inline, sym_name = "zkl_control_23", sym_visibility = "private"}> ({
    ^bb0(%arg147: !runtime.scope, %arg148: ui64, %arg149: !algebra.field_vector<"bls12-381.fr">, %arg150: ui64, %arg151: !algebra.field_vector<"bls12-381.fr">, %arg152: !algebra.field_vector<"bls12-381.fr">, %arg153: ui64):
      %265 = "func.call"(%arg147, %arg151, %arg150) <{callee = @zkl_6ba53ec68a0230031d706e4a93e78f80425c51108d34ecc0a5aa5681eded9c8e}> {runtime.site = "s14"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%265)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%266: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %267 = "func.call"(%arg147, %arg152, %arg150) <{callee = @zkl_6ba53ec68a0230031d706e4a93e78f80425c51108d34ecc0a5aa5681eded9c8e}> {runtime.site = "s16"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%267)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%268: !exec.stop):  // 10 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb10
      %269 = "exec.failed"(%268) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>
      "func.return"(%269) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb3(%270: !algebra.field<"bls12-381.fr">):  // pred: ^bb1
      %271 = "exec.apply"(%arg147, %arg149) <{binding = @zkl_binding_12, parameters = [], site = "s18"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%271)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb4(%272: !algebra.field_vector<"bls12-381.fr">, %273: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb3
      %274 = "exec.collect"(%arg147, %272, %273, %266) <{body = @zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_body, domain = @zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_domain, site = "s22"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%274)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb5(%275: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb4
      %276 = "exec.compute"(%arg147, %270, %266) <{callee = @zkl_c15efd5f24b71cb9e6e3766d00c208e0a0014177a6ae1e9dd67b23bda4eff8ab, site = "s26"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%276)[^bb6, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb6(%277: !algebra.field<"bls12-381.fr">):  // pred: ^bb5
      %278 = "exec.collect"(%arg147, %272, %273, %277) <{body = @zkl_map_f8f9614d3bd7d4196ffb7d73d3d80b5571e091e9fdbaeb4adc8aa23e703bd4a5_body, domain = @zkl_map_f8f9614d3bd7d4196ffb7d73d3d80b5571e091e9fdbaeb4adc8aa23e703bd4a5_domain, site = "s27"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%278)[^bb7, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb7(%279: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb6
      %280 = "func.call"(%arg147, %279, %arg153) <{callee = @zkl_3d3958243128671a7ae06c730aba5c78b4cae61932510ab43ba5bcabe7324295}> {runtime.site = "s29"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%280)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%281: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb7
      %282 = "exec.collect"(%arg147, %275, %281) <{body = @zkl_map_b7eb5d68e6edd9e938f02a44220440e7b9e5f3fe195e305a87f963f93affd321_body, domain = @zkl_map_b7eb5d68e6edd9e938f02a44220440e7b9e5f3fe195e305a87f963f93affd321_domain, site = "s30"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%282)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb9(%283: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb8
      %284 = "exec.apply"(%arg147) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s32"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%284)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb10(%285: ui64):  // pred: ^bb9
      %286 = "exec.apply"(%arg147, %arg150, %285) <{binding = @zkl_binding_7, parameters = [], site = "s33"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%286)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb11(%287: ui64):  // pred: ^bb10
      %288 = "exec.complete"(%arg147, %283, %287) : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>
      "func.return"(%288) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64)>) -> ()
    }) {runtime.region} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, sym_name = "zkl_map_f8f9614d3bd7d4196ffb7d73d3d80b5571e091e9fdbaeb4adc8aa23e703bd4a5_domain", sym_visibility = "private"}> ({
    ^bb0(%arg145: !algebra.field_vector<"bls12-381.fr">, %arg146: !algebra.field_vector<"bls12-381.fr">):
      %262 = "data.domain_elements"(%arg145) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %263 = "data.domain_elements"(%arg146) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %264 = "data.domain_zip"(%262, %263) : (!data.domain<!algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%264) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_map_f8f9614d3bd7d4196ffb7d73d3d80b5571e091e9fdbaeb4adc8aa23e703bd4a5_body", sym_visibility = "private"}> ({
    ^bb0(%arg139: !runtime.scope, %arg140: !algebra.field<"bls12-381.fr">, %arg141: !algebra.field<"bls12-381.fr">, %arg142: !algebra.field_vector<"bls12-381.fr">, %arg143: !algebra.field_vector<"bls12-381.fr">, %arg144: !algebra.field<"bls12-381.fr">):
      %257 = "exec.compute"(%arg139, %arg140, %arg141, %arg144) <{callee = @zkl_c8eacd293248ba42cad22bd955e2dec7c6105efe1dabf391c3a74b436be7412e, site = "body"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%257)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%258: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %259 = "exec.returned"(%258) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%259) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%260: !exec.stop):  // pred: ^bb0
      %261 = "exec.failed"(%260) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%261) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zkl_map_f8f9614d3bd7d4196ffb7d73d3d80b5571e091e9fdbaeb4adc8aa23e703bd4a5_body", []]} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, sym_name = "zkl_map_b7eb5d68e6edd9e938f02a44220440e7b9e5f3fe195e305a87f963f93affd321_domain", sym_visibility = "private"}> ({
    ^bb0(%arg137: !algebra.field_vector<"bls12-381.fr">, %arg138: !algebra.field_vector<"bls12-381.fr">):
      %254 = "data.domain_elements"(%arg137) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %255 = "data.domain_elements"(%arg138) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %256 = "data.domain_zip"(%254, %255) : (!data.domain<!algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%256) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_map_b7eb5d68e6edd9e938f02a44220440e7b9e5f3fe195e305a87f963f93affd321_body", sym_visibility = "private"}> ({
    ^bb0(%arg132: !runtime.scope, %arg133: !algebra.field<"bls12-381.fr">, %arg134: !algebra.field<"bls12-381.fr">, %arg135: !algebra.field_vector<"bls12-381.fr">, %arg136: !algebra.field_vector<"bls12-381.fr">):
      %249 = "exec.compute"(%arg132, %arg133, %arg134) <{callee = @zkl_02aa9bd9900f843069baf97f23f4f5ccab54b136c8fed5b90842e4c46b7e5fcd, site = "body"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%249)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%250: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %251 = "exec.returned"(%250) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%251) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%252: !exec.stop):  // pred: ^bb0
      %253 = "exec.failed"(%252) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%253) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zkl_map_b7eb5d68e6edd9e938f02a44220440e7b9e5f3fe195e305a87f963f93affd321_body", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_f9bc3972b3acce79409bfe72125c3b04de4dbb81a13d1dfbc918146c1354315c", sym_visibility = "private"}> ({
    ^bb0(%arg128: !runtime.scope, %arg129: !algebra.field_vector<"bls12-381.fr">, %arg130: !algebra.field<"bls12-381.fr">, %arg131: ui64):
      %244 = "func.call"(%arg128, %arg129, %arg130, %arg131) <{callee = @zkl_8184464d79b9512ca72dac4d64d1ba3d187fd1efb0b8118690b5a104ab35f351}> {runtime.site = "s2"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%244)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%245: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %246 = "exec.returned"(%245) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%246) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%247: !exec.stop):  // pred: ^bb0
      %248 = "exec.failed"(%247) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%248) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zks_dab24f1af4cf6ec12b12d53d6ef952d45bf4866eaa489b84bfcce536b42b3f2a", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_8184464d79b9512ca72dac4d64d1ba3d187fd1efb0b8118690b5a104ab35f351", sym_visibility = "private"}> ({
    ^bb0(%arg124: !runtime.scope, %arg125: !algebra.field_vector<"bls12-381.fr">, %arg126: !algebra.field<"bls12-381.fr">, %arg127: ui64):
      %235 = "exec.apply"(%arg124, %arg125, %arg126) <{binding = @zkl_binding_9, parameters = [], site = "s0"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%235)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%236: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %237 = "exec.compute"(%arg124) <{callee = @zkl_e38306e1154810613f8b855b4e24394048cbbd4c4b2723722235b0e03496f137, site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%237)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%238: !exec.stop):  // 3 preds: ^bb0, ^bb1, ^bb3
      %239 = "exec.failed"(%238) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%239) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%240: !algebra.field<"bls12-381.fr">):  // pred: ^bb1
      %241 = "func.call"(%arg124, %236, %240, %arg127) <{callee = @zkl_fbd2531b804047766f8107241edd0ea81368b70795e44e4d8e07484d142783bb}> {runtime.site = "s2"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%241)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb4(%242: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb3
      %243 = "exec.returned"(%242) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%243) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7212h636f6e7374616e745f726f77", []]} : () -> ()
    "func.func"() <{function_type = () -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_e38306e1154810613f8b855b4e24394048cbbd4c4b2723722235b0e03496f137", sym_visibility = "private"}> ({
      %234 = "algebra.constant"() <{value = #algebra.literal<<"bls12-381.fr">, 0 : ui255> : !algebra.field<"bls12-381.fr">}> : () -> !algebra.field<"bls12-381.fr">
      "func.return"(%234) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35", sym_visibility = "private"}> ({
    ^bb0(%arg120: !runtime.scope, %arg121: !algebra.field_vector<"bls12-381.fr">, %arg122: ui64, %arg123: !algebra.field_vector<"bls12-381.fr">):
      %229 = "exec.fold"(%arg120, %arg123, %arg121, %arg122) <{domain = @finite_zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35_s0_domain, site = "s0", step = @finite_zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35_s0_body}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%229)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%230: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %231 = "exec.returned"(%230) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%231) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%232: !exec.stop):  // pred: ^bb0
      %233 = "exec.failed"(%232) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%233) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg119: !algebra.field_vector<"bls12-381.fr">):
      %228 = "data.domain_elements"(%arg119) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%228) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "finite_zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg114: !runtime.scope, %arg115: !algebra.field_vector<"bls12-381.fr">, %arg116: !algebra.field<"bls12-381.fr">, %arg117: !algebra.field_vector<"bls12-381.fr">, %arg118: ui64):
      %223 = "func.call"(%arg114, %arg115, %arg116, %arg118) <{callee = @zkl_f9bc3972b3acce79409bfe72125c3b04de4dbb81a13d1dfbc918146c1354315c}> {runtime.site = "body"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%223)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%224: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %225 = "exec.returned"(%224) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%225) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%226: !exec.stop):  // pred: ^bb0
      %227 = "exec.failed"(%226) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%227) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["finite_zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35_s0_body", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_6ba53ec68a0230031d706e4a93e78f80425c51108d34ecc0a5aa5681eded9c8e", sym_visibility = "private"}> ({
    ^bb0(%arg111: !runtime.scope, %arg112: !algebra.field_vector<"bls12-381.fr">, %arg113: ui64):
      %213 = "exec.compute"(%arg111) <{callee = @zkl_e38306e1154810613f8b855b4e24394048cbbd4c4b2723722235b0e03496f137, site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%213)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%214: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %215 = "exec.apply"(%arg111) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s1"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%215)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%216: !exec.stop):  // 3 preds: ^bb0, ^bb1, ^bb3
      %217 = "exec.failed"(%216) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%217) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb3(%218: ui64):  // pred: ^bb1
      %219 = "func.call"(%arg111, %214, %218, %arg113, %arg112) <{callee = @zkl_4d05c370830a894df2470c3859782e53b3322378b124acf8f383759935b54a45}> {runtime.site = "s5"} : (!runtime.scope, !algebra.field<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
      "exec.dispatch"(%219)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb4(%220: !algebra.field<"bls12-381.fr">, %221: ui64):  // pred: ^bb3
      %222 = "exec.returned"(%220) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%222) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b727h656c656d656e74", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, ui64, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>, no_inline, sym_name = "zkl_09043a1369ab6c082f8534fc9d21f34f77067e68b9a4c2a907a132342ff59811", sym_visibility = "private"}> ({
    ^bb0(%arg106: !runtime.scope, %arg107: !algebra.field<"bls12-381.fr">, %arg108: ui64, %arg109: !algebra.field<"bls12-381.fr">, %arg110: ui64):
      %187 = "exec.apply"(%arg106, %arg108, %arg110) <{binding = @zkl_binding_4, parameters = [], site = "s3"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%187)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%188: i1):  // pred: ^bb0
      %189 = "exec.test"(%arg106, %188) <{site = "s6"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%189)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%190: !exec.stop):  // 10 preds: ^bb0, ^bb1, ^bb4, ^bb5, ^bb6, ^bb7, ^bb8, ^bb10, ^bb11, ^bb13
      %191 = "exec.failed"(%190) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%191) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb3(%192: i1):  // pred: ^bb1
      "cf.cond_br"(%192)[^bb4, ^bb5] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb4:  // pred: ^bb3
      %193 = "runtime.enter_scope"(%arg106, %arg107, %arg109) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "then", site = "s6"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%193)[^bb7, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb5:  // pred: ^bb3
      %194 = "runtime.enter_scope"(%arg106, %arg107, %arg109) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "else", site = "s6"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%194)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6(%195: !algebra.field<"bls12-381.fr">):  // 2 preds: ^bb9, ^bb12
      %196 = "exec.apply"(%arg106) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s11"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%196)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb7(%197: !runtime.scope):  // pred: ^bb4
      %198 = "func.call"(%197, %arg107, %arg109) <{callee = @zkl_control_24}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      %199 = "runtime.exit_scope"(%197, %198) : (!runtime.scope, !exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!algebra.field<"bls12-381.fr">)>)>
      "exec.dispatch"(%199)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!algebra.field<"bls12-381.fr">)>)>) -> ()
    ^bb8(%200: !runtime.transfer<(!algebra.field<"bls12-381.fr">)>):  // pred: ^bb7
      %201 = "runtime.accept_transfer"(%arg106, %200) : (!runtime.scope, !runtime.transfer<(!algebra.field<"bls12-381.fr">)>) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%201)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb9(%202: !algebra.field<"bls12-381.fr">):  // pred: ^bb8
      "cf.br"(%202)[^bb6] : (!algebra.field<"bls12-381.fr">) -> ()
    ^bb10(%203: !runtime.scope):  // pred: ^bb5
      %204 = "func.call"(%203, %arg107, %arg109) <{callee = @zkl_control_25}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      %205 = "runtime.exit_scope"(%203, %204) : (!runtime.scope, !exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!algebra.field<"bls12-381.fr">)>)>
      "exec.dispatch"(%205)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!algebra.field<"bls12-381.fr">)>)>) -> ()
    ^bb11(%206: !runtime.transfer<(!algebra.field<"bls12-381.fr">)>):  // pred: ^bb10
      %207 = "runtime.accept_transfer"(%arg106, %206) : (!runtime.scope, !runtime.transfer<(!algebra.field<"bls12-381.fr">)>) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%207)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb12(%208: !algebra.field<"bls12-381.fr">):  // pred: ^bb11
      "cf.br"(%208)[^bb6] : (!algebra.field<"bls12-381.fr">) -> ()
    ^bb13(%209: ui64):  // pred: ^bb6
      %210 = "exec.apply"(%arg106, %arg108, %209) <{binding = @zkl_binding_7, parameters = [], site = "s12"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%210)[^bb14, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb14(%211: ui64):  // pred: ^bb13
      %212 = "exec.returned"(%195, %211) : (!algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%212) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>) -> ()
    }) {runtime.origin = ["zks_09bf7b2d0f9a7fa09310de095093a32f6884e18e73addb2f7bae58f6b7c6de5b", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_24", sym_visibility = "private"}> ({
    ^bb0(%arg103: !runtime.scope, %arg104: !algebra.field<"bls12-381.fr">, %arg105: !algebra.field<"bls12-381.fr">):
      %186 = "exec.complete"(%arg103, %arg105) : (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%186) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_25", sym_visibility = "private"}> ({
    ^bb0(%arg100: !runtime.scope, %arg101: !algebra.field<"bls12-381.fr">, %arg102: !algebra.field<"bls12-381.fr">):
      %185 = "exec.complete"(%arg100, %arg101) : (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%185) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>, no_inline, sym_name = "zkl_4d05c370830a894df2470c3859782e53b3322378b124acf8f383759935b54a45", sym_visibility = "private"}> ({
    ^bb0(%arg95: !runtime.scope, %arg96: !algebra.field<"bls12-381.fr">, %arg97: ui64, %arg98: ui64, %arg99: !algebra.field_vector<"bls12-381.fr">):
      %179 = "exec.fold"(%arg95, %arg99, %arg96, %arg97, %arg98) <{domain = @finite_zkl_4d05c370830a894df2470c3859782e53b3322378b124acf8f383759935b54a45_s0_domain, site = "s0", step = @finite_zkl_4d05c370830a894df2470c3859782e53b3322378b124acf8f383759935b54a45_s0_body}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
      "exec.dispatch"(%179)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb1(%180: !algebra.field<"bls12-381.fr">, %181: ui64):  // pred: ^bb0
      %182 = "exec.returned"(%180, %181) : (!algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%182) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb2(%183: !exec.stop):  // pred: ^bb0
      %184 = "exec.failed"(%183) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%184) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_4d05c370830a894df2470c3859782e53b3322378b124acf8f383759935b54a45_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg94: !algebra.field_vector<"bls12-381.fr">):
      %178 = "data.domain_elements"(%arg94) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%178) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, ui64, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>, no_inline, sym_name = "finite_zkl_4d05c370830a894df2470c3859782e53b3322378b124acf8f383759935b54a45_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg88: !runtime.scope, %arg89: !algebra.field<"bls12-381.fr">, %arg90: ui64, %arg91: !algebra.field<"bls12-381.fr">, %arg92: !algebra.field_vector<"bls12-381.fr">, %arg93: ui64):
      %172 = "func.call"(%arg88, %arg89, %arg90, %arg91, %arg93) <{callee = @zkl_09043a1369ab6c082f8534fc9d21f34f77067e68b9a4c2a907a132342ff59811}> {runtime.site = "body"} : (!runtime.scope, !algebra.field<"bls12-381.fr">, ui64, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
      "exec.dispatch"(%172)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb1(%173: !algebra.field<"bls12-381.fr">, %174: ui64):  // pred: ^bb0
      %175 = "exec.returned"(%173, %174) : (!algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%175) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb2(%176: !exec.stop):  // pred: ^bb0
      %177 = "exec.failed"(%176) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%177) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>) -> ()
    }) {runtime.origin = ["finite_zkl_4d05c370830a894df2470c3859782e53b3322378b124acf8f383759935b54a45_s0_body", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_c15efd5f24b71cb9e6e3766d00c208e0a0014177a6ae1e9dd67b23bda4eff8ab", sym_visibility = "private"}> ({
    ^bb0(%arg86: !algebra.field<"bls12-381.fr">, %arg87: !algebra.field<"bls12-381.fr">):
      %171 = "algebra.field_subtract"(%arg86, %arg87) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%171) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_c8eacd293248ba42cad22bd955e2dec7c6105efe1dabf391c3a74b436be7412e", sym_visibility = "private"}> ({
    ^bb0(%arg83: !algebra.field<"bls12-381.fr">, %arg84: !algebra.field<"bls12-381.fr">, %arg85: !algebra.field<"bls12-381.fr">):
      %169 = "algebra.field_subtract"(%arg84, %arg83) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %170 = "algebra.field_multiply"(%169, %arg85) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%170) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_3d3958243128671a7ae06c730aba5c78b4cae61932510ab43ba5bcabe7324295", sym_visibility = "private"}> ({
    ^bb0(%arg80: !runtime.scope, %arg81: !algebra.field_vector<"bls12-381.fr">, %arg82: ui64):
      %156 = "exec.apply"(%arg80) <{binding = @zkl_binding_8, parameters = [], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%156)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%157: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %158 = "exec.compute"(%arg80) <{callee = @zkl_e38306e1154810613f8b855b4e24394048cbbd4c4b2723722235b0e03496f137, site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%158)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%159: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %160 = "exec.failed"(%159) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%160) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%161: !algebra.field<"bls12-381.fr">):  // pred: ^bb1
      %162 = "exec.apply"(%arg80) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s2"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%162)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%163: ui64):  // pred: ^bb3
      %164 = "func.call"(%arg80, %157, %161, %163, %arg82, %arg81) <{callee = @zkl_b09f44c87195c8e3d60f4dede007ee713df6eb6126ac95620f16b0ca8ac2c403}> {runtime.site = "s6"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
      "exec.dispatch"(%164)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb5(%165: !algebra.field_vector<"bls12-381.fr">, %166: !algebra.field<"bls12-381.fr">, %167: ui64):  // pred: ^bb4
      %168 = "exec.returned"(%165) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%168) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7210h73686966745f726f7773", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>, no_inline, sym_name = "zkl_abd6f98141af14ddf8b9152129fb3a9fb361b5735ade780e8d1c876d68deb283", sym_visibility = "private"}> ({
    ^bb0(%arg74: !runtime.scope, %arg75: !algebra.field_vector<"bls12-381.fr">, %arg76: !algebra.field<"bls12-381.fr">, %arg77: ui64, %arg78: !algebra.field<"bls12-381.fr">, %arg79: ui64):
      %124 = "exec.apply"(%arg74, %arg77, %arg79) <{binding = @zkl_binding_3, parameters = [], site = "s4"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%124)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%125: ui64):  // pred: ^bb0
      %126 = "exec.apply"(%arg74) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s5"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%126)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%127: !exec.stop):  // 13 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb6, ^bb7, ^bb8, ^bb9, ^bb10, ^bb12, ^bb13, ^bb15, ^bb16
      %128 = "exec.failed"(%127) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%128) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb3(%129: ui64):  // pred: ^bb1
      %130 = "exec.apply"(%arg74, %125, %129) <{binding = @zkl_binding_4, parameters = [], site = "s6"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%130)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb4(%131: i1):  // pred: ^bb3
      %132 = "exec.test"(%arg74, %131) <{site = "s8"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%132)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb5(%133: i1):  // pred: ^bb4
      "cf.cond_br"(%133)[^bb6, ^bb7] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb6:  // pred: ^bb5
      %134 = "runtime.enter_scope"(%arg74, %arg76) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "then", site = "s8"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%134)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // pred: ^bb5
      %135 = "runtime.enter_scope"(%arg74, %arg76) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "else", site = "s8"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%135)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb8(%136: !algebra.field<"bls12-381.fr">):  // 2 preds: ^bb11, ^bb14
      %137 = "exec.apply"(%arg74, %arg75, %136) <{binding = @zkl_binding_9, parameters = [], site = "s13"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%137)[^bb15, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb9(%138: !runtime.scope):  // pred: ^bb6
      %139 = "func.call"(%138, %arg76) <{callee = @zkl_control_26}> : (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      %140 = "runtime.exit_scope"(%138, %139) : (!runtime.scope, !exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!algebra.field<"bls12-381.fr">)>)>
      "exec.dispatch"(%140)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!algebra.field<"bls12-381.fr">)>)>) -> ()
    ^bb10(%141: !runtime.transfer<(!algebra.field<"bls12-381.fr">)>):  // pred: ^bb9
      %142 = "runtime.accept_transfer"(%arg74, %141) : (!runtime.scope, !runtime.transfer<(!algebra.field<"bls12-381.fr">)>) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%142)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb11(%143: !algebra.field<"bls12-381.fr">):  // pred: ^bb10
      "cf.br"(%143)[^bb8] : (!algebra.field<"bls12-381.fr">) -> ()
    ^bb12(%144: !runtime.scope):  // pred: ^bb7
      %145 = "func.call"(%144, %arg76) <{callee = @zkl_control_27}> : (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      %146 = "runtime.exit_scope"(%144, %145) : (!runtime.scope, !exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!algebra.field<"bls12-381.fr">)>)>
      "exec.dispatch"(%146)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!algebra.field<"bls12-381.fr">)>)>) -> ()
    ^bb13(%147: !runtime.transfer<(!algebra.field<"bls12-381.fr">)>):  // pred: ^bb12
      %148 = "runtime.accept_transfer"(%arg74, %147) : (!runtime.scope, !runtime.transfer<(!algebra.field<"bls12-381.fr">)>) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%148)[^bb14, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb14(%149: !algebra.field<"bls12-381.fr">):  // pred: ^bb13
      "cf.br"(%149)[^bb8] : (!algebra.field<"bls12-381.fr">) -> ()
    ^bb15(%150: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb8
      %151 = "exec.apply"(%arg74) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s15"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%151)[^bb16, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb16(%152: ui64):  // pred: ^bb15
      %153 = "exec.apply"(%arg74, %arg77, %152) <{binding = @zkl_binding_7, parameters = [], site = "s16"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%153)[^bb17, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb17(%154: ui64):  // pred: ^bb16
      %155 = "exec.returned"(%150, %arg78, %154) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%155) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>) -> ()
    }) {runtime.origin = ["zks_8581fd068387f06c481369dff1456320f16962167c6391f3d8bc1fe2a6daf333", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_26", sym_visibility = "private"}> ({
    ^bb0(%arg72: !runtime.scope, %arg73: !algebra.field<"bls12-381.fr">):
      %119 = "exec.compute"(%arg72) <{callee = @zkl_e38306e1154810613f8b855b4e24394048cbbd4c4b2723722235b0e03496f137, site = "s9"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%119)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%120: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %121 = "exec.complete"(%arg72, %120) : (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%121) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%122: !exec.stop):  // pred: ^bb0
      %123 = "exec.failed"(%122) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%123) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_27", sym_visibility = "private"}> ({
    ^bb0(%arg70: !runtime.scope, %arg71: !algebra.field<"bls12-381.fr">):
      %118 = "exec.complete"(%arg70, %arg71) : (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%118) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>, no_inline, sym_name = "zkl_b09f44c87195c8e3d60f4dede007ee713df6eb6126ac95620f16b0ca8ac2c403", sym_visibility = "private"}> ({
    ^bb0(%arg64: !runtime.scope, %arg65: !algebra.field_vector<"bls12-381.fr">, %arg66: !algebra.field<"bls12-381.fr">, %arg67: ui64, %arg68: ui64, %arg69: !algebra.field_vector<"bls12-381.fr">):
      %111 = "exec.fold"(%arg64, %arg69, %arg65, %arg66, %arg67, %arg68) <{domain = @finite_zkl_b09f44c87195c8e3d60f4dede007ee713df6eb6126ac95620f16b0ca8ac2c403_s0_domain, site = "s0", step = @finite_zkl_b09f44c87195c8e3d60f4dede007ee713df6eb6126ac95620f16b0ca8ac2c403_s0_body}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
      "exec.dispatch"(%111)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb1(%112: !algebra.field_vector<"bls12-381.fr">, %113: !algebra.field<"bls12-381.fr">, %114: ui64):  // pred: ^bb0
      %115 = "exec.returned"(%112, %113, %114) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%115) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb2(%116: !exec.stop):  // pred: ^bb0
      %117 = "exec.failed"(%116) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%117) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_b09f44c87195c8e3d60f4dede007ee713df6eb6126ac95620f16b0ca8ac2c403_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg63: !algebra.field_vector<"bls12-381.fr">):
      %110 = "data.domain_elements"(%arg63) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%110) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>, no_inline, sym_name = "finite_zkl_b09f44c87195c8e3d60f4dede007ee713df6eb6126ac95620f16b0ca8ac2c403_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg56: !runtime.scope, %arg57: !algebra.field_vector<"bls12-381.fr">, %arg58: !algebra.field<"bls12-381.fr">, %arg59: ui64, %arg60: !algebra.field<"bls12-381.fr">, %arg61: !algebra.field_vector<"bls12-381.fr">, %arg62: ui64):
      %103 = "func.call"(%arg56, %arg57, %arg58, %arg59, %arg60, %arg62) <{callee = @zkl_abd6f98141af14ddf8b9152129fb3a9fb361b5735ade780e8d1c876d68deb283}> {runtime.site = "body"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
      "exec.dispatch"(%103)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb1(%104: !algebra.field_vector<"bls12-381.fr">, %105: !algebra.field<"bls12-381.fr">, %106: ui64):  // pred: ^bb0
      %107 = "exec.returned"(%104, %105, %106) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%107) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb2(%108: !exec.stop):  // pred: ^bb0
      %109 = "exec.failed"(%108) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%109) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>) -> ()
    }) {runtime.origin = ["finite_zkl_b09f44c87195c8e3d60f4dede007ee713df6eb6126ac95620f16b0ca8ac2c403_s0_body", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_02aa9bd9900f843069baf97f23f4f5ccab54b136c8fed5b90842e4c46b7e5fcd", sym_visibility = "private"}> ({
    ^bb0(%arg54: !algebra.field<"bls12-381.fr">, %arg55: !algebra.field<"bls12-381.fr">):
      %102 = "algebra.field_add"(%arg54, %arg55) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%102) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_ca5df6081733f8afff4ae42147eb8eba3338d5a96600a7155f619346f19e4b47", sym_visibility = "private"}> ({
    ^bb0(%arg51: !runtime.scope, %arg52: !algebra.field_vector<"bls12-381.fr">, %arg53: ui64):
      %93 = "exec.apply"(%arg51) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%93)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%94: ui64):  // pred: ^bb0
      %95 = "exec.apply"(%arg51, %arg53, %94) <{binding = @zkl_binding_7, parameters = [], site = "s1"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%95)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%96: !exec.stop):  // 3 preds: ^bb0, ^bb1, ^bb3
      %97 = "exec.failed"(%96) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%97) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb3(%98: ui64):  // pred: ^bb1
      %99 = "func.call"(%arg51, %arg52, %98) <{callee = @zkl_6ba53ec68a0230031d706e4a93e78f80425c51108d34ecc0a5aa5681eded9c8e}> {runtime.site = "s2"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%99)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb4(%100: !algebra.field<"bls12-381.fr">):  // pred: ^bb3
      %101 = "exec.returned"(%100) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%101) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7213h656c656d656e745f6166746572", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_6ec6b9d6cb41b6bf4ef8e898ba1b283d099252f7de2db0b173f26714e3a46216", sym_visibility = "private"}> ({
    ^bb0(%arg49: !runtime.scope, %arg50: !algebra.field_vector<"bls12-381.fr">):
      %88 = "exec.apply"(%arg49, %arg50) <{binding = @zkl_binding_10, parameters = [], site = "s0"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%88)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%89: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %90 = "exec.returned"(%89) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%90) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%91: !exec.stop):  // pred: ^bb0
      %92 = "exec.failed"(%91) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%92) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6310h7072696d6974697665736h766563746f723h73756d", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_161d519d8d5fe2674feddb6e6d14269c9cca82ff216b6b3205ade46cc8b8d35f", sym_visibility = "private"}> ({
    ^bb0(%arg44: !runtime.scope, %arg45: !algebra.field_vector<"bls12-381.fr">, %arg46: !algebra.field_vector<"bls12-381.fr">, %arg47: !algebra.field_vector<"bls12-381.fr">, %arg48: !algebra.field_vector<"bls12-381.fr">):
      %53 = "exec.apply"(%arg44, %arg46) <{binding = @zkl_binding_2, parameters = [], site = "s0"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%53)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%54: ui64):  // pred: ^bb0
      %55 = "exec.apply"(%arg44, %arg47) <{binding = @zkl_binding_2, parameters = [], site = "s1"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%55)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%56: !exec.stop):  // 12 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb10, ^bb11, ^bb12
      %57 = "exec.failed"(%56) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%57) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb3(%58: ui64):  // pred: ^bb1
      %59 = "exec.apply"(%arg44, %54, %58) <{binding = @zkl_binding_7, parameters = [], site = "s2"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%59)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%60: ui64):  // pred: ^bb3
      %61 = "exec.apply"(%arg44, %arg48) <{binding = @zkl_binding_2, parameters = [], site = "s3"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%61)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%62: ui64):  // pred: ^bb4
      %63 = "exec.apply"(%arg44, %60, %62) <{binding = @zkl_binding_7, parameters = [], site = "s4"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%63)[^bb6, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb6(%64: ui64):  // pred: ^bb5
      %65 = "exec.apply"(%arg44) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s5"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%65)[^bb7, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb7(%66: ui64):  // pred: ^bb6
      %67 = "func.call"(%arg44, %arg45, %64, %66) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a}> {runtime.site = "s6"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%67)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb8(%68: !algebra.field_vector<"bls12-381.fr">, %69: ui64, %70: ui64):  // pred: ^bb7
      %71 = "func.call"(%arg44, %68, %69, %70, %arg46) <{callee = @zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be}> {runtime.site = "s8"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%71)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb9(%72: !algebra.field_vector<"bls12-381.fr">, %73: ui64, %74: ui64):  // pred: ^bb8
      %75 = "func.call"(%arg44, %72, %73, %74, %arg47) <{callee = @zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be}> {runtime.site = "s9"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%75)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb10(%76: !algebra.field_vector<"bls12-381.fr">, %77: ui64, %78: ui64):  // pred: ^bb9
      %79 = "func.call"(%arg44, %76, %77, %78, %arg48) <{callee = @zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be}> {runtime.site = "s10"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%79)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb11(%80: !algebra.field_vector<"bls12-381.fr">, %81: ui64, %82: ui64):  // pred: ^bb10
      %83 = "exec.compute"(%arg44, %80, %81, %82) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33, site = "s11"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%83)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb12(%84: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb11
      %85 = "exec.apply"(%arg44, %84) <{binding = @zkl_binding_10, parameters = [], site = "s12"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%85)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb13(%86: !algebra.field<"bls12-381.fr">):  // pred: ^bb12
      %87 = "exec.returned"(%86) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%87) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7215h6576616c756174655f776972696e67", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_1f2e31017a1a0403a56241b1d83eac39d1ecc40b298cd066516f78ae9c5b3434", sym_visibility = "private"}> ({
    ^bb0(%arg40: !runtime.scope, %arg41: !algebra.field_vector<"bls12-381.fr">, %arg42: !algebra.field_vector<"bls12-381.fr">, %arg43: !algebra.field<"bls12-381.fr">):
      %48 = "exec.collect"(%arg40, %arg41, %arg42, %arg43) <{body = @zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_body, domain = @zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_domain, site = "s0"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%48)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%49: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %50 = "exec.returned"(%49) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%50) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%51: !exec.stop):  // pred: ^bb0
      %52 = "exec.failed"(%51) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%52) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7210h6c696e655f706f696e74", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_21465134b1aa848c616c790eff1907b1a442ba76730b77da2be48acd923d6ff7", sym_visibility = "private"}> ({
    ^bb0(%arg37: !runtime.scope, %arg38: !algebra.field_vector<"bls12-381.fr">, %arg39: !algebra.field<"bls12-381.fr">):
      %39 = "exec.compute"(%arg37) <{callee = @zkl_acc5a50f3a300b126874f48e782cbb903e9f900ea776915474c16f8e7ecd49b5, site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%39)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%40: !algebra.field<"bls12-381.fr">, %41: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %42 = "func.call"(%arg37, %40, %41, %arg39, %arg38) <{callee = @zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d}> {runtime.site = "s2"} : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%42)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%43: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %44 = "exec.failed"(%43) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%44) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb3(%45: !algebra.field<"bls12-381.fr">, %46: !algebra.field<"bls12-381.fr">):  // pred: ^bb1
      %47 = "exec.returned"(%45) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%47) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7221h6576616c756174655f636f656666696369656e7473", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_bcbdb252ffc9abd0563757a6a45f0dccb9a7c345ecbfb58b787c5137455bd42e", sym_visibility = "private"}> ({
    ^bb0(%arg32: !runtime.scope, %arg33: !algebra.field<"bls12-381.fr">, %arg34: !algebra.field<"bls12-381.fr">, %arg35: !algebra.field<"bls12-381.fr">, %arg36: !algebra.field<"bls12-381.fr">):
      %33 = "exec.compute"(%arg32, %arg33, %arg34, %arg35, %arg36) <{callee = @zkl_82e44b33934fd674fa24fbb7f5705f2364f5020774fe25318dd2b968f9d001e4, site = "s4"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%33)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%34: !algebra.field<"bls12-381.fr">, %35: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %36 = "exec.returned"(%34, %35) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%36) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%37: !exec.stop):  // pred: ^bb0
      %38 = "exec.failed"(%37) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%38) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zks_c896eee882b0de19255b06dc85cce9b3173549e68e26b71cdd01e723c9c5b52d", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), sym_name = "zkl_82e44b33934fd674fa24fbb7f5705f2364f5020774fe25318dd2b968f9d001e4", sym_visibility = "private"}> ({
    ^bb0(%arg28: !algebra.field<"bls12-381.fr">, %arg29: !algebra.field<"bls12-381.fr">, %arg30: !algebra.field<"bls12-381.fr">, %arg31: !algebra.field<"bls12-381.fr">):
      %30 = "algebra.field_multiply"(%arg30, %arg29) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %31 = "algebra.field_add"(%arg28, %30) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %32 = "algebra.field_multiply"(%arg29, %arg31) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%31, %32) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = () -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), sym_name = "zkl_acc5a50f3a300b126874f48e782cbb903e9f900ea776915474c16f8e7ecd49b5", sym_visibility = "private"}> ({
      %28 = "algebra.constant"() <{value = #algebra.literal<<"bls12-381.fr">, 0 : ui255> : !algebra.field<"bls12-381.fr">}> : () -> !algebra.field<"bls12-381.fr">
      %29 = "algebra.constant"() <{value = #algebra.literal<<"bls12-381.fr">, 1 : ui255> : !algebra.field<"bls12-381.fr">}> : () -> !algebra.field<"bls12-381.fr">
      "func.return"(%28, %29) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d", sym_visibility = "private"}> ({
    ^bb0(%arg23: !runtime.scope, %arg24: !algebra.field<"bls12-381.fr">, %arg25: !algebra.field<"bls12-381.fr">, %arg26: !algebra.field<"bls12-381.fr">, %arg27: !algebra.field_vector<"bls12-381.fr">):
      %22 = "exec.fold"(%arg23, %arg27, %arg24, %arg25, %arg26) <{domain = @finite_zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d_s0_domain, site = "s0", step = @finite_zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d_s0_body}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%22)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%23: !algebra.field<"bls12-381.fr">, %24: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %25 = "exec.returned"(%23, %24) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%25) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%26: !exec.stop):  // pred: ^bb0
      %27 = "exec.failed"(%26) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%27) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg22: !algebra.field_vector<"bls12-381.fr">):
      %21 = "data.domain_elements"(%arg22) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%21) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "finite_zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg16: !runtime.scope, %arg17: !algebra.field<"bls12-381.fr">, %arg18: !algebra.field<"bls12-381.fr">, %arg19: !algebra.field<"bls12-381.fr">, %arg20: !algebra.field_vector<"bls12-381.fr">, %arg21: !algebra.field<"bls12-381.fr">):
      %15 = "func.call"(%arg16, %arg17, %arg18, %arg19, %arg21) <{callee = @zkl_bcbdb252ffc9abd0563757a6a45f0dccb9a7c345ecbfb58b787c5137455bd42e}> {runtime.site = "body"} : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%15)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%16: !algebra.field<"bls12-381.fr">, %17: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %18 = "exec.returned"(%16, %17) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%18) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%19: !exec.stop):  // pred: ^bb0
      %20 = "exec.failed"(%19) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%20) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["finite_zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d_s0_body", []]} : () -> ()
    "protocol.func"() <{contracts = [["target", "input_value", [@zkl_cb10975ebbde52f87ba3f031d71fbab61676c0ccc3b05423f90b82c03f36e3ff, [["input", 0, "role00000000"], ["input", 1, "role00000000"], ["input", 2, "role00000000"]]], unit, ["output", 0, "role00000000"]]], function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, input_roles = [["role00000000"], ["role00000000"], ["role00000000"]], origin = ["gkr::Input", [["F", ["field", "bls12-381.fr"]]]], output_roles = [["role00000000"]], roles = ["role00000000"], sym_name = "zkl_9719be65739d901a935dbaa0f3f8323a785562f7eee1e60cc8c8c9676f8fdb55"}> ({
    ^bb0(%arg13: !algebra.field_vector<"bls12-381.fr">, %arg14: !algebra.field_vector<"bls12-381.fr">, %arg15: !algebra.field<"bls12-381.fr">):
      %14 = "protocol.local_call"(%arg13, %arg14, %arg15) <{callee = @zkl_d74cb9bd9ed782590145b66a573f8104fca0e842c109c7d034296431308fc6b9, role = "role00000000", site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "protocol.return"(%14) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "zkf_d1b83b15191b85497fc6003ecffb377b2ff71a9228a1114a266874f0ba672708", sym_visibility = "private"}> ({
    ^bb0(%arg10: !algebra.field_vector<"bls12-381.fr">, %arg11: !algebra.field_vector<"bls12-381.fr">, %arg12: !algebra.field<"bls12-381.fr">):
      %10 = "algebra.multilinear_restrict_prefix"(%arg10, %arg11) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
      %11 = "algebra.constant"() <{value = #algebra.literal<<"bls12-381.fr">, 0 : ui255> : !algebra.field<"bls12-381.fr">}> : () -> !algebra.field<"bls12-381.fr">
      %12 = "algebra.finite_fold"(%10, %11) <{domain = @finite_zkl_cb10975ebbde52f87ba3f031d71fbab61676c0ccc3b05423f90b82c03f36e3ff_s2_domain, step = @finite_zkl_cb10975ebbde52f87ba3f031d71fbab61676c0ccc3b05423f90b82c03f36e3ff_s2_body}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %13 = "algebra.field_equal"(%arg12, %12) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "func.return"(%13) : (i1) -> ()
    }) : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_cb10975ebbde52f87ba3f031d71fbab61676c0ccc3b05423f90b82c03f36e3ff_s2_domain", sym_visibility = "private"}> ({
    ^bb0(%arg9: !algebra.field_vector<"bls12-381.fr">):
      %9 = "data.domain_elements"(%arg9) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%9) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "finite_zkl_cb10975ebbde52f87ba3f031d71fbab61676c0ccc3b05423f90b82c03f36e3ff_s2_body", sym_visibility = "private"}> ({
    ^bb0(%arg6: !algebra.field<"bls12-381.fr">, %arg7: !algebra.field<"bls12-381.fr">, %arg8: !algebra.field_vector<"bls12-381.fr">):
      %8 = "func.call"(%arg6, %arg7) <{callee = @zkl_293773d0130047867a66c9eaf450957dc940a0b0b9ee8988021422577cf8335f}> : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%8) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_293773d0130047867a66c9eaf450957dc940a0b0b9ee8988021422577cf8335f", sym_visibility = "private"}> ({
    ^bb0(%arg4: !algebra.field<"bls12-381.fr">, %arg5: !algebra.field<"bls12-381.fr">):
      %7 = "algebra.field_add"(%arg4, %arg5) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%7) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_d74cb9bd9ed782590145b66a573f8104fca0e842c109c7d034296431308fc6b9", sym_visibility = "private"}> ({
    ^bb0(%arg0: !runtime.scope, %arg1: !algebra.field_vector<"bls12-381.fr">, %arg2: !algebra.field_vector<"bls12-381.fr">, %arg3: !algebra.field<"bls12-381.fr">):
      %0 = "func.call"(%arg0, %arg1, %arg2) <{callee = @zkl_28c1498dbf9d83fc38ed7b21a89d56146297abcbf1ac78968a8b454c9eef5496}> {runtime.site = "s3"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%0)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%1: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %1, %arg3) <{binding = @zkl_binding_13, parameters = [], site = "s5"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>
      "exec.dispatch"(%2)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%3: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%4) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%5: i1):  // pred: ^bb1
      %6 = "exec.returned"(%5) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%6) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.origin = ["s3h676b7211h636865636b5f696e707574", []]} : () -> ()
    "relation.declare"() <{key = "shape", kind = "gkr.circuit/0", purposes = ["parameter", "parameter", "parameter", "parameter", "parameter", "parameter", "parameter"], revision = "0", signature = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, ui64) -> i1, static_arguments = [["field", "bls12-381.fr"], ["nat", "4"], ["nat", "4"]], sym_name = "zkl_cb1c10731e59161b14394fbb472272285b0bbba78877994f53fa6955497a3df4"}> : () -> ()
    "relation.declare"() <{key = "outputs", kind = "gkr.circuit/0", purposes = ["parameter", "parameter", "parameter", "parameter", "parameter", "parameter", "statement"], revision = "0", signature = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> i1, static_arguments = [["field", "bls12-381.fr"]], sym_name = "zkl_5effead4fa609f078c405b9340f603e2dc77b3e9155c76d7032b9f0b55bf1801"}> : () -> ()
    "relation.declare"() <{formula = @zkf_029bdd6bcc5b1485783f1674f8c6e15543fd2d268649f211eab729158162c828, key = "zkl_30326558223483c2b755cae1fef2fb9e26e5ee8894b87d6977fe6482997b20fd", kind = "zkc.language.formula/0", purposes = ["parameter", "parameter", "parameter", "parameter"], revision = "356b4e5222ba84c3f455118496c4a98fd85955480cae336a51f23e9e0c22f461", signature = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> i1, static_arguments = [], sym_name = "zkl_30326558223483c2b755cae1fef2fb9e26e5ee8894b87d6977fe6482997b20fd"}> : () -> ()
    "relation.declare"() <{key = "residual", kind = "gkr.rounds/0", purposes = ["parameter", "parameter", "parameter", "parameter", "statement", "statement"], revision = "0", signature = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, static_arguments = [["field", "bls12-381.fr"]], sym_name = "zkl_e276fa0fd61d1145b2034d7e5681d41484daeb4a120f83771eba638587b04670"}> : () -> ()
    "relation.declare"() <{formula = @zkf_d1b83b15191b85497fc6003ecffb377b2ff71a9228a1114a266874f0ba672708, key = "zkl_cb10975ebbde52f87ba3f031d71fbab61676c0ccc3b05423f90b82c03f36e3ff", kind = "zkc.language.formula/0", purposes = ["parameter", "statement", "statement"], revision = "0c44c9140dc602a623f722acece957ea0790f0e9a18a3ad91082036af55b4a83", signature = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, static_arguments = [], sym_name = "zkl_cb10975ebbde52f87ba3f031d71fbab61676c0ccc3b05423f90b82c03f36e3ff"}> : () -> ()
  }) : () -> ()
}) : () -> ()

