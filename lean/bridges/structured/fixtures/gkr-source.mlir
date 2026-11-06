"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>, source_declarations = [[[["nominal", "record", "gkr::LayerClaim", [["field", "bls12-381.fr"]]], "linear", false, [["point", ["builtin", "vector", [["field", "bls12-381.fr"]]], unit], ["value", ["field", "bls12-381.fr"], unit]], [], "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb"], [["nominal", "record", "gkr::Gates", [["field", "bls12-381.fr"]]], "ordinary", false, [["add", ["builtin", "vector", [["field", "bls12-381.fr"]]], unit], ["mul", ["builtin", "vector", [["field", "bls12-381.fr"]]], unit], ["left", ["builtin", "vector", [["field", "bls12-381.fr"]]], unit], ["right", ["builtin", "vector", [["field", "bls12-381.fr"]]], unit]], [], unit], [["nominal", "record", "gkr::Pending", [["field", "bls12-381.fr"]]], "linear", false, [["point", ["builtin", "vector", [["field", "bls12-381.fr"]]], unit], ["value", ["field", "bls12-381.fr"], unit]], [], "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1"], [["nominal", "record", "zkc::multilinear::Table", [["field", "bls12-381.fr"]]], "ordinary", false, [["entries", ["builtin", "vector", [["field", "bls12-381.fr"]]], unit], ["dimensions", ["index"], unit], ["columns", ["index"], unit]], [], unit]], [["zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [["inputs", ["builtin", "vector", [["field", "bls12-381.fr"]]], ["role00000000", "role00000001"], 0 : ui64, 1 : ui64, ["data", ["role00000000", "role00000001"]]], ["outputs", ["builtin", "vector", [["field", "bls12-381.fr"]]], ["role00000001"], 1 : ui64, 1 : ui64, ["data", ["role00000001"]]], ["add", ["builtin", "vector", [["field", "bls12-381.fr"]]], ["role00000000", "role00000001"], 2 : ui64, 1 : ui64, ["data", ["role00000000", "role00000001"]]], ["mul", ["builtin", "vector", [["field", "bls12-381.fr"]]], ["role00000000", "role00000001"], 3 : ui64, 1 : ui64, ["data", ["role00000000", "role00000001"]]], ["layers", ["index"], ["role00000000", "role00000001"], 4 : ui64, 1 : ui64, ["data", ["role00000000", "role00000001"]]], ["selector", ["index"], ["role00000000", "role00000001"], 5 : ui64, 1 : ui64, ["data", ["role00000000", "role00000001"]]], ["width", ["index"], ["role00000000", "role00000001"], 6 : ui64, 1 : ui64, ["data", ["role00000000", "role00000001"]]]], [["accepted", ["bool"], ["role00000001"], 0 : ui64, 1 : ui64, ["data", ["role00000001"]]]]], ["zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", [["gates", ["nominal", "record", "gkr::Gates", [["field", "bls12-381.fr"]]], ["role00000000"], 0 : ui64, 4 : ui64, ["data", ["role00000000"]]], ["claim", ["nominal", "record", "gkr::Pending", [["field", "bls12-381.fr"]]], ["role00000001"], 4 : ui64, 3 : ui64, ["data", ["role00000001"]]], ["rounds", ["index"], ["role00000000", "role00000001"], 7 : ui64, 1 : ui64, ["data", ["role00000000", "role00000001"]]]], [["point", ["builtin", "vector", [["field", "bls12-381.fr"]]], ["role00000000"], 0 : ui64, 1 : ui64, ["data", ["role00000000"]]], ["residual", ["nominal", "record", "gkr::Gates", [["field", "bls12-381.fr"]]], ["role00000000"], 1 : ui64, 4 : ui64, ["data", ["role00000000"]]], ["evaluation", ["nominal", "record", "gkr::Pending", [["field", "bls12-381.fr"]]], ["role00000001"], 5 : ui64, 3 : ui64, ["data", ["role00000001"]]]]], ["zkl_9719be65739d901a935dbaa0f3f8323a785562f7eee1e60cc8c8c9676f8fdb55", [["values", ["builtin", "vector", [["field", "bls12-381.fr"]]], ["role00000000"], 0 : ui64, 1 : ui64, ["data", ["role00000000"]]], ["claim", ["nominal", "record", "gkr::LayerClaim", [["field", "bls12-381.fr"]]], ["role00000000"], 1 : ui64, 3 : ui64, ["data", ["role00000000"]]]], [["accepted", ["bool"], ["role00000000"], 0 : ui64, 1 : ui64, ["data", ["role00000000"]]]]]], [["gkr::Gates", "6ddc0551ee91854f1eb8d67f26c10c4f82d64d3556a5e69c7fa7c90edbd3ac8e"], ["gkr::LayerClaim", "6ddc0551ee91854f1eb8d67f26c10c4f82d64d3556a5e69c7fa7c90edbd3ac8e"], ["gkr::Pending", "6ddc0551ee91854f1eb8d67f26c10c4f82d64d3556a5e69c7fa7c90edbd3ac8e"], ["zkc::multilinear::Table", "8aa28c4604470c28369b6893e2527323f693924f66cd54f1701edee86bd6bf62"]]]}> ({
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "field.equal", function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>, implementation = "", sym_name = "zkl_binding_18"}> : () -> ()
    "runtime.binding"() <{arguments = ["zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb"], contract = "resource_unit.consume", function_type = (!runtime.scope, !runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">) -> !exec.outcome<>, implementation = "", sym_name = "zkl_binding_17"}> : () -> ()
    "runtime.binding"() <{arguments = ["zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb"], contract = "resource_unit.pass", function_type = (!runtime.scope, !runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">)>, implementation = "", sym_name = "zkl_binding_16"}> : () -> ()
    "runtime.binding"() <{arguments = ["zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1"], contract = "resource_unit.consume", function_type = (!runtime.scope, !runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">) -> !exec.outcome<>, implementation = "", sym_name = "zkl_binding_15"}> : () -> ()
    "runtime.binding"() <{arguments = ["zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1"], contract = "resource_unit.create", function_type = (!runtime.scope) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">)>, implementation = "", sym_name = "zkl_binding_14"}> : () -> ()
    "runtime.binding"() <{arguments = ["zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb"], contract = "resource_unit.create", function_type = (!runtime.scope) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">)>, implementation = "", sym_name = "zkl_binding_13"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.split", function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>, implementation = "", sym_name = "zkl_binding_12"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.sub", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_11"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.sum", function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, implementation = "", sym_name = "zkl_binding_10"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.append", function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, implementation = "", sym_name = "zkl_binding_9"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.empty", function_type = (!runtime.scope) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, implementation = "", sym_name = "zkl_binding_8"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.add", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_7"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.mul", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_6"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.div", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_5"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.equal", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>, implementation = "", sym_name = "zkl_binding_4"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.mod", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_3"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.length", function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_2"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.constant", function_type = (!runtime.scope) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_1"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.less", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>, implementation = "", sym_name = "zkl_binding_0"}> : () -> ()
    "protocol.func"() <{contracts = [["input", "shape", [@zkl_cb1c10731e59161b14394fbb472272285b0bbba78877994f53fa6955497a3df4, [["input", 0, "role00000001"], ["input", 1, "role00000001"], ["input", 2, "role00000001"], ["input", 3, "role00000001"], ["input", 4, "role00000001"], ["input", 5, "role00000001"], ["input", 6, "role00000001"]]], unit, unit], ["target", "circuit_outputs", [@zkl_5effead4fa609f078c405b9340f603e2dc77b3e9155c76d7032b9f0b55bf1801, [["input", 0, "role00000001"], ["input", 2, "role00000001"], ["input", 3, "role00000001"], ["input", 4, "role00000001"], ["input", 5, "role00000001"], ["input", 6, "role00000001"], ["input", 1, "role00000001"]]], unit, ["output", 0, "role00000001"]]], function_type = (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, ui64, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> i1, input_roles = [["role00000000", "role00000001"], ["role00000001"], ["role00000000", "role00000001"], ["role00000000", "role00000001"], ["role00000000", "role00000001"], ["role00000000", "role00000001"], ["role00000000", "role00000001"], ["role00000001"]], origin = ["gkr::Gkr", [["F", ["field", "bls12-381.fr"]], ["MaxLayers", ["nat", "4"]], ["MaxWidth", ["nat", "4"]]]], output_roles = [["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2"}> ({
    ^bb0(%arg494: !data.field_vector<"bls12-381.fr">, %arg495: !data.field_vector<"bls12-381.fr">, %arg496: !data.field_vector<"bls12-381.fr">, %arg497: !data.field_vector<"bls12-381.fr">, %arg498: ui64, %arg499: ui64, %arg500: ui64, %arg501: !protocol.service_ref<"random.bls12-381.fr/0">):
      %1182 = "data.index"() <{value = 4 : ui64}> : () -> ui64
      %1183 = "protocol.local_call"(%1182, %arg500) <{callee = @s3h7a6b637h696e64696365734h6c657373, role = "role00000001", site = "s1"}> : (ui64, ui64) -> i1
      %1184 = "arith.constant"() <{value = false}> : () -> i1
      %1185 = "arith.cmpi"(%1183, %1184) <{predicate = 0 : i64}> : (i1, i1) -> i1
      "protocol.guard"(%1185) <{owner = "role00000001", site = "s4"}> : (i1) -> ()
      %1186 = "data.index"() <{value = 4 : ui64}> : () -> ui64
      %1187 = "protocol.local_call"(%1186, %arg498) <{callee = @s3h7a6b637h696e64696365734h6c657373, role = "role00000001", site = "s6"}> : (ui64, ui64) -> i1
      %1188 = "arith.constant"() <{value = false}> : () -> i1
      %1189 = "arith.cmpi"(%1187, %1188) <{predicate = 0 : i64}> : (i1, i1) -> i1
      "protocol.guard"(%1189) <{owner = "role00000001", site = "s9"}> : (i1) -> ()
      %1190 = "data.index"() <{value = 1 : ui64}> : () -> ui64
      %1191 = "protocol.local_call"(%arg494, %arg500, %1190) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655, role = "role00000001", site = "s11"}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> i1
      "protocol.guard"(%1191) <{owner = "role00000001", site = "s12"}> : (i1) -> ()
      %1192 = "data.index"() <{value = 1 : ui64}> : () -> ui64
      %1193 = "protocol.local_call"(%arg495, %arg500, %1192) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655, role = "role00000001", site = "s14"}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> i1
      "protocol.guard"(%1193) <{owner = "role00000001", site = "s15"}> : (i1) -> ()
      %1194 = "protocol.local_call"(%arg499, %arg500) <{callee = @s3h7a6b637h7072656c7564659h696e6465785f616464, role = "role00000001", site = "s16"}> : (ui64, ui64) -> ui64
      %1195 = "protocol.local_call"(%1194, %arg500) <{callee = @s3h7a6b637h7072656c7564659h696e6465785f616464, role = "role00000001", site = "s17"}> : (ui64, ui64) -> ui64
      %1196 = "protocol.local_call"(%1195, %arg500) <{callee = @s3h7a6b637h7072656c7564659h696e6465785f616464, role = "role00000001", site = "s18"}> : (ui64, ui64) -> ui64
      %1197 = "data.index"() <{value = 1 : ui64}> : () -> ui64
      %1198 = "protocol.local_call"(%arg496, %1196, %1197) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655, role = "role00000001", site = "s20"}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> i1
      "protocol.guard"(%1198) <{owner = "role00000001", site = "s21"}> : (i1) -> ()
      %1199 = "protocol.local_call"(%arg499, %arg500) <{callee = @s3h7a6b637h7072656c7564659h696e6465785f616464, role = "role00000001", site = "s22"}> : (ui64, ui64) -> ui64
      %1200 = "protocol.local_call"(%1199, %arg500) <{callee = @s3h7a6b637h7072656c7564659h696e6465785f616464, role = "role00000001", site = "s23"}> : (ui64, ui64) -> ui64
      %1201 = "protocol.local_call"(%1200, %arg500) <{callee = @s3h7a6b637h7072656c7564659h696e6465785f616464, role = "role00000001", site = "s24"}> : (ui64, ui64) -> ui64
      %1202 = "data.index"() <{value = 1 : ui64}> : () -> ui64
      %1203 = "protocol.local_call"(%arg497, %1201, %1202) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655, role = "role00000001", site = "s26"}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> i1
      "protocol.guard"(%1203) <{owner = "role00000001", site = "s27"}> : (i1) -> ()
      %1204 = "protocol.local_call"(%arg499) <{callee = @s3h676b7212h706f7765725f6f665f74776f, role = "role00000001", site = "s28"}> : (ui64) -> ui64
      %1205 = "protocol.local_call"(%1204, %arg498) <{callee = @s3h7a6b637h696e64696365734h6c657373, role = "role00000001", site = "s29"}> : (ui64, ui64) -> i1
      %1206 = "arith.constant"() <{value = false}> : () -> i1
      %1207 = "arith.cmpi"(%1205, %1206) <{predicate = 0 : i64}> : (i1, i1) -> i1
      "protocol.guard"(%1207) <{owner = "role00000001", site = "s32"}> : (i1) -> ()
      %1208 = "protocol.local_call"() <{callee = @zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f, role = "role00000001", site = "s33"}> : () -> !data.field_vector<"bls12-381.fr">
      %1209 = "protocol.local_call"() <{callee = @zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f, role = "role00000000", site = "s35"}> : () -> !data.field_vector<"bls12-381.fr">
      %1210:2 = "protocol.repeat"(%arg500, %1208, %1209, %arg501) <{carried = 2 : i64, carried_roles = [["role00000001"], ["role00000000"]], maximum = 4 : i64, roles = ["role00000000", "role00000001"], site = "s37"}> ({
      ^bb0(%arg517: ui64, %arg518: !data.field_vector<"bls12-381.fr">, %arg519: !data.field_vector<"bls12-381.fr">, %arg520: !protocol.service_ref<"random.bls12-381.fr/0">):
        %1255 = "protocol.query"(%arg520) <{method = "draw", owner = "role00000001", site = "label_6f7574707574"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
        %1256 = "protocol.exchange"(%1255) <{receiver = "role00000000", sender = "role00000001", site = "label_6f75747075745f64656c6976657279_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1257 = "protocol.restrict_roles"(%1256) <{roles = ["role00000000"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1258 = "protocol.local_call"(%arg518, %1255) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000001", site = "s42"}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !data.field_vector<"bls12-381.fr">
        %1259 = "protocol.local_call"(%arg519, %1257) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000000", site = "s44"}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !data.field_vector<"bls12-381.fr">
        "protocol.yield"(%1258, %1259) : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> ()
      }) : (ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)
      %1211 = "protocol.local_call"(%arg495, %1210#0) <{callee = @zkl_28c1498dbf9d83fc38ed7b21a89d56146297abcbf1ac78968a8b454c9eef5496, role = "role00000001", site = "s48"}> : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %1212:3 = "protocol.local_call"(%1210#0, %1211) <{callee = @zkl_7b9dfa97fa3e158d428459ec12d8a2d5aa171a060ab79f314eeccc53ee772b17, role = "role00000001", site = "s49"}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %1213:4 = "protocol.repeat"(%arg498, %1210#1, %1212#0, %1212#1, %1212#2, %arg494, %arg496, %arg497, %arg498, %arg499, %arg500, %arg501) <{carried = 4 : i64, carried_roles = [["role00000000"], ["role00000001"], ["role00000001"], ["role00000001"]], maximum = 4 : i64, roles = ["role00000000", "role00000001"], site = "s57"}> ({
      ^bb0(%arg502: ui64, %arg503: !data.field_vector<"bls12-381.fr">, %arg504: !runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, %arg505: !data.field_vector<"bls12-381.fr">, %arg506: !algebra.field<"bls12-381.fr">, %arg507: !data.field_vector<"bls12-381.fr">, %arg508: !data.field_vector<"bls12-381.fr">, %arg509: !data.field_vector<"bls12-381.fr">, %arg510: ui64, %arg511: ui64, %arg512: ui64, %arg513: !protocol.service_ref<"random.bls12-381.fr/0">):
        %1215:5 = "protocol.local_call"(%arg504, %arg505, %arg506) <{callee = @zkl_e0f7a4e58ae24eb13e9b2033c42c179b2766ff6cdb4ae1470bf7ef9b1721d646, role = "role00000001", site = "s58"}> : (!runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %1216 = "protocol.local_call"(%arg508, %arg509, %arg507, %arg510, %arg511, %arg512, %arg502) <{callee = @zkl_8c63ad97d926a7762c597860addde408bcd2077ea9cda1b99df123dc13e64af6, role = "role00000000", site = "s62"}> : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, ui64, ui64, ui64) -> !data.field_vector<"bls12-381.fr">
        %1217 = "protocol.local_call"(%arg508, %arg502, %arg511) <{callee = @zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e, role = "role00000000", site = "s64"}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !data.field_vector<"bls12-381.fr">
        %1218 = "protocol.local_call"(%arg509, %arg502, %arg511) <{callee = @zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e, role = "role00000000", site = "s65"}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !data.field_vector<"bls12-381.fr">
        %1219:4 = "protocol.local_call"(%1217, %1218, %arg503, %1216, %arg512) <{callee = @zkl_d1f2756b99b17aad26e4b85a966eec4c9419609618b22e3ee7f8a3349cb1e33b, role = "role00000000", site = "s66"}> : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64) -> (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)
        %1220:3 = "protocol.local_call"(%1215#4) <{callee = @zkl_e1405e1bb4604e60f337203132c746492bf7c31b55302426ae19c2c021c2da1a, role = "role00000001", site = "s69"}> : (!algebra.field<"bls12-381.fr">) -> (!runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %1221:8 = "protocol.apply"(%1219#0, %1219#1, %1219#2, %1219#3, %1220#0, %1220#1, %1220#2, %arg512, %arg513) <{callee = @zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba, roles = ["role00000000", "role00000001"], site = "label_6c656674"}> : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %1222:8 = "protocol.apply"(%1221#1, %1221#2, %1221#3, %1221#4, %1221#5, %1221#6, %1221#7, %arg512, %arg513) <{callee = @zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba, roles = ["role00000000", "role00000001"], site = "label_7269676874"}> : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %1223:2 = "protocol.local_call"(%1222#5, %1222#6, %1222#7) <{callee = @zkl_bd4f0d76e787de675c5732a4a96fc396d45486f32b3dcda5182ccc324969c825, role = "role00000001", site = "s78"}> : (!runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %1224:2 = "protocol.local_call"(%1223#0) <{callee = @zkl_cfcf40daaab145a916368cf7a01eccd9ba0e536fbbc30a06c4a25e7ec96ecbe7, role = "role00000001", site = "s81"}> : (!data.field_vector<"bls12-381.fr">) -> (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)
        %1225 = "protocol.local_call"(%1216, %1221#0, %1222#0, %arg512) <{callee = @zkl_91fe8ea73b5db3432f90fc8fe9725c8455fce8782b4cc4d2839d05826de71b8f, role = "role00000000", site = "s83"}> : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64) -> !data.field_vector<"bls12-381.fr">
        %1226 = "data.index"() <{value = 0 : ui64}> : () -> ui64
        %1227 = "protocol.local_call"(%1225, %1226) <{callee = @zkl_6ba53ec68a0230031d706e4a93e78f80425c51108d34ecc0a5aa5681eded9c8e, role = "role00000000", site = "s86"}> : (!data.field_vector<"bls12-381.fr">, ui64) -> !algebra.field<"bls12-381.fr">
        %1228 = "protocol.exchange"(%1227) <{receiver = "role00000001", sender = "role00000000", site = "label_6c696e655f636f6e7374616e74_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1229 = "protocol.restrict_roles"(%1228) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1230 = "protocol.local_call"() <{callee = @zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f, role = "role00000001", site = "s89"}> : () -> !data.field_vector<"bls12-381.fr">
        %1231 = "protocol.local_call"(%1230, %1229) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000001", site = "s90"}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !data.field_vector<"bls12-381.fr">
        %1232 = "protocol.repeat"(%arg512, %1231, %1225) <{carried = 1 : i64, carried_roles = [["role00000001"]], maximum = 4 : i64, roles = ["role00000000", "role00000001"], site = "s93"}> ({
        ^bb0(%arg514: ui64, %arg515: !data.field_vector<"bls12-381.fr">, %arg516: !data.field_vector<"bls12-381.fr">):
          %1251 = "protocol.local_call"(%arg516, %arg514) <{callee = @zkl_ca5df6081733f8afff4ae42147eb8eba3338d5a96600a7155f619346f19e4b47, role = "role00000000", site = "s94"}> : (!data.field_vector<"bls12-381.fr">, ui64) -> !algebra.field<"bls12-381.fr">
          %1252 = "protocol.exchange"(%1251) <{receiver = "role00000001", sender = "role00000000", site = "label_6c696e655f636f656666696369656e74_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
          %1253 = "protocol.restrict_roles"(%1252) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
          %1254 = "protocol.local_call"(%arg515, %1253) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000001", site = "s97"}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !data.field_vector<"bls12-381.fr">
          "protocol.yield"(%1254) : (!data.field_vector<"bls12-381.fr">) -> ()
        }) : (ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !data.field_vector<"bls12-381.fr">
        %1233 = "protocol.local_call"(%1232) <{callee = @zkl_6ec6b9d6cb41b6bf4ef8e898ba1b283d099252f7de2db0b173f26714e3a46216, role = "role00000001", site = "s101"}> : (!data.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1234 = "protocol.local_call"(%arg508, %arg502, %arg511) <{callee = @zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e, role = "role00000001", site = "s103"}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !data.field_vector<"bls12-381.fr">
        %1235 = "protocol.local_call"(%1234, %1215#3, %1224#0, %1224#1) <{callee = @zkl_161d519d8d5fe2674feddb6e6d14269c9cca82ff216b6b3205ade46cc8b8d35f, role = "role00000001", site = "s107"}> : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1236 = "protocol.local_call"(%arg509, %arg502, %arg511) <{callee = @zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e, role = "role00000001", site = "s109"}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !data.field_vector<"bls12-381.fr">
        %1237 = "protocol.local_call"(%1236, %1215#3, %1224#0, %1224#1) <{callee = @zkl_161d519d8d5fe2674feddb6e6d14269c9cca82ff216b6b3205ade46cc8b8d35f, role = "role00000001", site = "s113"}> : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1238 = "algebra.field_add"(%1229, %1233) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1239 = "algebra.field_multiply"(%1235, %1238) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1240 = "algebra.field_multiply"(%1237, %1229) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1241 = "algebra.field_multiply"(%1240, %1233) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1242 = "algebra.field_add"(%1239, %1241) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1243 = "algebra.field_equal"(%1223#1, %1242) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
        "protocol.guard"(%1243) <{owner = "role00000001", site = "s122"}> : (i1) -> ()
        %1244 = "protocol.query"(%arg513) <{method = "draw", owner = "role00000001", site = "label_6c696e655f6368616c6c656e6765"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
        %1245 = "protocol.exchange"(%1244) <{receiver = "role00000000", sender = "role00000001", site = "label_6c696e655f64656c6976657279_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1246 = "protocol.restrict_roles"(%1245) <{roles = ["role00000000"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1247 = "protocol.local_call"(%1224#0, %1224#1, %1244) <{callee = @zkl_1f2e31017a1a0403a56241b1d83eac39d1ecc40b298cd066516f78ae9c5b3434, role = "role00000001", site = "s130"}> : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !data.field_vector<"bls12-381.fr">
        %1248 = "protocol.local_call"(%1232, %1244) <{callee = @zkl_21465134b1aa848c616c790eff1907b1a442ba76730b77da2be48acd923d6ff7, role = "role00000001", site = "s131"}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1249:3 = "protocol.local_call"(%1215#0, %1215#1, %1215#2, %1247, %1248) <{callee = @zkl_744f32fd2e4e542d6467fe3f764e183881171708947eb2bd852cea6f32a0407e, role = "role00000001", site = "s132"}> : (!runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %1250 = "protocol.local_call"(%1221#0, %1222#0, %1246) <{callee = @zkl_1f2e31017a1a0403a56241b1d83eac39d1ecc40b298cd066516f78ae9c5b3434, role = "role00000000", site = "s134"}> : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !data.field_vector<"bls12-381.fr">
        "protocol.yield"(%1250, %1249#0, %1249#1, %1249#2) : (!data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
      }) : (ui64, !data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, ui64, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %1214 = "protocol.apply"(%arg494, %1213#1, %1213#2, %1213#3) <{callee = @zkl_9719be65739d901a935dbaa0f3f8323a785562f7eee1e60cc8c8c9676f8fdb55, roles = ["role00000001"], site = "label_696e707574"}> : (!data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "protocol.return"(%1214) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "s3h7a6b637h696e64696365734h6c657373", sym_visibility = "private"}> ({
    ^bb0(%arg491: !runtime.scope, %arg492: ui64, %arg493: ui64):
      %1177 = "exec.apply"(%arg491, %arg492, %arg493) <{binding = @zkl_binding_0, parameters = [], site = "s0"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1177)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1178: i1):  // pred: ^bb0
      %1179 = "exec.returned"(%1178) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%1179) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%1180: !exec.stop):  // pred: ^bb0
      %1181 = "exec.failed"(%1180) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%1181) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.origin = ["s3h7a6b637h696e64696365734h6c657373", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", sym_visibility = "private"}> ({
    ^bb0(%arg487: !runtime.scope, %arg488: !data.field_vector<"bls12-381.fr">, %arg489: ui64, %arg490: ui64):
      %1119 = "exec.apply"(%arg487) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1119)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1120: ui64):  // pred: ^bb0
      %1121 = "func.call"(%arg487, %1120, %arg490) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s1"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1121)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%1122: !exec.stop):  // 23 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12, ^bb15, ^bb16, ^bb17, ^bb18, ^bb19, ^bb21, ^bb22, ^bb25, ^bb26, ^bb28, ^bb29, ^bb31, ^bb32
      %1123 = "exec.failed"(%1122) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%1123) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%1124: i1):  // pred: ^bb1
      %1125 = "exec.test"(%arg487, %1124) <{site = "s3"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1125)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb4(%1126: i1):  // pred: ^bb3
      "cf.cond_br"(%1126)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %1127 = "runtime.enter_scope"(%arg487, %arg489) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "then", site = "s3"}> : (!runtime.scope, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1127)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %1128 = "runtime.enter_scope"(%arg487, %arg489) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "else", site = "s3"}> : (!runtime.scope, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1128)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7(%1129: i1):  // 2 preds: ^bb10, ^bb13
      %1130 = "exec.test"(%arg487, %1129) <{site = "s11"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1130)[^bb14, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb8(%1131: !runtime.scope):  // pred: ^bb5
      %1132 = "func.call"(%1131, %arg489) <{callee = @zkl_control_0}> : (!runtime.scope, ui64) -> !exec.outcome<(i1)>
      %1133 = "runtime.exit_scope"(%1131, %1132) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%1133)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb9(%1134: !runtime.transfer<(i1)>):  // pred: ^bb8
      %1135 = "runtime.accept_transfer"(%arg487, %1134) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1135)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb10(%1136: i1):  // pred: ^bb9
      "cf.br"(%1136)[^bb7] : (i1) -> ()
    ^bb11(%1137: !runtime.scope):  // pred: ^bb6
      %1138 = "func.call"(%1137, %arg489) <{callee = @zkl_control_1}> : (!runtime.scope, ui64) -> !exec.outcome<(i1)>
      %1139 = "runtime.exit_scope"(%1137, %1138) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%1139)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb12(%1140: !runtime.transfer<(i1)>):  // pred: ^bb11
      %1141 = "runtime.accept_transfer"(%arg487, %1140) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1141)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb13(%1142: i1):  // pred: ^bb12
      "cf.br"(%1142)[^bb7] : (i1) -> ()
    ^bb14(%1143: i1):  // pred: ^bb7
      "cf.cond_br"(%1143)[^bb15, ^bb16] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb15:  // pred: ^bb14
      %1144 = "runtime.enter_scope"(%arg487, %arg488, %arg490) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "then", site = "s11"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1144)[^bb18, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb16:  // pred: ^bb14
      %1145 = "runtime.enter_scope"(%arg487, %arg488, %arg490) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "else", site = "s11"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1145)[^bb21, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb17(%1146: i1):  // 2 preds: ^bb20, ^bb23
      %1147 = "exec.test"(%arg487, %1146) <{site = "s22"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1147)[^bb24, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb18(%1148: !runtime.scope):  // pred: ^bb15
      %1149 = "func.call"(%1148, %arg488, %arg490) <{callee = @zkl_control_2}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>
      %1150 = "runtime.exit_scope"(%1148, %1149) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%1150)[^bb19, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb19(%1151: !runtime.transfer<(i1)>):  // pred: ^bb18
      %1152 = "runtime.accept_transfer"(%arg487, %1151) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1152)[^bb20, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb20(%1153: i1):  // pred: ^bb19
      "cf.br"(%1153)[^bb17] : (i1) -> ()
    ^bb21(%1154: !runtime.scope):  // pred: ^bb16
      %1155 = "func.call"(%1154, %arg488, %arg490) <{callee = @zkl_control_3}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>
      %1156 = "runtime.exit_scope"(%1154, %1155) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%1156)[^bb22, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb22(%1157: !runtime.transfer<(i1)>):  // pred: ^bb21
      %1158 = "runtime.accept_transfer"(%arg487, %1157) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1158)[^bb23, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb23(%1159: i1):  // pred: ^bb22
      "cf.br"(%1159)[^bb17] : (i1) -> ()
    ^bb24(%1160: i1):  // pred: ^bb17
      "cf.cond_br"(%1160)[^bb25, ^bb26] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb25:  // pred: ^bb24
      %1161 = "runtime.enter_scope"(%arg487, %arg488, %arg489, %arg490) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "then", site = "s22"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1161)[^bb28, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb26:  // pred: ^bb24
      %1162 = "runtime.enter_scope"(%arg487, %arg488, %arg489, %arg490) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "else", site = "s22"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1162)[^bb31, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb27(%1163: i1):  // 2 preds: ^bb30, ^bb33
      %1164 = "exec.returned"(%1163) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%1164) : (!exec.outcome<(i1)>) -> ()
    ^bb28(%1165: !runtime.scope):  // pred: ^bb25
      %1166 = "func.call"(%1165, %arg488, %arg489, %arg490) <{callee = @zkl_control_4}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      %1167 = "runtime.exit_scope"(%1165, %1166) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%1167)[^bb29, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb29(%1168: !runtime.transfer<(i1)>):  // pred: ^bb28
      %1169 = "runtime.accept_transfer"(%arg487, %1168) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1169)[^bb30, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb30(%1170: i1):  // pred: ^bb29
      "cf.br"(%1170)[^bb27] : (i1) -> ()
    ^bb31(%1171: !runtime.scope):  // pred: ^bb26
      %1172 = "func.call"(%1171, %arg488, %arg489, %arg490) <{callee = @zkl_control_5}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      %1173 = "runtime.exit_scope"(%1171, %1172) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%1173)[^bb32, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb32(%1174: !runtime.transfer<(i1)>):  // pred: ^bb31
      %1175 = "runtime.accept_transfer"(%arg487, %1174) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1175)[^bb33, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb33(%1176: i1):  // pred: ^bb32
      "cf.br"(%1176)[^bb27] : (i1) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_0", sym_visibility = "private"}> ({
    ^bb0(%arg485: !runtime.scope, %arg486: ui64):
      %1112 = "exec.apply"(%arg485) <{binding = @zkl_binding_1, parameters = [64 : ui64], site = "s4"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1112)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1113: ui64):  // pred: ^bb0
      %1114 = "func.call"(%arg485, %arg486, %1113) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s5"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1114)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%1115: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %1116 = "exec.failed"(%1115) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%1116) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%1117: i1):  // pred: ^bb1
      %1118 = "exec.complete"(%arg485, %1117) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%1118) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_1", sym_visibility = "private"}> ({
    ^bb0(%arg483: !runtime.scope, %arg484: ui64):
      %1107 = "exec.boolean"(%arg483) <{site = "s7", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1107)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1108: i1):  // pred: ^bb0
      %1109 = "exec.complete"(%arg483, %1108) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%1109) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%1110: !exec.stop):  // pred: ^bb0
      %1111 = "exec.failed"(%1110) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%1111) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_2", sym_visibility = "private"}> ({
    ^bb0(%arg480: !runtime.scope, %arg481: !data.field_vector<"bls12-381.fr">, %arg482: ui64):
      %1096 = "exec.apply"(%arg480, %arg481) <{binding = @zkl_binding_2, parameters = [], site = "s12"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1096)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1097: ui64):  // pred: ^bb0
      %1098 = "exec.apply"(%arg480, %1097, %arg482) <{binding = @zkl_binding_3, parameters = [], site = "s13"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1098)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%1099: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %1100 = "exec.failed"(%1099) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%1100) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%1101: ui64):  // pred: ^bb1
      %1102 = "exec.apply"(%arg480) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s14"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1102)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%1103: ui64):  // pred: ^bb3
      %1104 = "exec.apply"(%arg480, %1101, %1103) <{binding = @zkl_binding_4, parameters = [], site = "s15"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1104)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb5(%1105: i1):  // pred: ^bb4
      %1106 = "exec.complete"(%arg480, %1105) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%1106) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_3", sym_visibility = "private"}> ({
    ^bb0(%arg477: !runtime.scope, %arg478: !data.field_vector<"bls12-381.fr">, %arg479: ui64):
      %1091 = "exec.boolean"(%arg477) <{site = "s17", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1091)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1092: i1):  // pred: ^bb0
      %1093 = "exec.complete"(%arg477, %1092) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%1093) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%1094: !exec.stop):  // pred: ^bb0
      %1095 = "exec.failed"(%1094) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%1095) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_4", sym_visibility = "private"}> ({
    ^bb0(%arg473: !runtime.scope, %arg474: !data.field_vector<"bls12-381.fr">, %arg475: ui64, %arg476: ui64):
      %1080 = "exec.apply"(%arg473, %arg474) <{binding = @zkl_binding_2, parameters = [], site = "s23"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1080)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1081: ui64):  // pred: ^bb0
      %1082 = "exec.apply"(%arg473, %1081, %arg476) <{binding = @zkl_binding_5, parameters = [], site = "s24"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1082)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%1083: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %1084 = "exec.failed"(%1083) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%1084) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%1085: ui64):  // pred: ^bb1
      %1086 = "func.call"(%arg473, %arg475) <{callee = @s3h7a6b6311h6d756c74696c696e6561724h726f7773}> {runtime.site = "s25"} : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1086)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%1087: ui64):  // pred: ^bb3
      %1088 = "exec.apply"(%arg473, %1085, %1087) <{binding = @zkl_binding_4, parameters = [], site = "s26"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1088)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb5(%1089: i1):  // pred: ^bb4
      %1090 = "exec.complete"(%arg473, %1089) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%1090) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_5", sym_visibility = "private"}> ({
    ^bb0(%arg469: !runtime.scope, %arg470: !data.field_vector<"bls12-381.fr">, %arg471: ui64, %arg472: ui64):
      %1075 = "exec.boolean"(%arg469) <{site = "s28", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1075)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1076: i1):  // pred: ^bb0
      %1077 = "exec.complete"(%arg469, %1076) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%1077) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%1078: !exec.stop):  // pred: ^bb0
      %1079 = "exec.failed"(%1078) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%1079) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "s3h7a6b6311h6d756c74696c696e6561724h726f7773", sym_visibility = "private"}> ({
    ^bb0(%arg467: !runtime.scope, %arg468: ui64):
      %1028 = "exec.apply"(%arg467) <{binding = @zkl_binding_1, parameters = [64 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1028)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1029: ui64):  // pred: ^bb0
      %1030 = "func.call"(%arg467, %arg468, %1029) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s1"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1030)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%1031: !exec.stop):  // 14 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12, ^bb14, ^bb15, ^bb19, ^bb21
      %1032 = "exec.failed"(%1031) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%1032) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%1033: i1):  // pred: ^bb1
      %1034 = "exec.test"(%arg467, %1033) <{site = "s2"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1034)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb4(%1035: i1):  // pred: ^bb3
      "cf.cond_br"(%1035)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %1036 = "runtime.enter_scope"(%arg467) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s2"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1036)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %1037 = "runtime.enter_scope"(%arg467) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s2"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1037)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // 2 preds: ^bb10, ^bb13
      %1038 = "exec.apply"(%arg467) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s3"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1038)[^bb14, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb8(%1039: !runtime.scope):  // pred: ^bb5
      %1040 = "func.call"(%1039) <{callee = @zkl_control_6}> : (!runtime.scope) -> !exec.outcome<>
      %1041 = "runtime.exit_scope"(%1039, %1040) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%1041)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb9(%1042: !runtime.transfer<>):  // pred: ^bb8
      %1043 = "runtime.accept_transfer"(%arg467, %1042) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%1043)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb10:  // pred: ^bb9
      "cf.br"()[^bb7] : () -> ()
    ^bb11(%1044: !runtime.scope):  // pred: ^bb6
      %1045 = "func.call"(%1044) <{callee = @zkl_control_7}> : (!runtime.scope) -> !exec.outcome<>
      %1046 = "runtime.exit_scope"(%1044, %1045) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%1046)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb12(%1047: !runtime.transfer<>):  // pred: ^bb11
      %1048 = "runtime.accept_transfer"(%arg467, %1047) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%1048)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb13:  // pred: ^bb12
      "cf.br"()[^bb7] : () -> ()
    ^bb14(%1049: ui64):  // pred: ^bb7
      %1050 = "exec.apply"(%arg467) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s5"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1050)[^bb15, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb15(%1051: ui64):  // pred: ^bb14
      %1052 = "exec.range"(%arg467, %1051, %arg468) <{site = "s6"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%1052)[^bb16, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i64, i64)>) -> ()
    ^bb16(%1053: i64, %1054: i64):  // pred: ^bb15
      %1055 = "runtime.borrow_transfer"(%arg467, %1049) : (!runtime.scope, ui64) -> !runtime.transfer<(ui64)>
      "cf.br"(%1053, %1055)[^bb17] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb17(%1056: i64, %1057: !runtime.transfer<(ui64)>):  // 2 preds: ^bb16, ^bb20
      %1058 = "arith.cmpi"(%1056, %1054) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%1058, %1057)[^bb18, ^bb19] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(ui64)>) -> ()
    ^bb18:  // pred: ^bb17
      %1059 = "runtime.iteration"(%arg467, %1056) <{site = "s6"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1059)[^bb22, ^bb21] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb19(%1060: !runtime.transfer<(ui64)>):  // pred: ^bb17
      %1061 = "runtime.accept_transfer"(%arg467, %1060) : (!runtime.scope, !runtime.transfer<(ui64)>) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1061)[^bb25, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb20(%1062: !runtime.transfer<(ui64)>):  // pred: ^bb24
      %1063 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %1064 = "arith.addi"(%1056, %1063) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%1064, %1062)[^bb17] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb21(%1065: !exec.stop):  // 3 preds: ^bb18, ^bb22, ^bb23
      "runtime.release_transfer"(%1057) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%1065)[^bb2] : (!exec.stop) -> ()
    ^bb22(%1066: ui64):  // pred: ^bb18
      %1067 = "runtime.transfer_values"(%1057) : (!runtime.transfer<(ui64)>) -> ui64
      %1068 = "runtime.enter_scope"(%arg467, %1056, %1066, %1067) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 2>, site = "s6"}> : (!runtime.scope, i64, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1068)[^bb23, ^bb21] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb23(%1069: !runtime.scope):  // pred: ^bb22
      %1070 = "func.call"(%1069, %1066, %1067) <{callee = @zkl_control_8}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      %1071 = "runtime.exit_scope"(%1069, %1070) : (!runtime.scope, !exec.outcome<(ui64)>) -> !exec.outcome<(!runtime.transfer<(ui64)>)>
      "exec.dispatch"(%1071)[^bb24, ^bb21] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(ui64)>)>) -> ()
    ^bb24(%1072: !runtime.transfer<(ui64)>):  // pred: ^bb23
      "runtime.release_transfer"(%1057) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%1072)[^bb20] : (!runtime.transfer<(ui64)>) -> ()
    ^bb25(%1073: ui64):  // pred: ^bb19
      %1074 = "exec.returned"(%1073) : (ui64) -> !exec.outcome<(ui64)>
      "func.return"(%1074) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561724h726f7773", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_6", sym_visibility = "private"}> ({
    ^bb0(%arg466: !runtime.scope):
      %1027 = "exec.complete"(%arg466) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%1027) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_7", sym_visibility = "private"}> ({
    ^bb0(%arg465: !runtime.scope):
      %1024 = "exec.reject"(%arg465) <{reason = "reject", site = "s2_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%1024)[^bb1] : (!exec.stop) -> ()
    ^bb1(%1025: !exec.stop):  // pred: ^bb0
      %1026 = "exec.failed"(%1025) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%1026) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "zkl_control_8", sym_visibility = "private"}> ({
    ^bb0(%arg462: !runtime.scope, %arg463: ui64, %arg464: ui64):
      %1017 = "exec.apply"(%arg462) <{binding = @zkl_binding_1, parameters = [2 : ui64], site = "s7"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1017)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1018: ui64):  // pred: ^bb0
      %1019 = "exec.apply"(%arg462, %arg464, %1018) <{binding = @zkl_binding_6, parameters = [], site = "s8"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1019)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%1020: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %1021 = "exec.failed"(%1020) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%1021) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%1022: ui64):  // pred: ^bb1
      %1023 = "exec.complete"(%arg462, %1022) : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "func.return"(%1023) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "s3h7a6b637h7072656c7564659h696e6465785f616464", sym_visibility = "private"}> ({
    ^bb0(%arg459: !runtime.scope, %arg460: ui64, %arg461: ui64):
      %1012 = "exec.apply"(%arg459, %arg460, %arg461) <{binding = @zkl_binding_7, parameters = [], site = "s0"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1012)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1013: ui64):  // pred: ^bb0
      %1014 = "exec.returned"(%1013) : (ui64) -> !exec.outcome<(ui64)>
      "func.return"(%1014) : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%1015: !exec.stop):  // pred: ^bb0
      %1016 = "exec.failed"(%1015) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%1016) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b637h7072656c7564659h696e6465785f616464", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "s3h676b7212h706f7765725f6f665f74776f", sym_visibility = "private"}> ({
    ^bb0(%arg457: !runtime.scope, %arg458: ui64):
      %983 = "exec.apply"(%arg457) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%983)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%984: ui64):  // pred: ^bb0
      %985 = "exec.apply"(%arg457) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s2"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%985)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%986: !exec.stop):  // 5 preds: ^bb0, ^bb1, ^bb3, ^bb7, ^bb9
      %987 = "exec.failed"(%986) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%987) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%988: ui64):  // pred: ^bb1
      %989 = "exec.range"(%arg457, %988, %arg458) <{site = "s3"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%989)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i64, i64)>) -> ()
    ^bb4(%990: i64, %991: i64):  // pred: ^bb3
      %992 = "runtime.borrow_transfer"(%arg457, %984) : (!runtime.scope, ui64) -> !runtime.transfer<(ui64)>
      "cf.br"(%990, %992)[^bb5] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb5(%993: i64, %994: !runtime.transfer<(ui64)>):  // 2 preds: ^bb4, ^bb8
      %995 = "arith.cmpi"(%993, %991) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%995, %994)[^bb6, ^bb7] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(ui64)>) -> ()
    ^bb6:  // pred: ^bb5
      %996 = "runtime.iteration"(%arg457, %993) <{site = "s3"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%996)[^bb10, ^bb9] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb7(%997: !runtime.transfer<(ui64)>):  // pred: ^bb5
      %998 = "runtime.accept_transfer"(%arg457, %997) : (!runtime.scope, !runtime.transfer<(ui64)>) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%998)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb8(%999: !runtime.transfer<(ui64)>):  // pred: ^bb12
      %1000 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %1001 = "arith.addi"(%993, %1000) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%1001, %999)[^bb5] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb9(%1002: !exec.stop):  // 3 preds: ^bb6, ^bb10, ^bb11
      "runtime.release_transfer"(%994) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%1002)[^bb2] : (!exec.stop) -> ()
    ^bb10(%1003: ui64):  // pred: ^bb6
      %1004 = "runtime.transfer_values"(%994) : (!runtime.transfer<(ui64)>) -> ui64
      %1005 = "runtime.enter_scope"(%arg457, %993, %1003, %1004) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 2>, site = "s3"}> : (!runtime.scope, i64, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1005)[^bb11, ^bb9] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb11(%1006: !runtime.scope):  // pred: ^bb10
      %1007 = "func.call"(%1006, %1003, %1004) <{callee = @zkl_control_9}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      %1008 = "runtime.exit_scope"(%1006, %1007) : (!runtime.scope, !exec.outcome<(ui64)>) -> !exec.outcome<(!runtime.transfer<(ui64)>)>
      "exec.dispatch"(%1008)[^bb12, ^bb9] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(ui64)>)>) -> ()
    ^bb12(%1009: !runtime.transfer<(ui64)>):  // pred: ^bb11
      "runtime.release_transfer"(%994) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%1009)[^bb8] : (!runtime.transfer<(ui64)>) -> ()
    ^bb13(%1010: ui64):  // pred: ^bb7
      %1011 = "exec.returned"(%1010) : (ui64) -> !exec.outcome<(ui64)>
      "func.return"(%1011) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.origin = ["s3h676b7212h706f7765725f6f665f74776f", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "zkl_control_9", sym_visibility = "private"}> ({
    ^bb0(%arg454: !runtime.scope, %arg455: ui64, %arg456: ui64):
      %976 = "exec.apply"(%arg454) <{binding = @zkl_binding_1, parameters = [2 : ui64], site = "s4"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%976)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%977: ui64):  // pred: ^bb0
      %978 = "exec.apply"(%arg454, %arg456, %977) <{binding = @zkl_binding_6, parameters = [], site = "s5"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%978)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%979: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %980 = "exec.failed"(%979) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%980) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%981: ui64):  // pred: ^bb1
      %982 = "exec.complete"(%arg454, %981) : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "func.return"(%982) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", sym_visibility = "private"}> ({
    ^bb0(%arg453: !runtime.scope):
      %971 = "exec.apply"(%arg453) <{binding = @zkl_binding_8, parameters = [], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%971)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%972: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %973 = "exec.returned"(%972) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%973) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%974: !exec.stop):  // pred: ^bb0
      %975 = "exec.failed"(%974) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%975) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6310h7072696d6974697665736h766563746f725h656d707479", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", sym_visibility = "private"}> ({
    ^bb0(%arg450: !runtime.scope, %arg451: !data.field_vector<"bls12-381.fr">, %arg452: !algebra.field<"bls12-381.fr">):
      %966 = "exec.apply"(%arg450, %arg451, %arg452) <{binding = @zkl_binding_9, parameters = [], site = "s0"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%966)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%967: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %968 = "exec.returned"(%967) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%968) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%969: !exec.stop):  // pred: ^bb0
      %970 = "exec.failed"(%969) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%970) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6310h7072696d6974697665736h766563746f726h617070656e64", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_28c1498dbf9d83fc38ed7b21a89d56146297abcbf1ac78968a8b454c9eef5496", sym_visibility = "private"}> ({
    ^bb0(%arg447: !runtime.scope, %arg448: !data.field_vector<"bls12-381.fr">, %arg449: !data.field_vector<"bls12-381.fr">):
      %947 = "exec.apply"(%arg447, %arg449) <{binding = @zkl_binding_2, parameters = [], site = "s0"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%947)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%948: ui64):  // pred: ^bb0
      %949 = "exec.apply"(%arg447) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s1"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%949)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%950: !exec.stop):  // 6 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6
      %951 = "exec.failed"(%950) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%951) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb3(%952: ui64):  // pred: ^bb1
      %953 = "func.call"(%arg447, %arg448, %948, %952) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a}> {runtime.site = "s2"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%953)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb4(%954: !data.field_vector<"bls12-381.fr">, %955: ui64, %956: ui64):  // pred: ^bb3
      %957 = "func.call"(%arg447, %954, %955, %956, %arg449) <{callee = @zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be}> {runtime.site = "s4"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%957)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb5(%958: !data.field_vector<"bls12-381.fr">, %959: ui64, %960: ui64):  // pred: ^bb4
      %961 = "exec.compute"(%arg447, %958, %959, %960) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33, site = "s5"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%961)[^bb6, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb6(%962: !data.field_vector<"bls12-381.fr">):  // pred: ^bb5
      %963 = "exec.apply"(%arg447, %962) <{binding = @zkl_binding_10, parameters = [], site = "s6"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%963)[^bb7, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb7(%964: !algebra.field<"bls12-381.fr">):  // pred: ^bb6
      %965 = "exec.returned"(%964) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%965) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b728h6576616c75617465", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", sym_visibility = "private"}> ({
    ^bb0(%arg443: !runtime.scope, %arg444: !data.field_vector<"bls12-381.fr">, %arg445: ui64, %arg446: ui64):
      %928 = "func.call"(%arg443, %arg444, %arg445, %arg446) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655}> {runtime.site = "s0"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%928)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%929: i1):  // pred: ^bb0
      %930 = "exec.test"(%arg443, %929) <{site = "s1"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%930)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%931: !exec.stop):  // 8 preds: ^bb0, ^bb1, ^bb4, ^bb5, ^bb7, ^bb8, ^bb10, ^bb11
      %932 = "exec.failed"(%931) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%932) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb3(%933: i1):  // pred: ^bb1
      "cf.cond_br"(%933)[^bb4, ^bb5] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb4:  // pred: ^bb3
      %934 = "runtime.enter_scope"(%arg443) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%934)[^bb7, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb5:  // pred: ^bb3
      %935 = "runtime.enter_scope"(%arg443) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%935)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // 2 preds: ^bb9, ^bb12
      %936 = "exec.returned"(%arg444, %arg445, %arg446) : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%936) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb7(%937: !runtime.scope):  // pred: ^bb4
      %938 = "func.call"(%937) <{callee = @zkl_control_10}> : (!runtime.scope) -> !exec.outcome<>
      %939 = "runtime.exit_scope"(%937, %938) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%939)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb8(%940: !runtime.transfer<>):  // pred: ^bb7
      %941 = "runtime.accept_transfer"(%arg443, %940) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%941)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb9:  // pred: ^bb8
      "cf.br"()[^bb6] : () -> ()
    ^bb10(%942: !runtime.scope):  // pred: ^bb5
      %943 = "func.call"(%942) <{callee = @zkl_control_11}> : (!runtime.scope) -> !exec.outcome<>
      %944 = "runtime.exit_scope"(%942, %943) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%944)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb11(%945: !runtime.transfer<>):  // pred: ^bb10
      %946 = "runtime.accept_transfer"(%arg443, %945) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%946)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb12:  // pred: ^bb11
      "cf.br"()[^bb6] : () -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561725h7461626c65", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_10", sym_visibility = "private"}> ({
    ^bb0(%arg442: !runtime.scope):
      %927 = "exec.complete"(%arg442) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%927) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_11", sym_visibility = "private"}> ({
    ^bb0(%arg441: !runtime.scope):
      %924 = "exec.reject"(%arg441) <{reason = "reject", site = "s1_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%924)[^bb1] : (!exec.stop) -> ()
    ^bb1(%925: !exec.stop):  // pred: ^bb0
      %926 = "exec.failed"(%925) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%926) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be", sym_visibility = "private"}> ({
    ^bb0(%arg436: !runtime.scope, %arg437: !data.field_vector<"bls12-381.fr">, %arg438: ui64, %arg439: ui64, %arg440: !data.field_vector<"bls12-381.fr">):
      %917 = "func.call"(%arg436, %arg437, %arg438, %arg439, %arg440) <{callee = @zkl_f76cda8e28f45b05fc9c2123a0520855404c183a59c052d86cc45895f4878f8b}> {runtime.site = "s0"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%917)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb1(%918: !data.field_vector<"bls12-381.fr">, %919: ui64, %920: ui64):  // pred: ^bb0
      %921 = "exec.returned"(%918, %919, %920) : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%921) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb2(%922: !exec.stop):  // pred: ^bb0
      %923 = "exec.failed"(%922) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%923) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e65617210h6669785f707265666978", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_195a79478f48dffc2a6917273d8317df0fabae786920a46fa2ac6b2737144299", sym_visibility = "private"}> ({
    ^bb0(%arg431: !runtime.scope, %arg432: !data.field_vector<"bls12-381.fr">, %arg433: ui64, %arg434: ui64, %arg435: !algebra.field<"bls12-381.fr">):
      %910 = "func.call"(%arg431, %arg432, %arg433, %arg434, %arg435) <{callee = @zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d}> {runtime.site = "s2"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%910)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb1(%911: !data.field_vector<"bls12-381.fr">, %912: ui64, %913: ui64):  // pred: ^bb0
      %914 = "exec.returned"(%911, %912, %913) : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%914) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb2(%915: !exec.stop):  // pred: ^bb0
      %916 = "exec.failed"(%915) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%916) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["zks_50b2228592370f9a2bce2e71277fbb9bf36d691d6ece4416923708e3a0c063ae", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d", sym_visibility = "private"}> ({
    ^bb0(%arg426: !runtime.scope, %arg427: !data.field_vector<"bls12-381.fr">, %arg428: ui64, %arg429: ui64, %arg430: !algebra.field<"bls12-381.fr">):
      %898 = "func.call"(%arg426, %arg427, %arg428, %arg429) <{callee = @zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087}> {runtime.site = "s0"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%898)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%899: !data.field_vector<"bls12-381.fr">, %900: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %901 = "exec.collect"(%arg426, %899, %900, %arg430) <{body = @zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body, domain = @zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_domain, site = "s4"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%901)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%902: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %903 = "exec.failed"(%902) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%903) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb3(%904: !data.field_vector<"bls12-381.fr">):  // pred: ^bb1
      %905 = "exec.apply"(%arg426) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s7"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%905)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%906: ui64):  // pred: ^bb3
      %907 = "exec.apply"(%arg426, %arg428, %906) <{binding = @zkl_binding_11, parameters = [], site = "s8"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%907)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%908: ui64):  // pred: ^bb4
      %909 = "exec.returned"(%904, %908, %arg429) : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%909) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561729h6669785f6669727374", []]} : () -> ()
    "data.domain"() <{function_type = (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, sym_name = "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_domain", sym_visibility = "private"}> ({
    ^bb0(%arg424: !data.field_vector<"bls12-381.fr">, %arg425: !data.field_vector<"bls12-381.fr">):
      %895 = "data.domain_elements"(%arg424) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %896 = "data.domain_elements"(%arg425) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %897 = "data.domain_zip"(%895, %896) : (!data.domain<!algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%897) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body", sym_visibility = "private"}> ({
    ^bb0(%arg418: !runtime.scope, %arg419: !algebra.field<"bls12-381.fr">, %arg420: !algebra.field<"bls12-381.fr">, %arg421: !data.field_vector<"bls12-381.fr">, %arg422: !data.field_vector<"bls12-381.fr">, %arg423: !algebra.field<"bls12-381.fr">):
      %890 = "exec.compute"(%arg418, %arg419, %arg420, %arg423) <{callee = @zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5, site = "body"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%890)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%891: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %892 = "exec.returned"(%891) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%892) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%893: !exec.stop):  // pred: ^bb0
      %894 = "exec.failed"(%893) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%894) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087", sym_visibility = "private"}> ({
    ^bb0(%arg414: !runtime.scope, %arg415: !data.field_vector<"bls12-381.fr">, %arg416: ui64, %arg417: ui64):
      %866 = "exec.apply"(%arg414) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%866)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%867: ui64):  // pred: ^bb0
      %868 = "func.call"(%arg414, %867, %arg416) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s2"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%868)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%869: !exec.stop):  // 10 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12
      %870 = "exec.failed"(%869) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "func.return"(%870) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%871: i1):  // pred: ^bb1
      %872 = "exec.test"(%arg414, %871) <{site = "s3"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%872)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb4(%873: i1):  // pred: ^bb3
      "cf.cond_br"(%873)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %874 = "runtime.enter_scope"(%arg414) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s3"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%874)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %875 = "runtime.enter_scope"(%arg414) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s3"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%875)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // 2 preds: ^bb10, ^bb13
      %876 = "exec.apply"(%arg414, %arg415) <{binding = @zkl_binding_12, parameters = [], site = "s5"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%876)[^bb14, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%877: !runtime.scope):  // pred: ^bb5
      %878 = "func.call"(%877) <{callee = @zkl_control_12}> : (!runtime.scope) -> !exec.outcome<>
      %879 = "runtime.exit_scope"(%877, %878) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%879)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb9(%880: !runtime.transfer<>):  // pred: ^bb8
      %881 = "runtime.accept_transfer"(%arg414, %880) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%881)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb10:  // pred: ^bb9
      "cf.br"()[^bb7] : () -> ()
    ^bb11(%882: !runtime.scope):  // pred: ^bb6
      %883 = "func.call"(%882) <{callee = @zkl_control_13}> : (!runtime.scope) -> !exec.outcome<>
      %884 = "runtime.exit_scope"(%882, %883) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%884)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb12(%885: !runtime.transfer<>):  // pred: ^bb11
      %886 = "runtime.accept_transfer"(%arg414, %885) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%886)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb13:  // pred: ^bb12
      "cf.br"()[^bb7] : () -> ()
    ^bb14(%887: !data.field_vector<"bls12-381.fr">, %888: !data.field_vector<"bls12-381.fr">):  // pred: ^bb7
      %889 = "exec.returned"(%887, %888) : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "func.return"(%889) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561726h68616c766573", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_12", sym_visibility = "private"}> ({
    ^bb0(%arg413: !runtime.scope):
      %865 = "exec.complete"(%arg413) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%865) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_13", sym_visibility = "private"}> ({
    ^bb0(%arg412: !runtime.scope):
      %862 = "exec.reject"(%arg412) <{reason = "reject", site = "s3_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%862)[^bb1] : (!exec.stop) -> ()
    ^bb1(%863: !exec.stop):  // pred: ^bb0
      %864 = "exec.failed"(%863) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%864) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5", sym_visibility = "private"}> ({
    ^bb0(%arg409: !algebra.field<"bls12-381.fr">, %arg410: !algebra.field<"bls12-381.fr">, %arg411: !algebra.field<"bls12-381.fr">):
      %859 = "algebra.field_subtract"(%arg410, %arg409) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %860 = "algebra.field_multiply"(%859, %arg411) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %861 = "algebra.field_add"(%arg409, %860) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%861) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_f76cda8e28f45b05fc9c2123a0520855404c183a59c052d86cc45895f4878f8b", sym_visibility = "private"}> ({
    ^bb0(%arg404: !runtime.scope, %arg405: !data.field_vector<"bls12-381.fr">, %arg406: ui64, %arg407: ui64, %arg408: !data.field_vector<"bls12-381.fr">):
      %852 = "exec.fold"(%arg404, %arg408, %arg405, %arg406, %arg407) <{domain = @finite_zkl_f76cda8e28f45b05fc9c2123a0520855404c183a59c052d86cc45895f4878f8b_s0_domain, site = "s0", step = @finite_zkl_f76cda8e28f45b05fc9c2123a0520855404c183a59c052d86cc45895f4878f8b_s0_body}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%852)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb1(%853: !data.field_vector<"bls12-381.fr">, %854: ui64, %855: ui64):  // pred: ^bb0
      %856 = "exec.returned"(%853, %854, %855) : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%856) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb2(%857: !exec.stop):  // pred: ^bb0
      %858 = "exec.failed"(%857) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%858) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_f76cda8e28f45b05fc9c2123a0520855404c183a59c052d86cc45895f4878f8b_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg403: !data.field_vector<"bls12-381.fr">):
      %851 = "data.domain_elements"(%arg403) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%851) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "finite_zkl_f76cda8e28f45b05fc9c2123a0520855404c183a59c052d86cc45895f4878f8b_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg397: !runtime.scope, %arg398: !data.field_vector<"bls12-381.fr">, %arg399: ui64, %arg400: ui64, %arg401: !algebra.field<"bls12-381.fr">, %arg402: !data.field_vector<"bls12-381.fr">):
      %844 = "func.call"(%arg397, %arg398, %arg399, %arg400, %arg401) <{callee = @zkl_195a79478f48dffc2a6917273d8317df0fabae786920a46fa2ac6b2737144299}> {runtime.site = "body"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%844)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb1(%845: !data.field_vector<"bls12-381.fr">, %846: ui64, %847: ui64):  // pred: ^bb0
      %848 = "exec.returned"(%845, %846, %847) : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%848) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb2(%849: !exec.stop):  // pred: ^bb0
      %850 = "exec.failed"(%849) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%850) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["finite_zkl_f76cda8e28f45b05fc9c2123a0520855404c183a59c052d86cc45895f4878f8b_s0_body", []]} : () -> ()
    "func.func"() <{function_type = (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !data.field_vector<"bls12-381.fr">, sym_name = "zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", sym_visibility = "private"}> ({
    ^bb0(%arg394: !data.field_vector<"bls12-381.fr">, %arg395: ui64, %arg396: ui64):
      "func.return"(%arg394) : (!data.field_vector<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_7b9dfa97fa3e158d428459ec12d8a2d5aa171a060ab79f314eeccc53ee772b17", sym_visibility = "private"}> ({
    ^bb0(%arg391: !runtime.scope, %arg392: !data.field_vector<"bls12-381.fr">, %arg393: !algebra.field<"bls12-381.fr">):
      %839 = "exec.apply"(%arg391) <{binding = @zkl_binding_13, parameters = [], site = "s0_create_0"}> : (!runtime.scope) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">)>
      "exec.dispatch"(%839)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">)>) -> ()
    ^bb1(%840: !runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">):  // pred: ^bb0
      %841 = "exec.returned"(%840, %arg392, %arg393) : (!runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%841) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%842: !exec.stop):  // pred: ^bb0
      %843 = "exec.failed"(%842) : (!exec.stop) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%843) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7211h6c617965725f636c61696d", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_e0f7a4e58ae24eb13e9b2033c42c179b2766ff6cdb4ae1470bf7ef9b1721d646", sym_visibility = "private"}> ({
    ^bb0(%arg387: !runtime.scope, %arg388: !runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, %arg389: !data.field_vector<"bls12-381.fr">, %arg390: !algebra.field<"bls12-381.fr">):
      %838 = "exec.returned"(%arg388, %arg389, %arg390, %arg389, %arg390) : (!runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%838) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7210h6f70656e5f6c61796572", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, ui64, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_8c63ad97d926a7762c597860addde408bcd2077ea9cda1b99df123dc13e64af6", sym_visibility = "private"}> ({
    ^bb0(%arg379: !runtime.scope, %arg380: !data.field_vector<"bls12-381.fr">, %arg381: !data.field_vector<"bls12-381.fr">, %arg382: !data.field_vector<"bls12-381.fr">, %arg383: ui64, %arg384: ui64, %arg385: ui64, %arg386: ui64):
      %804 = "exec.apply"(%arg379) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s2"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%804)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%805: ui64):  // pred: ^bb0
      %806 = "exec.apply"(%arg379, %arg383, %arg386) <{binding = @zkl_binding_11, parameters = [], site = "s3"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%806)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%807: !exec.stop):  // 7 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb9, ^bb11
      %808 = "exec.failed"(%807) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%808) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%809: ui64):  // pred: ^bb1
      %810 = "exec.apply"(%arg379) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s4"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%810)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%811: ui64):  // pred: ^bb3
      %812 = "exec.apply"(%arg379, %809, %811) <{binding = @zkl_binding_11, parameters = [], site = "s5"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%812)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%813: ui64):  // pred: ^bb4
      %814 = "exec.range"(%arg379, %805, %813) <{site = "s10"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%814)[^bb6, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i64, i64)>) -> ()
    ^bb6(%815: i64, %816: i64):  // pred: ^bb5
      %817 = "runtime.borrow_transfer"(%arg379, %arg382, %arg383) : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>
      "cf.br"(%815, %817)[^bb7] : (i64, !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb7(%818: i64, %819: !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>):  // 2 preds: ^bb6, ^bb10
      %820 = "arith.cmpi"(%818, %816) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%820, %819)[^bb8, ^bb9] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb8:  // pred: ^bb7
      %821 = "runtime.iteration"(%arg379, %818) <{site = "s10"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%821)[^bb12, ^bb11] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb9(%822: !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>):  // pred: ^bb7
      %823 = "runtime.accept_transfer"(%arg379, %822) : (!runtime.scope, !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>
      "exec.dispatch"(%823)[^bb15, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb10(%824: !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>):  // pred: ^bb14
      %825 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %826 = "arith.addi"(%818, %825) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%826, %824)[^bb7] : (i64, !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb11(%827: !exec.stop):  // 3 preds: ^bb8, ^bb12, ^bb13
      "runtime.release_transfer"(%819) : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
      "cf.br"(%827)[^bb2] : (!exec.stop) -> ()
    ^bb12(%828: ui64):  // pred: ^bb8
      %829:2 = "runtime.transfer_values"(%819) : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> (!data.field_vector<"bls12-381.fr">, ui64)
      %830 = "runtime.enter_scope"(%arg379, %818, %828, %829#0, %829#1, %arg380, %arg381, %arg384, %arg385) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 7>, site = "s10"}> : (!runtime.scope, i64, ui64, !data.field_vector<"bls12-381.fr">, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%830)[^bb13, ^bb11] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb13(%831: !runtime.scope):  // pred: ^bb12
      %832 = "func.call"(%831, %828, %829#0, %829#1, %arg380, %arg381, %arg384, %arg385) <{callee = @zkl_control_14}> : (!runtime.scope, ui64, !data.field_vector<"bls12-381.fr">, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>
      %833 = "runtime.exit_scope"(%831, %832) : (!runtime.scope, !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>) -> !exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>)>
      "exec.dispatch"(%833)[^bb14, ^bb11] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>)>) -> ()
    ^bb14(%834: !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>):  // pred: ^bb13
      "runtime.release_transfer"(%819) : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
      "cf.br"(%834)[^bb10] : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb15(%835: !data.field_vector<"bls12-381.fr">, %836: ui64):  // pred: ^bb9
      %837 = "exec.returned"(%835) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%837) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7212h76616c7565735f62656c6f77", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, !data.field_vector<"bls12-381.fr">, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>, no_inline, sym_name = "zkl_control_14", sym_visibility = "private"}> ({
    ^bb0(%arg371: !runtime.scope, %arg372: ui64, %arg373: !data.field_vector<"bls12-381.fr">, %arg374: ui64, %arg375: !data.field_vector<"bls12-381.fr">, %arg376: !data.field_vector<"bls12-381.fr">, %arg377: ui64, %arg378: ui64):
      %791 = "exec.apply"(%arg371) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s11"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%791)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%792: ui64):  // pred: ^bb0
      %793 = "exec.apply"(%arg371, %arg374, %792) <{binding = @zkl_binding_11, parameters = [], site = "s12"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%793)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%794: !exec.stop):  // 5 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5
      %795 = "exec.failed"(%794) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>
      "func.return"(%795) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb3(%796: ui64):  // pred: ^bb1
      %797 = "func.call"(%arg371, %arg375, %796, %arg377) <{callee = @zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e}> {runtime.site = "s14"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%797)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb4(%798: !data.field_vector<"bls12-381.fr">):  // pred: ^bb3
      %799 = "func.call"(%arg371, %arg376, %796, %arg377) <{callee = @zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e}> {runtime.site = "s15"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%799)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb5(%800: !data.field_vector<"bls12-381.fr">):  // pred: ^bb4
      %801 = "func.call"(%arg371, %798, %800, %arg373, %arg378) <{callee = @zkl_3a99bc0fa1dab7cb27c9ec80754c3782b0a32e76ddc961a50e12c24c6cbff683}> {runtime.site = "s16"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%801)[^bb6, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb6(%802: !data.field_vector<"bls12-381.fr">):  // pred: ^bb5
      %803 = "exec.complete"(%arg371, %802, %796) : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>
      "func.return"(%803) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", sym_visibility = "private"}> ({
    ^bb0(%arg367: !runtime.scope, %arg368: !data.field_vector<"bls12-381.fr">, %arg369: ui64, %arg370: ui64):
      %763 = "exec.apply"(%arg367) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s2"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%763)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%764: ui64):  // pred: ^bb0
      %765 = "exec.range"(%arg367, %764, %arg370) <{site = "s4"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%765)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i64, i64)>) -> ()
    ^bb2(%766: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb6, ^bb8
      %767 = "exec.failed"(%766) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%767) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%768: i64, %769: i64):  // pred: ^bb1
      %770 = "runtime.borrow_transfer"(%arg367, %arg368, %arg370) : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>
      "cf.br"(%768, %770)[^bb4] : (i64, !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb4(%771: i64, %772: !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>):  // 2 preds: ^bb3, ^bb7
      %773 = "arith.cmpi"(%771, %769) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%773, %772)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb5:  // pred: ^bb4
      %774 = "runtime.iteration"(%arg367, %771) <{site = "s4"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%774)[^bb9, ^bb8] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb6(%775: !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>):  // pred: ^bb4
      %776 = "runtime.accept_transfer"(%arg367, %775) : (!runtime.scope, !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>
      "exec.dispatch"(%776)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb7(%777: !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>):  // pred: ^bb11
      %778 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %779 = "arith.addi"(%771, %778) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%779, %777)[^bb4] : (i64, !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb8(%780: !exec.stop):  // 3 preds: ^bb5, ^bb9, ^bb10
      "runtime.release_transfer"(%772) : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
      "cf.br"(%780)[^bb2] : (!exec.stop) -> ()
    ^bb9(%781: ui64):  // pred: ^bb5
      %782:2 = "runtime.transfer_values"(%772) : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> (!data.field_vector<"bls12-381.fr">, ui64)
      %783 = "runtime.enter_scope"(%arg367, %771, %781, %782#0, %782#1, %arg369) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 4>, site = "s4"}> : (!runtime.scope, i64, ui64, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%783)[^bb10, ^bb8] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb10(%784: !runtime.scope):  // pred: ^bb9
      %785 = "func.call"(%784, %781, %782#0, %782#1, %arg369) <{callee = @zkl_control_15}> : (!runtime.scope, ui64, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>
      %786 = "runtime.exit_scope"(%784, %785) : (!runtime.scope, !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>) -> !exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>)>
      "exec.dispatch"(%786)[^bb11, ^bb8] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>)>) -> ()
    ^bb11(%787: !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>):  // pred: ^bb10
      "runtime.release_transfer"(%772) : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
      "cf.br"(%787)[^bb7] : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb12(%788: !data.field_vector<"bls12-381.fr">, %789: ui64):  // pred: ^bb6
      %790 = "exec.returned"(%788) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%790) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7212h73656c6563745f626c6f636b", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>, no_inline, sym_name = "zkl_control_15", sym_visibility = "private"}> ({
    ^bb0(%arg362: !runtime.scope, %arg363: ui64, %arg364: !data.field_vector<"bls12-381.fr">, %arg365: ui64, %arg366: ui64):
      %724 = "exec.apply"(%arg362) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s5"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%724)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%725: ui64):  // pred: ^bb0
      %726 = "exec.apply"(%arg362, %arg365, %725) <{binding = @zkl_binding_11, parameters = [], site = "s6"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%726)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%727: !exec.stop):  // 16 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb10, ^bb12, ^bb13, ^bb15, ^bb16, ^bb18, ^bb19
      %728 = "exec.failed"(%727) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>
      "func.return"(%728) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb3(%729: ui64):  // pred: ^bb1
      %730 = "func.call"(%arg362, %729) <{callee = @s3h676b7212h706f7765725f6f665f74776f}> {runtime.site = "s8"} : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%730)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%731: ui64):  // pred: ^bb3
      %732 = "exec.apply"(%arg362, %arg366, %731) <{binding = @zkl_binding_5, parameters = [], site = "s9"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%732)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%733: ui64):  // pred: ^bb4
      %734 = "exec.apply"(%arg362) <{binding = @zkl_binding_1, parameters = [2 : ui64], site = "s10"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%734)[^bb6, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb6(%735: ui64):  // pred: ^bb5
      %736 = "exec.apply"(%arg362, %733, %735) <{binding = @zkl_binding_3, parameters = [], site = "s11"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%736)[^bb7, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb7(%737: ui64):  // pred: ^bb6
      %738 = "exec.apply"(%arg362, %arg364) <{binding = @zkl_binding_12, parameters = [], site = "s13"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%738)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%739: !data.field_vector<"bls12-381.fr">, %740: !data.field_vector<"bls12-381.fr">):  // pred: ^bb7
      %741 = "exec.apply"(%arg362) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s15"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%741)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb9(%742: ui64):  // pred: ^bb8
      %743 = "exec.apply"(%arg362, %737, %742) <{binding = @zkl_binding_4, parameters = [], site = "s16"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%743)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb10(%744: i1):  // pred: ^bb9
      %745 = "exec.test"(%arg362, %744) <{site = "s19"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%745)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb11(%746: i1):  // pred: ^bb10
      "cf.cond_br"(%746)[^bb12, ^bb13] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb12:  // pred: ^bb11
      %747 = "runtime.enter_scope"(%arg362, %739, %740) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "then", site = "s19"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%747)[^bb15, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb13:  // pred: ^bb11
      %748 = "runtime.enter_scope"(%arg362, %739, %740) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "else", site = "s19"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%748)[^bb18, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb14(%749: !data.field_vector<"bls12-381.fr">):  // 2 preds: ^bb17, ^bb20
      %750 = "exec.complete"(%arg362, %749, %729) : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>
      "func.return"(%750) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb15(%751: !runtime.scope):  // pred: ^bb12
      %752 = "func.call"(%751, %739, %740) <{callee = @zkl_control_16}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      %753 = "runtime.exit_scope"(%751, %752) : (!runtime.scope, !exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>)>
      "exec.dispatch"(%753)[^bb16, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>)>) -> ()
    ^bb16(%754: !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>):  // pred: ^bb15
      %755 = "runtime.accept_transfer"(%arg362, %754) : (!runtime.scope, !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%755)[^bb17, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb17(%756: !data.field_vector<"bls12-381.fr">):  // pred: ^bb16
      "cf.br"(%756)[^bb14] : (!data.field_vector<"bls12-381.fr">) -> ()
    ^bb18(%757: !runtime.scope):  // pred: ^bb13
      %758 = "func.call"(%757, %739, %740) <{callee = @zkl_control_17}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      %759 = "runtime.exit_scope"(%757, %758) : (!runtime.scope, !exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>)>
      "exec.dispatch"(%759)[^bb19, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>)>) -> ()
    ^bb19(%760: !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>):  // pred: ^bb18
      %761 = "runtime.accept_transfer"(%arg362, %760) : (!runtime.scope, !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%761)[^bb20, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb20(%762: !data.field_vector<"bls12-381.fr">):  // pred: ^bb19
      "cf.br"(%762)[^bb14] : (!data.field_vector<"bls12-381.fr">) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_16", sym_visibility = "private"}> ({
    ^bb0(%arg359: !runtime.scope, %arg360: !data.field_vector<"bls12-381.fr">, %arg361: !data.field_vector<"bls12-381.fr">):
      %723 = "exec.complete"(%arg359, %arg361) : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%723) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_17", sym_visibility = "private"}> ({
    ^bb0(%arg356: !runtime.scope, %arg357: !data.field_vector<"bls12-381.fr">, %arg358: !data.field_vector<"bls12-381.fr">):
      %722 = "exec.complete"(%arg356, %arg357) : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%722) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_3a99bc0fa1dab7cb27c9ec80754c3782b0a32e76ddc961a50e12c24c6cbff683", sym_visibility = "private"}> ({
    ^bb0(%arg351: !runtime.scope, %arg352: !data.field_vector<"bls12-381.fr">, %arg353: !data.field_vector<"bls12-381.fr">, %arg354: !data.field_vector<"bls12-381.fr">, %arg355: ui64):
      %687 = "func.call"(%arg351, %arg355) <{callee = @s3h676b7212h706f7765725f6f665f74776f}> {runtime.site = "s0"} : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%687)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%688: ui64):  // pred: ^bb0
      %689 = "func.call"(%arg351, %arg354, %688) <{callee = @zkl_afd97de07c9ccae9db68186ebf66098aed7daffb4b11c598d0da5cd116df8490}> {runtime.site = "s2"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%689)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%690: !exec.stop):  // 8 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb10, ^bb12
      %691 = "exec.failed"(%690) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%691) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%692: !data.field_vector<"bls12-381.fr">):  // pred: ^bb1
      %693 = "func.call"(%arg351, %arg354, %688) <{callee = @zkl_33f3047479634e63ecd16a0855f88ad8af019c37d677a4ffe6f5bacc63307947}> {runtime.site = "s4"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%693)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb4(%694: !data.field_vector<"bls12-381.fr">):  // pred: ^bb3
      %695 = "exec.apply"(%arg351) <{binding = @zkl_binding_8, parameters = [], site = "s6"}> : (!runtime.scope) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%695)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb5(%696: !data.field_vector<"bls12-381.fr">):  // pred: ^bb4
      %697 = "exec.apply"(%arg351) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s8"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%697)[^bb6, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb6(%698: ui64):  // pred: ^bb5
      %699 = "exec.range"(%arg351, %698, %688) <{site = "s14"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%699)[^bb7, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i64, i64)>) -> ()
    ^bb7(%700: i64, %701: i64):  // pred: ^bb6
      %702 = "runtime.borrow_transfer"(%arg351, %696) : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>
      "cf.br"(%700, %702)[^bb8] : (i64, !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%703: i64, %704: !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>):  // 2 preds: ^bb7, ^bb11
      %705 = "arith.cmpi"(%703, %701) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%705, %704)[^bb9, ^bb10] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb9:  // pred: ^bb8
      %706 = "runtime.iteration"(%arg351, %703) <{site = "s14"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%706)[^bb13, ^bb12] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb10(%707: !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>):  // pred: ^bb8
      %708 = "runtime.accept_transfer"(%arg351, %707) : (!runtime.scope, !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%708)[^bb16, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb11(%709: !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>):  // pred: ^bb15
      %710 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %711 = "arith.addi"(%703, %710) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%711, %709)[^bb8] : (i64, !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb12(%712: !exec.stop):  // 3 preds: ^bb9, ^bb13, ^bb14
      "runtime.release_transfer"(%704) : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
      "cf.br"(%712)[^bb2] : (!exec.stop) -> ()
    ^bb13(%713: ui64):  // pred: ^bb9
      %714 = "runtime.transfer_values"(%704) : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> !data.field_vector<"bls12-381.fr">
      %715 = "runtime.enter_scope"(%arg351, %703, %713, %714, %arg352, %arg353, %arg355, %692, %694) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 7>, site = "s14"}> : (!runtime.scope, i64, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%715)[^bb14, ^bb12] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb14(%716: !runtime.scope):  // pred: ^bb13
      %717 = "func.call"(%716, %713, %714, %arg352, %arg353, %arg355, %692, %694) <{callee = @zkl_control_18}> : (!runtime.scope, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      %718 = "runtime.exit_scope"(%716, %717) : (!runtime.scope, !exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>)>
      "exec.dispatch"(%718)[^bb15, ^bb12] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>)>) -> ()
    ^bb15(%719: !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>):  // pred: ^bb14
      "runtime.release_transfer"(%704) : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
      "cf.br"(%719)[^bb11] : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb16(%720: !data.field_vector<"bls12-381.fr">):  // pred: ^bb10
      %721 = "exec.returned"(%720) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%721) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7212h6c617965725f76616c756573", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_18", sym_visibility = "private"}> ({
    ^bb0(%arg343: !runtime.scope, %arg344: ui64, %arg345: !data.field_vector<"bls12-381.fr">, %arg346: !data.field_vector<"bls12-381.fr">, %arg347: !data.field_vector<"bls12-381.fr">, %arg348: ui64, %arg349: !data.field_vector<"bls12-381.fr">, %arg350: !data.field_vector<"bls12-381.fr">):
      %674 = "func.call"(%arg343, %arg346, %arg344, %arg348) <{callee = @zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e}> {runtime.site = "s15"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%674)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%675: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %676 = "func.call"(%arg343, %arg347, %arg344, %arg348) <{callee = @zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e}> {runtime.site = "s17"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%676)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%677: !exec.stop):  // 5 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5
      %678 = "exec.failed"(%677) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%678) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%679: !data.field_vector<"bls12-381.fr">):  // pred: ^bb1
      %680 = "exec.collect"(%arg343, %675, %679, %arg349, %arg350) <{body = @zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_body, domain = @zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_domain, site = "s19"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%680)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb4(%681: !data.field_vector<"bls12-381.fr">):  // pred: ^bb3
      %682 = "exec.apply"(%arg343, %681) <{binding = @zkl_binding_10, parameters = [], site = "s20"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%682)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb5(%683: !algebra.field<"bls12-381.fr">):  // pred: ^bb4
      %684 = "exec.apply"(%arg343, %arg345, %683) <{binding = @zkl_binding_9, parameters = [], site = "s21"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%684)[^bb6, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb6(%685: !data.field_vector<"bls12-381.fr">):  // pred: ^bb5
      %686 = "exec.complete"(%arg343, %685) : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%686) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "data.domain"() <{function_type = (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, sym_name = "zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_domain", sym_visibility = "private"}> ({
    ^bb0(%arg339: !data.field_vector<"bls12-381.fr">, %arg340: !data.field_vector<"bls12-381.fr">, %arg341: !data.field_vector<"bls12-381.fr">, %arg342: !data.field_vector<"bls12-381.fr">):
      %667 = "data.domain_elements"(%arg339) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %668 = "data.domain_elements"(%arg340) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %669 = "data.domain_zip"(%667, %668) : (!data.domain<!algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      %670 = "data.domain_elements"(%arg341) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %671 = "data.domain_zip"(%669, %670) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      %672 = "data.domain_elements"(%arg342) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %673 = "data.domain_zip"(%671, %672) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%673) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_body", sym_visibility = "private"}> ({
    ^bb0(%arg330: !runtime.scope, %arg331: !algebra.field<"bls12-381.fr">, %arg332: !algebra.field<"bls12-381.fr">, %arg333: !algebra.field<"bls12-381.fr">, %arg334: !algebra.field<"bls12-381.fr">, %arg335: !data.field_vector<"bls12-381.fr">, %arg336: !data.field_vector<"bls12-381.fr">, %arg337: !data.field_vector<"bls12-381.fr">, %arg338: !data.field_vector<"bls12-381.fr">):
      %662 = "exec.compute"(%arg330, %arg331, %arg332, %arg333, %arg334) <{callee = @zkl_6b3d366572d1ba53650a202f39ff52a2f298a1591829443fbeaa34ef3974f084, site = "body"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%662)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%663: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %664 = "exec.returned"(%663) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%664) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%665: !exec.stop):  // pred: ^bb0
      %666 = "exec.failed"(%665) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%666) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_body", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_afd97de07c9ccae9db68186ebf66098aed7daffb4b11c598d0da5cd116df8490", sym_visibility = "private"}> ({
    ^bb0(%arg327: !runtime.scope, %arg328: !data.field_vector<"bls12-381.fr">, %arg329: ui64):
      %655 = "exec.apply"(%arg327) <{binding = @zkl_binding_8, parameters = [], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%655)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%656: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %657 = "func.call"(%arg327, %656, %arg329, %arg328) <{callee = @zkl_64f08ca50fc7259b0fd328123878fa34f141da3df44e0981a3e41ac11e2735dd}> {runtime.site = "s2"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%657)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%658: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %659 = "exec.failed"(%658) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%659) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%660: !data.field_vector<"bls12-381.fr">):  // pred: ^bb1
      %661 = "exec.returned"(%660) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%661) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b729h7265706c6963617465", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_e7a7efcd14676d32c0e577ff1097f611a3dc84c74ecaa8bfdbebb25968971255", sym_visibility = "private"}> ({
    ^bb0(%arg323: !runtime.scope, %arg324: !data.field_vector<"bls12-381.fr">, %arg325: !algebra.field<"bls12-381.fr">, %arg326: ui64):
      %650 = "func.call"(%arg323, %arg324, %arg325, %arg326) <{callee = @zkl_fbd2531b804047766f8107241edd0ea81368b70795e44e4d8e07484d142783bb}> {runtime.site = "s2"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%650)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%651: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %652 = "exec.returned"(%651) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%652) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%653: !exec.stop):  // pred: ^bb0
      %654 = "exec.failed"(%653) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%654) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zks_99cdc30b104640f79094177f26387b3c04df24c083a5fa7125a3fd69fc1eb459", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_fbd2531b804047766f8107241edd0ea81368b70795e44e4d8e07484d142783bb", sym_visibility = "private"}> ({
    ^bb0(%arg319: !runtime.scope, %arg320: !data.field_vector<"bls12-381.fr">, %arg321: !algebra.field<"bls12-381.fr">, %arg322: ui64):
      %623 = "exec.apply"(%arg319) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s1"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%623)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%624: ui64):  // pred: ^bb0
      %625 = "exec.range"(%arg319, %624, %arg322) <{site = "s3"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%625)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i64, i64)>) -> ()
    ^bb2(%626: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb6, ^bb8
      %627 = "exec.failed"(%626) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%627) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%628: i64, %629: i64):  // pred: ^bb1
      %630 = "runtime.borrow_transfer"(%arg319, %arg320) : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>
      "cf.br"(%628, %630)[^bb4] : (i64, !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb4(%631: i64, %632: !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>):  // 2 preds: ^bb3, ^bb7
      %633 = "arith.cmpi"(%631, %629) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%633, %632)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb5:  // pred: ^bb4
      %634 = "runtime.iteration"(%arg319, %631) <{site = "s3"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%634)[^bb9, ^bb8] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb6(%635: !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>):  // pred: ^bb4
      %636 = "runtime.accept_transfer"(%arg319, %635) : (!runtime.scope, !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%636)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb7(%637: !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>):  // pred: ^bb11
      %638 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %639 = "arith.addi"(%631, %638) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%639, %637)[^bb4] : (i64, !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%640: !exec.stop):  // 3 preds: ^bb5, ^bb9, ^bb10
      "runtime.release_transfer"(%632) : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
      "cf.br"(%640)[^bb2] : (!exec.stop) -> ()
    ^bb9(%641: ui64):  // pred: ^bb5
      %642 = "runtime.transfer_values"(%632) : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> !data.field_vector<"bls12-381.fr">
      %643 = "runtime.enter_scope"(%arg319, %631, %641, %642, %arg321) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 3>, site = "s3"}> : (!runtime.scope, i64, ui64, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%643)[^bb10, ^bb8] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb10(%644: !runtime.scope):  // pred: ^bb9
      %645 = "func.call"(%644, %641, %642, %arg321) <{callee = @zkl_control_19}> : (!runtime.scope, ui64, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      %646 = "runtime.exit_scope"(%644, %645) : (!runtime.scope, !exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>)>
      "exec.dispatch"(%646)[^bb11, ^bb8] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>)>) -> ()
    ^bb11(%647: !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>):  // pred: ^bb10
      "runtime.release_transfer"(%632) : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
      "cf.br"(%647)[^bb7] : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb12(%648: !data.field_vector<"bls12-381.fr">):  // pred: ^bb6
      %649 = "exec.returned"(%648) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%649) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7212h7265706561745f76616c7565", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_19", sym_visibility = "private"}> ({
    ^bb0(%arg315: !runtime.scope, %arg316: ui64, %arg317: !data.field_vector<"bls12-381.fr">, %arg318: !algebra.field<"bls12-381.fr">):
      %618 = "exec.apply"(%arg315, %arg317, %arg318) <{binding = @zkl_binding_9, parameters = [], site = "s4"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%618)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%619: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %620 = "exec.complete"(%arg315, %619) : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%620) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%621: !exec.stop):  // pred: ^bb0
      %622 = "exec.failed"(%621) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%622) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_64f08ca50fc7259b0fd328123878fa34f141da3df44e0981a3e41ac11e2735dd", sym_visibility = "private"}> ({
    ^bb0(%arg311: !runtime.scope, %arg312: !data.field_vector<"bls12-381.fr">, %arg313: ui64, %arg314: !data.field_vector<"bls12-381.fr">):
      %613 = "exec.fold"(%arg311, %arg314, %arg312, %arg313) <{domain = @finite_zkl_64f08ca50fc7259b0fd328123878fa34f141da3df44e0981a3e41ac11e2735dd_s0_domain, site = "s0", step = @finite_zkl_64f08ca50fc7259b0fd328123878fa34f141da3df44e0981a3e41ac11e2735dd_s0_body}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%613)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%614: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %615 = "exec.returned"(%614) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%615) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%616: !exec.stop):  // pred: ^bb0
      %617 = "exec.failed"(%616) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%617) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_64f08ca50fc7259b0fd328123878fa34f141da3df44e0981a3e41ac11e2735dd_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg310: !data.field_vector<"bls12-381.fr">):
      %612 = "data.domain_elements"(%arg310) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%612) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "finite_zkl_64f08ca50fc7259b0fd328123878fa34f141da3df44e0981a3e41ac11e2735dd_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg305: !runtime.scope, %arg306: !data.field_vector<"bls12-381.fr">, %arg307: !algebra.field<"bls12-381.fr">, %arg308: !data.field_vector<"bls12-381.fr">, %arg309: ui64):
      %607 = "func.call"(%arg305, %arg306, %arg307, %arg309) <{callee = @zkl_e7a7efcd14676d32c0e577ff1097f611a3dc84c74ecaa8bfdbebb25968971255}> {runtime.site = "body"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%607)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%608: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %609 = "exec.returned"(%608) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%609) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%610: !exec.stop):  // pred: ^bb0
      %611 = "exec.failed"(%610) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%611) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["finite_zkl_64f08ca50fc7259b0fd328123878fa34f141da3df44e0981a3e41ac11e2735dd_s0_body", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_33f3047479634e63ecd16a0855f88ad8af019c37d677a4ffe6f5bacc63307947", sym_visibility = "private"}> ({
    ^bb0(%arg302: !runtime.scope, %arg303: !data.field_vector<"bls12-381.fr">, %arg304: ui64):
      %578 = "exec.apply"(%arg302) <{binding = @zkl_binding_8, parameters = [], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%578)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%579: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %580 = "exec.apply"(%arg302) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s2"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%580)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%581: !exec.stop):  // 5 preds: ^bb0, ^bb1, ^bb3, ^bb7, ^bb9
      %582 = "exec.failed"(%581) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%582) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%583: ui64):  // pred: ^bb1
      %584 = "exec.range"(%arg302, %583, %arg304) <{site = "s4"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%584)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i64, i64)>) -> ()
    ^bb4(%585: i64, %586: i64):  // pred: ^bb3
      %587 = "runtime.borrow_transfer"(%arg302, %579) : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>
      "cf.br"(%585, %587)[^bb5] : (i64, !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb5(%588: i64, %589: !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>):  // 2 preds: ^bb4, ^bb8
      %590 = "arith.cmpi"(%588, %586) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%590, %589)[^bb6, ^bb7] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb6:  // pred: ^bb5
      %591 = "runtime.iteration"(%arg302, %588) <{site = "s4"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%591)[^bb10, ^bb9] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb7(%592: !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>):  // pred: ^bb5
      %593 = "runtime.accept_transfer"(%arg302, %592) : (!runtime.scope, !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%593)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%594: !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>):  // pred: ^bb12
      %595 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %596 = "arith.addi"(%588, %595) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%596, %594)[^bb5] : (i64, !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb9(%597: !exec.stop):  // 3 preds: ^bb6, ^bb10, ^bb11
      "runtime.release_transfer"(%589) : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
      "cf.br"(%597)[^bb2] : (!exec.stop) -> ()
    ^bb10(%598: ui64):  // pred: ^bb6
      %599 = "runtime.transfer_values"(%589) : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> !data.field_vector<"bls12-381.fr">
      %600 = "runtime.enter_scope"(%arg302, %588, %598, %599, %arg303) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 3>, site = "s4"}> : (!runtime.scope, i64, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%600)[^bb11, ^bb9] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb11(%601: !runtime.scope):  // pred: ^bb10
      %602 = "func.call"(%601, %598, %599, %arg303) <{callee = @zkl_control_20}> : (!runtime.scope, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      %603 = "runtime.exit_scope"(%601, %602) : (!runtime.scope, !exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>)>
      "exec.dispatch"(%603)[^bb12, ^bb9] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>)>) -> ()
    ^bb12(%604: !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>):  // pred: ^bb11
      "runtime.release_transfer"(%589) : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
      "cf.br"(%604)[^bb8] : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb13(%605: !data.field_vector<"bls12-381.fr">):  // pred: ^bb7
      %606 = "exec.returned"(%605) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%606) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b724h74696c65", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_20", sym_visibility = "private"}> ({
    ^bb0(%arg298: !runtime.scope, %arg299: ui64, %arg300: !data.field_vector<"bls12-381.fr">, %arg301: !data.field_vector<"bls12-381.fr">):
      %573 = "func.call"(%arg298, %arg300, %arg301) <{callee = @zkl_e82798dff61bd8f44d82e86c57d3877221b197a8dd223c42911fed63bef673aa}> {runtime.site = "s5"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%573)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%574: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %575 = "exec.complete"(%arg298, %574) : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%575) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%576: !exec.stop):  // pred: ^bb0
      %577 = "exec.failed"(%576) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%577) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_ac1d3513b06c1d4950d126f678b9482e4ca13944fc4b35442d1a33796d064b0c", sym_visibility = "private"}> ({
    ^bb0(%arg295: !runtime.scope, %arg296: !data.field_vector<"bls12-381.fr">, %arg297: !algebra.field<"bls12-381.fr">):
      %568 = "exec.apply"(%arg295, %arg296, %arg297) <{binding = @zkl_binding_9, parameters = [], site = "s2"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%568)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%569: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %570 = "exec.returned"(%569) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%570) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%571: !exec.stop):  // pred: ^bb0
      %572 = "exec.failed"(%571) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%572) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zks_42e44eec4fd7419218a6cf70cf462d528dfc3e199764475009d12bc09d4ada97", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_e82798dff61bd8f44d82e86c57d3877221b197a8dd223c42911fed63bef673aa", sym_visibility = "private"}> ({
    ^bb0(%arg292: !runtime.scope, %arg293: !data.field_vector<"bls12-381.fr">, %arg294: !data.field_vector<"bls12-381.fr">):
      %563 = "exec.fold"(%arg292, %arg294, %arg293) <{domain = @finite_zkl_e82798dff61bd8f44d82e86c57d3877221b197a8dd223c42911fed63bef673aa_s0_domain, site = "s0", step = @finite_zkl_e82798dff61bd8f44d82e86c57d3877221b197a8dd223c42911fed63bef673aa_s0_body}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%563)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%564: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %565 = "exec.returned"(%564) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%565) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%566: !exec.stop):  // pred: ^bb0
      %567 = "exec.failed"(%566) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%567) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_e82798dff61bd8f44d82e86c57d3877221b197a8dd223c42911fed63bef673aa_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg291: !data.field_vector<"bls12-381.fr">):
      %562 = "data.domain_elements"(%arg291) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%562) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "finite_zkl_e82798dff61bd8f44d82e86c57d3877221b197a8dd223c42911fed63bef673aa_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg287: !runtime.scope, %arg288: !data.field_vector<"bls12-381.fr">, %arg289: !algebra.field<"bls12-381.fr">, %arg290: !data.field_vector<"bls12-381.fr">):
      %557 = "func.call"(%arg287, %arg288, %arg289) <{callee = @zkl_ac1d3513b06c1d4950d126f678b9482e4ca13944fc4b35442d1a33796d064b0c}> {runtime.site = "body"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%557)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%558: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %559 = "exec.returned"(%558) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%559) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%560: !exec.stop):  // pred: ^bb0
      %561 = "exec.failed"(%560) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%561) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["finite_zkl_e82798dff61bd8f44d82e86c57d3877221b197a8dd223c42911fed63bef673aa_s0_body", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_6b3d366572d1ba53650a202f39ff52a2f298a1591829443fbeaa34ef3974f084", sym_visibility = "private"}> ({
    ^bb0(%arg283: !algebra.field<"bls12-381.fr">, %arg284: !algebra.field<"bls12-381.fr">, %arg285: !algebra.field<"bls12-381.fr">, %arg286: !algebra.field<"bls12-381.fr">):
      %552 = "algebra.field_add"(%arg285, %arg286) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %553 = "algebra.field_multiply"(%arg283, %552) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %554 = "algebra.field_multiply"(%arg284, %arg285) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %555 = "algebra.field_multiply"(%554, %arg286) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %556 = "algebra.field_add"(%553, %555) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%556) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_d1f2756b99b17aad26e4b85a966eec4c9419609618b22e3ee7f8a3349cb1e33b", sym_visibility = "private"}> ({
    ^bb0(%arg277: !runtime.scope, %arg278: !data.field_vector<"bls12-381.fr">, %arg279: !data.field_vector<"bls12-381.fr">, %arg280: !data.field_vector<"bls12-381.fr">, %arg281: !data.field_vector<"bls12-381.fr">, %arg282: ui64):
      %533 = "func.call"(%arg277, %arg282) <{callee = @s3h676b7212h706f7765725f6f665f74776f}> {runtime.site = "s0"} : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%533)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%534: ui64):  // pred: ^bb0
      %535 = "exec.apply"(%arg277, %arg280) <{binding = @zkl_binding_2, parameters = [], site = "s2"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%535)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%536: !exec.stop):  // 8 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb8
      %537 = "exec.failed"(%536) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "func.return"(%537) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%538: ui64):  // pred: ^bb1
      %539 = "exec.apply"(%arg277, %538, %arg282) <{binding = @zkl_binding_7, parameters = [], site = "s3"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%539)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%540: ui64):  // pred: ^bb3
      %541 = "exec.apply"(%arg277, %540, %arg282) <{binding = @zkl_binding_7, parameters = [], site = "s4"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%541)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%542: ui64):  // pred: ^bb4
      %543 = "func.call"(%arg277, %arg278, %542, %arg280) <{callee = @zkl_b16c159516733e0a19ce242015622636ee99dc6084d8c851dfb43c25cee57b59}> {runtime.site = "s6"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%543)[^bb6, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb6(%544: !data.field_vector<"bls12-381.fr">):  // pred: ^bb5
      %545 = "func.call"(%arg277, %arg279, %542, %arg280) <{callee = @zkl_b16c159516733e0a19ce242015622636ee99dc6084d8c851dfb43c25cee57b59}> {runtime.site = "s7"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%545)[^bb7, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb7(%546: !data.field_vector<"bls12-381.fr">):  // pred: ^bb6
      %547 = "func.call"(%arg277, %arg281, %534) <{callee = @zkl_afd97de07c9ccae9db68186ebf66098aed7daffb4b11c598d0da5cd116df8490}> {runtime.site = "s8"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%547)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%548: !data.field_vector<"bls12-381.fr">):  // pred: ^bb7
      %549 = "func.call"(%arg277, %arg281, %534) <{callee = @zkl_33f3047479634e63ecd16a0855f88ad8af019c37d677a4ffe6f5bacc63307947}> {runtime.site = "s9"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%549)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb9(%550: !data.field_vector<"bls12-381.fr">):  // pred: ^bb8
      %551 = "exec.returned"(%544, %546, %548, %550) : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "func.return"(%551) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7211h6c617965725f6761746573", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_b16c159516733e0a19ce242015622636ee99dc6084d8c851dfb43c25cee57b59", sym_visibility = "private"}> ({
    ^bb0(%arg273: !runtime.scope, %arg274: !data.field_vector<"bls12-381.fr">, %arg275: ui64, %arg276: !data.field_vector<"bls12-381.fr">):
      %518 = "exec.apply"(%arg273) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%518)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%519: ui64):  // pred: ^bb0
      %520 = "func.call"(%arg273, %arg274, %arg275, %519) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a}> {runtime.site = "s1"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%520)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb2(%521: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %522 = "exec.failed"(%521) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%522) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%523: !data.field_vector<"bls12-381.fr">, %524: ui64, %525: ui64):  // pred: ^bb1
      %526 = "func.call"(%arg273, %523, %524, %525, %arg276) <{callee = @zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be}> {runtime.site = "s2"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%526)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb4(%527: !data.field_vector<"bls12-381.fr">, %528: ui64, %529: ui64):  // pred: ^bb3
      %530 = "exec.compute"(%arg273, %527, %528, %529) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33, site = "s3"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%530)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb5(%531: !data.field_vector<"bls12-381.fr">):  // pred: ^bb4
      %532 = "exec.returned"(%531) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%532) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b728h7265737472696374", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_e1405e1bb4604e60f337203132c746492bf7c31b55302426ae19c2c021c2da1a", sym_visibility = "private"}> ({
    ^bb0(%arg271: !runtime.scope, %arg272: !algebra.field<"bls12-381.fr">):
      %511 = "exec.apply"(%arg271) <{binding = @zkl_binding_8, parameters = [], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%511)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%512: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %513 = "exec.apply"(%arg271) <{binding = @zkl_binding_14, parameters = [], site = "s1_create_0"}> : (!runtime.scope) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">)>
      "exec.dispatch"(%513)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">)>) -> ()
    ^bb2(%514: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %515 = "exec.failed"(%514) : (!exec.stop) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%515) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb3(%516: !runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">):  // pred: ^bb1
      %517 = "exec.returned"(%516, %512, %arg272) : (!runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%517) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b727h70656e64696e67", []]} : () -> ()
    "protocol.func"() <{contracts = [["input", "shape", [@zkl_30326558223483c2b755cae1fef2fb9e26e5ee8894b87d6977fe6482997b20fd, [["input", 0, "role00000000"], ["input", 1, "role00000000"], ["input", 2, "role00000000"], ["input", 3, "role00000000"]]], unit, unit], ["continuation", "gate_sum", [@zkl_e276fa0fd61d1145b2034d7e5681d41484daeb4a120f83771eba638587b04670, [["input", 0, "role00000000"], ["input", 1, "role00000000"], ["input", 2, "role00000000"], ["input", 3, "role00000000"], ["input", 5, "role00000001"], ["input", 6, "role00000001"]]], [@zkl_e276fa0fd61d1145b2034d7e5681d41484daeb4a120f83771eba638587b04670, [["input", 0, "role00000000"], ["input", 1, "role00000000"], ["input", 2, "role00000000"], ["input", 3, "role00000000"], ["output", 6, "role00000001"], ["output", 7, "role00000001"]]], unit]], function_type = (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), input_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"], ["role00000001"], ["role00000000", "role00000001"], ["role00000001"]], origin = ["gkr::Rounds", [["F", ["field", "bls12-381.fr"]], ["Max", ["nat", "4"]]]], output_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"], ["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba"}> ({
    ^bb0(%arg253: !data.field_vector<"bls12-381.fr">, %arg254: !data.field_vector<"bls12-381.fr">, %arg255: !data.field_vector<"bls12-381.fr">, %arg256: !data.field_vector<"bls12-381.fr">, %arg257: !runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">, %arg258: !data.field_vector<"bls12-381.fr">, %arg259: !algebra.field<"bls12-381.fr">, %arg260: ui64, %arg261: !protocol.service_ref<"random.bls12-381.fr/0">):
      %486 = "protocol.local_call"() <{callee = @zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f, role = "role00000000", site = "s1"}> : () -> !data.field_vector<"bls12-381.fr">
      %487:2 = "protocol.local_call"(%arg257, %arg258, %arg259) <{callee = @zkl_bd4f0d76e787de675c5732a4a96fc396d45486f32b3dcda5182ccc324969c825, role = "role00000001", site = "s3"}> : (!runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %488:7 = "protocol.repeat"(%arg260, %arg253, %arg254, %arg255, %arg256, %486, %487#0, %487#1, %arg261) <{carried = 7 : i64, carried_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"]], maximum = 4 : i64, roles = ["role00000000", "role00000001"], site = "s9"}> ({
      ^bb0(%arg262: ui64, %arg263: !data.field_vector<"bls12-381.fr">, %arg264: !data.field_vector<"bls12-381.fr">, %arg265: !data.field_vector<"bls12-381.fr">, %arg266: !data.field_vector<"bls12-381.fr">, %arg267: !data.field_vector<"bls12-381.fr">, %arg268: !data.field_vector<"bls12-381.fr">, %arg269: !algebra.field<"bls12-381.fr">, %arg270: !protocol.service_ref<"random.bls12-381.fr/0">):
        %490:3 = "protocol.local_call"(%arg263, %arg264, %arg265, %arg266) <{callee = @zkl_e2f65d17b480da5da0270346faa1bd036c7a5f879e30f4b2b6bac1224b05e394, role = "role00000000", site = "s10"}> : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %491 = "protocol.exchange"(%490#0) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %492 = "protocol.restrict_roles"(%491) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %493 = "protocol.exchange"(%490#1) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_1"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %494 = "protocol.restrict_roles"(%493) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %495 = "protocol.exchange"(%490#2) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_2"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %496 = "protocol.restrict_roles"(%495) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %497 = "algebra.field_add"(%492, %492) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %498 = "algebra.field_add"(%497, %494) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %499 = "algebra.field_add"(%498, %496) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %500 = "algebra.field_equal"(%arg269, %499) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
        "protocol.guard"(%500) <{owner = "role00000001", site = "s21"}> : (i1) -> ()
        %501 = "protocol.query"(%arg270) <{method = "draw", owner = "role00000001", site = "label_6368616c6c656e6765"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
        %502 = "protocol.exchange"(%501) <{receiver = "role00000000", sender = "role00000001", site = "label_64656c6976657279_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %503 = "protocol.restrict_roles"(%502) <{roles = ["role00000000"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %504:4 = "protocol.local_call"(%arg263, %arg264, %arg265, %arg266, %503) <{callee = @zkl_36caebca415236dd6aac1763c9a581b89c25a00e62432b484ec92ae08e6a0099, role = "role00000000", site = "s26"}> : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)
        %505 = "protocol.local_call"(%arg267, %503) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000000", site = "s28"}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !data.field_vector<"bls12-381.fr">
        %506 = "protocol.local_call"(%arg268, %501) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000001", site = "s30"}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !data.field_vector<"bls12-381.fr">
        %507 = "algebra.field_multiply"(%501, %496) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %508 = "algebra.field_add"(%494, %507) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %509 = "algebra.field_multiply"(%501, %508) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %510 = "algebra.field_add"(%492, %509) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        "protocol.yield"(%504#0, %504#1, %504#2, %504#3, %505, %506, %510) : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
      }) : (ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %489:3 = "protocol.local_call"(%488#5, %488#6) <{callee = @zkl_bcddf8825098d44ae9ce732a7b45754c16637e2a47a4c9f29ef9a21612daeaa3, role = "role00000001", site = "s42"}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      "protocol.return"(%488#4, %488#0, %488#1, %488#2, %488#3, %489#0, %489#1, %489#2) : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> i1, sym_name = "zkf_029bdd6bcc5b1485783f1674f8c6e15543fd2d268649f211eab729158162c828", sym_visibility = "private"}> ({
    ^bb0(%arg241: !data.field_vector<"bls12-381.fr">, %arg242: !data.field_vector<"bls12-381.fr">, %arg243: !data.field_vector<"bls12-381.fr">, %arg244: !data.field_vector<"bls12-381.fr">):
      %473 = "data.dim"(%arg241) <{axis = 0 : i64}> : (!data.field_vector<"bls12-381.fr">) -> ui64
      %474 = "data.dim"(%arg242) <{axis = 0 : i64}> : (!data.field_vector<"bls12-381.fr">) -> ui64
      %475 = "data.index_equal"(%473, %474) : (ui64, ui64) -> i1
      %476 = "data.branch"(%475, %arg241, %arg243) <{alternatives = ["then", "else"]}> ({
      ^bb0(%arg251: !data.field_vector<"bls12-381.fr">, %arg252: !data.field_vector<"bls12-381.fr">):
        %483 = "data.dim"(%arg251) <{axis = 0 : i64}> : (!data.field_vector<"bls12-381.fr">) -> ui64
        %484 = "data.dim"(%arg252) <{axis = 0 : i64}> : (!data.field_vector<"bls12-381.fr">) -> ui64
        %485 = "data.index_equal"(%483, %484) : (ui64, ui64) -> i1
        "data.yield"(%485) : (i1) -> ()
      }, {
      ^bb0(%arg249: !data.field_vector<"bls12-381.fr">, %arg250: !data.field_vector<"bls12-381.fr">):
        %482 = "arith.constant"() <{value = false}> : () -> i1
        "data.yield"(%482) : (i1) -> ()
      }) : (i1, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> i1
      %477 = "data.branch"(%476, %arg241, %arg244) <{alternatives = ["then", "else"]}> ({
      ^bb0(%arg247: !data.field_vector<"bls12-381.fr">, %arg248: !data.field_vector<"bls12-381.fr">):
        %479 = "data.dim"(%arg247) <{axis = 0 : i64}> : (!data.field_vector<"bls12-381.fr">) -> ui64
        %480 = "data.dim"(%arg248) <{axis = 0 : i64}> : (!data.field_vector<"bls12-381.fr">) -> ui64
        %481 = "data.index_equal"(%479, %480) : (ui64, ui64) -> i1
        "data.yield"(%481) : (i1) -> ()
      }, {
      ^bb0(%arg245: !data.field_vector<"bls12-381.fr">, %arg246: !data.field_vector<"bls12-381.fr">):
        %478 = "arith.constant"() <{value = false}> : () -> i1
        "data.yield"(%478) : (i1) -> ()
      }) : (i1, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> i1
      "func.return"(%477) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_bd4f0d76e787de675c5732a4a96fc396d45486f32b3dcda5182ccc324969c825", sym_visibility = "private"}> ({
    ^bb0(%arg237: !runtime.scope, %arg238: !runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">, %arg239: !data.field_vector<"bls12-381.fr">, %arg240: !algebra.field<"bls12-381.fr">):
      %469 = "exec.apply"(%arg237, %arg238) <{binding = @zkl_binding_15, parameters = [], site = "s0_unpack_0"}> : (!runtime.scope, !runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">) -> !exec.outcome<>
      "exec.dispatch"(%469)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb1:  // pred: ^bb0
      %470 = "exec.returned"(%arg239, %arg240) : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%470) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%471: !exec.stop):  // pred: ^bb0
      %472 = "exec.failed"(%471) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%472) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7211h6f70656e5f726f756e6473", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_e2f65d17b480da5da0270346faa1bd036c7a5f879e30f4b2b6bac1224b05e394", sym_visibility = "private"}> ({
    ^bb0(%arg232: !runtime.scope, %arg233: !data.field_vector<"bls12-381.fr">, %arg234: !data.field_vector<"bls12-381.fr">, %arg235: !data.field_vector<"bls12-381.fr">, %arg236: !data.field_vector<"bls12-381.fr">):
      %440 = "exec.apply"(%arg232, %arg233) <{binding = @zkl_binding_12, parameters = [], site = "s1"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%440)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%441: !data.field_vector<"bls12-381.fr">, %442: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %443 = "exec.apply"(%arg232, %arg234) <{binding = @zkl_binding_12, parameters = [], site = "s4"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%443)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%444: !exec.stop):  // 11 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb10, ^bb11
      %445 = "exec.failed"(%444) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%445) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb3(%446: !data.field_vector<"bls12-381.fr">, %447: !data.field_vector<"bls12-381.fr">):  // pred: ^bb1
      %448 = "exec.apply"(%arg232, %arg235) <{binding = @zkl_binding_12, parameters = [], site = "s7"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%448)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb4(%449: !data.field_vector<"bls12-381.fr">, %450: !data.field_vector<"bls12-381.fr">):  // pred: ^bb3
      %451 = "exec.apply"(%arg232, %arg236) <{binding = @zkl_binding_12, parameters = [], site = "s10"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%451)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb5(%452: !data.field_vector<"bls12-381.fr">, %453: !data.field_vector<"bls12-381.fr">):  // pred: ^bb4
      %454 = "exec.collect"(%arg232, %441, %446, %449, %452) <{body = @zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_body, domain = @zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_domain, site = "s16"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%454)[^bb6, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb6(%455: !data.field_vector<"bls12-381.fr">):  // pred: ^bb5
      %456 = "exec.apply"(%arg232, %455) <{binding = @zkl_binding_10, parameters = [], site = "s17"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%456)[^bb7, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb7(%457: !algebra.field<"bls12-381.fr">):  // pred: ^bb6
      %458 = "exec.collect"(%arg232, %442, %447, %450, %453) <{body = @zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_body, domain = @zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_domain, site = "s23"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%458)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%459: !data.field_vector<"bls12-381.fr">):  // pred: ^bb7
      %460 = "exec.apply"(%arg232, %459) <{binding = @zkl_binding_10, parameters = [], site = "s24"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%460)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb9(%461: !algebra.field<"bls12-381.fr">):  // pred: ^bb8
      %462 = "exec.collect"(%arg232, %441, %442, %446, %447, %449, %450, %452, %453) <{body = @zkl_map_b02c6bec831af4d953cc5d5558b1dfebb2f6666e509fde68f0a09745680b6577_body, domain = @zkl_map_b02c6bec831af4d953cc5d5558b1dfebb2f6666e509fde68f0a09745680b6577_domain, site = "s34"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%462)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb10(%463: !data.field_vector<"bls12-381.fr">):  // pred: ^bb9
      %464 = "exec.apply"(%arg232, %463) <{binding = @zkl_binding_10, parameters = [], site = "s35"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%464)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb11(%465: !algebra.field<"bls12-381.fr">):  // pred: ^bb10
      %466 = "exec.compute"(%arg232, %457, %461, %465) <{callee = @zkl_ae0ec2b882ea51d896368927e811be493e3af32def2e5ada1525e385646e6229, site = "s37"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%466)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb12(%467: !algebra.field<"bls12-381.fr">):  // pred: ^bb11
      %468 = "exec.returned"(%457, %467, %465) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%468) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7213h726f756e645f6d657373616765", []]} : () -> ()
    "data.domain"() <{function_type = (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, sym_name = "zkl_map_b02c6bec831af4d953cc5d5558b1dfebb2f6666e509fde68f0a09745680b6577_domain", sym_visibility = "private"}> ({
    ^bb0(%arg224: !data.field_vector<"bls12-381.fr">, %arg225: !data.field_vector<"bls12-381.fr">, %arg226: !data.field_vector<"bls12-381.fr">, %arg227: !data.field_vector<"bls12-381.fr">, %arg228: !data.field_vector<"bls12-381.fr">, %arg229: !data.field_vector<"bls12-381.fr">, %arg230: !data.field_vector<"bls12-381.fr">, %arg231: !data.field_vector<"bls12-381.fr">):
      %425 = "data.domain_elements"(%arg224) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %426 = "data.domain_elements"(%arg225) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %427 = "data.domain_zip"(%425, %426) : (!data.domain<!algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      %428 = "data.domain_elements"(%arg226) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %429 = "data.domain_zip"(%427, %428) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      %430 = "data.domain_elements"(%arg227) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %431 = "data.domain_zip"(%429, %430) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      %432 = "data.domain_elements"(%arg228) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %433 = "data.domain_zip"(%431, %432) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      %434 = "data.domain_elements"(%arg229) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %435 = "data.domain_zip"(%433, %434) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      %436 = "data.domain_elements"(%arg230) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %437 = "data.domain_zip"(%435, %436) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      %438 = "data.domain_elements"(%arg231) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %439 = "data.domain_zip"(%437, %438) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%439) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_map_b02c6bec831af4d953cc5d5558b1dfebb2f6666e509fde68f0a09745680b6577_body", sym_visibility = "private"}> ({
    ^bb0(%arg207: !runtime.scope, %arg208: !algebra.field<"bls12-381.fr">, %arg209: !algebra.field<"bls12-381.fr">, %arg210: !algebra.field<"bls12-381.fr">, %arg211: !algebra.field<"bls12-381.fr">, %arg212: !algebra.field<"bls12-381.fr">, %arg213: !algebra.field<"bls12-381.fr">, %arg214: !algebra.field<"bls12-381.fr">, %arg215: !algebra.field<"bls12-381.fr">, %arg216: !data.field_vector<"bls12-381.fr">, %arg217: !data.field_vector<"bls12-381.fr">, %arg218: !data.field_vector<"bls12-381.fr">, %arg219: !data.field_vector<"bls12-381.fr">, %arg220: !data.field_vector<"bls12-381.fr">, %arg221: !data.field_vector<"bls12-381.fr">, %arg222: !data.field_vector<"bls12-381.fr">, %arg223: !data.field_vector<"bls12-381.fr">):
      %420 = "exec.compute"(%arg207, %arg208, %arg209, %arg210, %arg211, %arg212, %arg213, %arg214, %arg215) <{callee = @zkl_f5e0b2f9a4003d8d806a7a288580cf1f30d07d383f870564beff948ccf011d6b, site = "body"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%420)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%421: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %422 = "exec.returned"(%421) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%422) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%423: !exec.stop):  // pred: ^bb0
      %424 = "exec.failed"(%423) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%424) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zkl_map_b02c6bec831af4d953cc5d5558b1dfebb2f6666e509fde68f0a09745680b6577_body", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_f5e0b2f9a4003d8d806a7a288580cf1f30d07d383f870564beff948ccf011d6b", sym_visibility = "private"}> ({
    ^bb0(%arg199: !algebra.field<"bls12-381.fr">, %arg200: !algebra.field<"bls12-381.fr">, %arg201: !algebra.field<"bls12-381.fr">, %arg202: !algebra.field<"bls12-381.fr">, %arg203: !algebra.field<"bls12-381.fr">, %arg204: !algebra.field<"bls12-381.fr">, %arg205: !algebra.field<"bls12-381.fr">, %arg206: !algebra.field<"bls12-381.fr">):
      %406 = "algebra.field_subtract"(%arg200, %arg199) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %407 = "algebra.field_subtract"(%arg202, %arg201) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %408 = "algebra.field_subtract"(%arg204, %arg203) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %409 = "algebra.field_subtract"(%arg206, %arg205) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %410 = "algebra.field_add"(%408, %409) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %411 = "algebra.field_multiply"(%406, %410) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %412 = "algebra.field_multiply"(%408, %arg205) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %413 = "algebra.field_multiply"(%arg203, %409) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %414 = "algebra.field_add"(%412, %413) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %415 = "algebra.field_multiply"(%407, %414) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %416 = "algebra.field_add"(%411, %415) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %417 = "algebra.field_multiply"(%arg201, %408) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %418 = "algebra.field_multiply"(%417, %409) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %419 = "algebra.field_add"(%416, %418) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%419) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_ae0ec2b882ea51d896368927e811be493e3af32def2e5ada1525e385646e6229", sym_visibility = "private"}> ({
    ^bb0(%arg196: !algebra.field<"bls12-381.fr">, %arg197: !algebra.field<"bls12-381.fr">, %arg198: !algebra.field<"bls12-381.fr">):
      %404 = "algebra.field_subtract"(%arg197, %arg196) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %405 = "algebra.field_subtract"(%404, %arg198) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%405) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_36caebca415236dd6aac1763c9a581b89c25a00e62432b484ec92ae08e6a0099", sym_visibility = "private"}> ({
    ^bb0(%arg190: !runtime.scope, %arg191: !data.field_vector<"bls12-381.fr">, %arg192: !data.field_vector<"bls12-381.fr">, %arg193: !data.field_vector<"bls12-381.fr">, %arg194: !data.field_vector<"bls12-381.fr">, %arg195: !algebra.field<"bls12-381.fr">):
      %393 = "func.call"(%arg190, %arg191, %arg195) <{callee = @zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac}> {runtime.site = "s1"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%393)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%394: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %395 = "func.call"(%arg190, %arg192, %arg195) <{callee = @zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac}> {runtime.site = "s3"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%395)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%396: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %397 = "exec.failed"(%396) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "func.return"(%397) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%398: !data.field_vector<"bls12-381.fr">):  // pred: ^bb1
      %399 = "func.call"(%arg190, %arg193, %arg195) <{callee = @zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac}> {runtime.site = "s5"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%399)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb4(%400: !data.field_vector<"bls12-381.fr">):  // pred: ^bb3
      %401 = "func.call"(%arg190, %arg194, %arg195) <{callee = @zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac}> {runtime.site = "s7"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%401)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb5(%402: !data.field_vector<"bls12-381.fr">):  // pred: ^bb4
      %403 = "exec.returned"(%394, %398, %400, %402) : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "func.return"(%403) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b729h6669785f6761746573", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac", sym_visibility = "private"}> ({
    ^bb0(%arg187: !runtime.scope, %arg188: !data.field_vector<"bls12-381.fr">, %arg189: !algebra.field<"bls12-381.fr">):
      %385 = "exec.apply"(%arg187, %arg188) <{binding = @zkl_binding_12, parameters = [], site = "s0"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%385)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%386: !data.field_vector<"bls12-381.fr">, %387: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %388 = "exec.collect"(%arg187, %386, %387, %arg189) <{body = @zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_body, domain = @zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_domain, site = "s4"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%388)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%389: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %390 = "exec.failed"(%389) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%390) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%391: !data.field_vector<"bls12-381.fr">):  // pred: ^bb1
      %392 = "exec.returned"(%391) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%392) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b723h666978", []]} : () -> ()
    "data.domain"() <{function_type = (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, sym_name = "zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_domain", sym_visibility = "private"}> ({
    ^bb0(%arg185: !data.field_vector<"bls12-381.fr">, %arg186: !data.field_vector<"bls12-381.fr">):
      %382 = "data.domain_elements"(%arg185) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %383 = "data.domain_elements"(%arg186) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %384 = "data.domain_zip"(%382, %383) : (!data.domain<!algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%384) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_body", sym_visibility = "private"}> ({
    ^bb0(%arg179: !runtime.scope, %arg180: !algebra.field<"bls12-381.fr">, %arg181: !algebra.field<"bls12-381.fr">, %arg182: !data.field_vector<"bls12-381.fr">, %arg183: !data.field_vector<"bls12-381.fr">, %arg184: !algebra.field<"bls12-381.fr">):
      %377 = "exec.compute"(%arg179, %arg180, %arg181, %arg184) <{callee = @zkl_9de40b3e39acd7da53c8d9f1ec759779b60f4d0d3b7314f8741f798f050dbfd1, site = "body"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%377)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%378: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %379 = "exec.returned"(%378) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%379) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%380: !exec.stop):  // pred: ^bb0
      %381 = "exec.failed"(%380) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%381) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_body", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_9de40b3e39acd7da53c8d9f1ec759779b60f4d0d3b7314f8741f798f050dbfd1", sym_visibility = "private"}> ({
    ^bb0(%arg176: !algebra.field<"bls12-381.fr">, %arg177: !algebra.field<"bls12-381.fr">, %arg178: !algebra.field<"bls12-381.fr">):
      %374 = "algebra.field_subtract"(%arg177, %arg176) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %375 = "algebra.field_multiply"(%374, %arg178) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %376 = "algebra.field_add"(%arg176, %375) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%376) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_bcddf8825098d44ae9ce732a7b45754c16637e2a47a4c9f29ef9a21612daeaa3", sym_visibility = "private"}> ({
    ^bb0(%arg173: !runtime.scope, %arg174: !data.field_vector<"bls12-381.fr">, %arg175: !algebra.field<"bls12-381.fr">):
      %369 = "exec.apply"(%arg173) <{binding = @zkl_binding_14, parameters = [], site = "s0_create_0"}> : (!runtime.scope) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">)>
      "exec.dispatch"(%369)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">)>) -> ()
    ^bb1(%370: !runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">):  // pred: ^bb0
      %371 = "exec.returned"(%370, %arg174, %arg175) : (!runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%371) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%372: !exec.stop):  // pred: ^bb0
      %373 = "exec.failed"(%372) : (!exec.stop) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%373) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_7a6404beff2b3202f4e73aaa336c7f5379ab99d8d6bd07e4f30061716d1ad4d1">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b729h61745f707265666978", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_cfcf40daaab145a916368cf7a01eccd9ba0e536fbbc30a06c4a25e7ec96ecbe7", sym_visibility = "private"}> ({
    ^bb0(%arg171: !runtime.scope, %arg172: !data.field_vector<"bls12-381.fr">):
      %340 = "exec.apply"(%arg171, %arg172) <{binding = @zkl_binding_2, parameters = [], site = "s0"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%340)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%341: ui64):  // pred: ^bb0
      %342 = "exec.apply"(%arg171) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s1"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%342)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%343: !exec.stop):  // 10 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb6, ^bb7, ^bb9, ^bb10, ^bb12, ^bb13
      %344 = "exec.failed"(%343) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "func.return"(%344) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%345: ui64):  // pred: ^bb1
      %346 = "exec.apply"(%arg171, %341, %345) <{binding = @zkl_binding_4, parameters = [], site = "s2"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%346)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb4(%347: i1):  // pred: ^bb3
      %348 = "exec.test"(%arg171, %347) <{site = "s4"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%348)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb5(%349: i1):  // pred: ^bb4
      "cf.cond_br"(%349)[^bb6, ^bb7] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb6:  // pred: ^bb5
      %350 = "runtime.enter_scope"(%arg171, %arg172) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "then", site = "s4"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%350)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // pred: ^bb5
      %351 = "runtime.enter_scope"(%arg171, %arg172) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "else", site = "s4"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%351)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb8(%352: !data.field_vector<"bls12-381.fr">, %353: !data.field_vector<"bls12-381.fr">):  // 2 preds: ^bb11, ^bb14
      %354 = "exec.returned"(%352, %353) : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "func.return"(%354) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb9(%355: !runtime.scope):  // pred: ^bb6
      %356 = "func.call"(%355, %arg172) <{callee = @zkl_control_21}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      %357 = "runtime.exit_scope"(%355, %356) : (!runtime.scope, !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>)>
      "exec.dispatch"(%357)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>)>) -> ()
    ^bb10(%358: !runtime.transfer<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>):  // pred: ^bb9
      %359 = "runtime.accept_transfer"(%arg171, %358) : (!runtime.scope, !runtime.transfer<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%359)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb11(%360: !data.field_vector<"bls12-381.fr">, %361: !data.field_vector<"bls12-381.fr">):  // pred: ^bb10
      "cf.br"(%360, %361)[^bb8] : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> ()
    ^bb12(%362: !runtime.scope):  // pred: ^bb7
      %363 = "func.call"(%362, %arg172) <{callee = @zkl_control_22}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      %364 = "runtime.exit_scope"(%362, %363) : (!runtime.scope, !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>)>
      "exec.dispatch"(%364)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>)>) -> ()
    ^bb13(%365: !runtime.transfer<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>):  // pred: ^bb12
      %366 = "runtime.accept_transfer"(%arg171, %365) : (!runtime.scope, !runtime.transfer<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%366)[^bb14, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb14(%367: !data.field_vector<"bls12-381.fr">, %368: !data.field_vector<"bls12-381.fr">):  // pred: ^bb13
      "cf.br"(%367, %368)[^bb8] : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> ()
    }) {runtime.origin = ["s3h676b7211h73706c69745f706f696e74", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_21", sym_visibility = "private"}> ({
    ^bb0(%arg169: !runtime.scope, %arg170: !data.field_vector<"bls12-381.fr">):
      %339 = "exec.complete"(%arg169, %arg170, %arg170) : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "func.return"(%339) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_22", sym_visibility = "private"}> ({
    ^bb0(%arg167: !runtime.scope, %arg168: !data.field_vector<"bls12-381.fr">):
      %333 = "exec.apply"(%arg167, %arg168) <{binding = @zkl_binding_12, parameters = [], site = "s7"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%333)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%334: !data.field_vector<"bls12-381.fr">, %335: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %336 = "exec.complete"(%arg167, %334, %335) : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "func.return"(%336) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%337: !exec.stop):  // pred: ^bb0
      %338 = "exec.failed"(%337) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "func.return"(%338) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_91fe8ea73b5db3432f90fc8fe9725c8455fce8782b4cc4d2839d05826de71b8f", sym_visibility = "private"}> ({
    ^bb0(%arg162: !runtime.scope, %arg163: !data.field_vector<"bls12-381.fr">, %arg164: !data.field_vector<"bls12-381.fr">, %arg165: !data.field_vector<"bls12-381.fr">, %arg166: ui64):
      %295 = "exec.apply"(%arg162) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%295)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%296: ui64):  // pred: ^bb0
      %297 = "exec.apply"(%arg162, %arg166, %296) <{binding = @zkl_binding_7, parameters = [], site = "s1"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%297)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%298: !exec.stop):  // 9 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb11, ^bb13
      %299 = "exec.failed"(%298) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%299) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%300: ui64):  // pred: ^bb1
      %301 = "exec.apply"(%arg162) <{binding = @zkl_binding_8, parameters = [], site = "s3"}> : (!runtime.scope) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%301)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb4(%302: !data.field_vector<"bls12-381.fr">):  // pred: ^bb3
      %303 = "func.call"(%arg162, %302, %arg166, %arg163) <{callee = @zkl_3469bbe358bfad3d167fe48bcafbbc14c8c1d7293ef83ba9b5a8953626c1c272}> {runtime.site = "s5"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%303)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb5(%304: !data.field_vector<"bls12-381.fr">):  // pred: ^bb4
      %305 = "exec.apply"(%arg162) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s7"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%305)[^bb6, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb6(%306: ui64):  // pred: ^bb5
      %307 = "exec.apply"(%arg162) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s9"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%307)[^bb7, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb7(%308: ui64):  // pred: ^bb6
      %309 = "exec.range"(%arg162, %308, %arg166) <{site = "s13"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%309)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i64, i64)>) -> ()
    ^bb8(%310: i64, %311: i64):  // pred: ^bb7
      %312 = "runtime.borrow_transfer"(%arg162, %304, %306) : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>
      "cf.br"(%310, %312)[^bb9] : (i64, !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb9(%313: i64, %314: !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>):  // 2 preds: ^bb8, ^bb12
      %315 = "arith.cmpi"(%313, %311) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%315, %314)[^bb10, ^bb11] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb10:  // pred: ^bb9
      %316 = "runtime.iteration"(%arg162, %313) <{site = "s13"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%316)[^bb14, ^bb13] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb11(%317: !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>):  // pred: ^bb9
      %318 = "runtime.accept_transfer"(%arg162, %317) : (!runtime.scope, !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>
      "exec.dispatch"(%318)[^bb17, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb12(%319: !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>):  // pred: ^bb16
      %320 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %321 = "arith.addi"(%313, %320) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%321, %319)[^bb9] : (i64, !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb13(%322: !exec.stop):  // 3 preds: ^bb10, ^bb14, ^bb15
      "runtime.release_transfer"(%314) : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
      "cf.br"(%322)[^bb2] : (!exec.stop) -> ()
    ^bb14(%323: ui64):  // pred: ^bb10
      %324:2 = "runtime.transfer_values"(%314) : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> (!data.field_vector<"bls12-381.fr">, ui64)
      %325 = "runtime.enter_scope"(%arg162, %313, %323, %324#0, %324#1, %arg164, %arg165, %300) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 6>, site = "s13"}> : (!runtime.scope, i64, ui64, !data.field_vector<"bls12-381.fr">, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%325)[^bb15, ^bb13] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb15(%326: !runtime.scope):  // pred: ^bb14
      %327 = "func.call"(%326, %323, %324#0, %324#1, %arg164, %arg165, %300) <{callee = @zkl_control_23}> : (!runtime.scope, ui64, !data.field_vector<"bls12-381.fr">, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>
      %328 = "runtime.exit_scope"(%326, %327) : (!runtime.scope, !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>) -> !exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>)>
      "exec.dispatch"(%328)[^bb16, ^bb13] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>)>) -> ()
    ^bb16(%329: !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>):  // pred: ^bb15
      "runtime.release_transfer"(%314) : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
      "cf.br"(%329)[^bb12] : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb17(%330: !data.field_vector<"bls12-381.fr">, %331: ui64):  // pred: ^bb11
      %332 = "exec.returned"(%330) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%332) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7217h6c696e655f636f656666696369656e7473", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, !data.field_vector<"bls12-381.fr">, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>, no_inline, sym_name = "zkl_control_23", sym_visibility = "private"}> ({
    ^bb0(%arg155: !runtime.scope, %arg156: ui64, %arg157: !data.field_vector<"bls12-381.fr">, %arg158: ui64, %arg159: !data.field_vector<"bls12-381.fr">, %arg160: !data.field_vector<"bls12-381.fr">, %arg161: ui64):
      %271 = "func.call"(%arg155, %arg159, %arg158) <{callee = @zkl_6ba53ec68a0230031d706e4a93e78f80425c51108d34ecc0a5aa5681eded9c8e}> {runtime.site = "s14"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%271)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%272: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %273 = "func.call"(%arg155, %arg160, %arg158) <{callee = @zkl_6ba53ec68a0230031d706e4a93e78f80425c51108d34ecc0a5aa5681eded9c8e}> {runtime.site = "s16"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%273)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%274: !exec.stop):  // 10 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb10
      %275 = "exec.failed"(%274) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>
      "func.return"(%275) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb3(%276: !algebra.field<"bls12-381.fr">):  // pred: ^bb1
      %277 = "exec.apply"(%arg155, %arg157) <{binding = @zkl_binding_12, parameters = [], site = "s18"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%277)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb4(%278: !data.field_vector<"bls12-381.fr">, %279: !data.field_vector<"bls12-381.fr">):  // pred: ^bb3
      %280 = "exec.collect"(%arg155, %278, %279, %272) <{body = @zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_body, domain = @zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_domain, site = "s22"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%280)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb5(%281: !data.field_vector<"bls12-381.fr">):  // pred: ^bb4
      %282 = "exec.compute"(%arg155, %276, %272) <{callee = @zkl_c15efd5f24b71cb9e6e3766d00c208e0a0014177a6ae1e9dd67b23bda4eff8ab, site = "s26"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%282)[^bb6, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb6(%283: !algebra.field<"bls12-381.fr">):  // pred: ^bb5
      %284 = "exec.collect"(%arg155, %278, %279, %283) <{body = @zkl_map_f8f9614d3bd7d4196ffb7d73d3d80b5571e091e9fdbaeb4adc8aa23e703bd4a5_body, domain = @zkl_map_f8f9614d3bd7d4196ffb7d73d3d80b5571e091e9fdbaeb4adc8aa23e703bd4a5_domain, site = "s27"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%284)[^bb7, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb7(%285: !data.field_vector<"bls12-381.fr">):  // pred: ^bb6
      %286 = "func.call"(%arg155, %285, %arg161) <{callee = @zkl_3d3958243128671a7ae06c730aba5c78b4cae61932510ab43ba5bcabe7324295}> {runtime.site = "s29"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%286)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%287: !data.field_vector<"bls12-381.fr">):  // pred: ^bb7
      %288 = "exec.collect"(%arg155, %281, %287) <{body = @zkl_map_b7eb5d68e6edd9e938f02a44220440e7b9e5f3fe195e305a87f963f93affd321_body, domain = @zkl_map_b7eb5d68e6edd9e938f02a44220440e7b9e5f3fe195e305a87f963f93affd321_domain, site = "s30"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%288)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb9(%289: !data.field_vector<"bls12-381.fr">):  // pred: ^bb8
      %290 = "exec.apply"(%arg155) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s32"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%290)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb10(%291: ui64):  // pred: ^bb9
      %292 = "exec.apply"(%arg155, %arg158, %291) <{binding = @zkl_binding_7, parameters = [], site = "s33"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%292)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb11(%293: ui64):  // pred: ^bb10
      %294 = "exec.complete"(%arg155, %289, %293) : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>
      "func.return"(%294) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    }) {runtime.region} : () -> ()
    "data.domain"() <{function_type = (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, sym_name = "zkl_map_f8f9614d3bd7d4196ffb7d73d3d80b5571e091e9fdbaeb4adc8aa23e703bd4a5_domain", sym_visibility = "private"}> ({
    ^bb0(%arg153: !data.field_vector<"bls12-381.fr">, %arg154: !data.field_vector<"bls12-381.fr">):
      %268 = "data.domain_elements"(%arg153) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %269 = "data.domain_elements"(%arg154) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %270 = "data.domain_zip"(%268, %269) : (!data.domain<!algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%270) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_map_f8f9614d3bd7d4196ffb7d73d3d80b5571e091e9fdbaeb4adc8aa23e703bd4a5_body", sym_visibility = "private"}> ({
    ^bb0(%arg147: !runtime.scope, %arg148: !algebra.field<"bls12-381.fr">, %arg149: !algebra.field<"bls12-381.fr">, %arg150: !data.field_vector<"bls12-381.fr">, %arg151: !data.field_vector<"bls12-381.fr">, %arg152: !algebra.field<"bls12-381.fr">):
      %263 = "exec.compute"(%arg147, %arg148, %arg149, %arg152) <{callee = @zkl_c8eacd293248ba42cad22bd955e2dec7c6105efe1dabf391c3a74b436be7412e, site = "body"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%263)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%264: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %265 = "exec.returned"(%264) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%265) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%266: !exec.stop):  // pred: ^bb0
      %267 = "exec.failed"(%266) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%267) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zkl_map_f8f9614d3bd7d4196ffb7d73d3d80b5571e091e9fdbaeb4adc8aa23e703bd4a5_body", []]} : () -> ()
    "data.domain"() <{function_type = (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, sym_name = "zkl_map_b7eb5d68e6edd9e938f02a44220440e7b9e5f3fe195e305a87f963f93affd321_domain", sym_visibility = "private"}> ({
    ^bb0(%arg145: !data.field_vector<"bls12-381.fr">, %arg146: !data.field_vector<"bls12-381.fr">):
      %260 = "data.domain_elements"(%arg145) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %261 = "data.domain_elements"(%arg146) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %262 = "data.domain_zip"(%260, %261) : (!data.domain<!algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%262) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_map_b7eb5d68e6edd9e938f02a44220440e7b9e5f3fe195e305a87f963f93affd321_body", sym_visibility = "private"}> ({
    ^bb0(%arg140: !runtime.scope, %arg141: !algebra.field<"bls12-381.fr">, %arg142: !algebra.field<"bls12-381.fr">, %arg143: !data.field_vector<"bls12-381.fr">, %arg144: !data.field_vector<"bls12-381.fr">):
      %255 = "exec.compute"(%arg140, %arg141, %arg142) <{callee = @zkl_02aa9bd9900f843069baf97f23f4f5ccab54b136c8fed5b90842e4c46b7e5fcd, site = "body"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%255)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%256: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %257 = "exec.returned"(%256) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%257) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%258: !exec.stop):  // pred: ^bb0
      %259 = "exec.failed"(%258) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%259) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zkl_map_b7eb5d68e6edd9e938f02a44220440e7b9e5f3fe195e305a87f963f93affd321_body", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_f9bc3972b3acce79409bfe72125c3b04de4dbb81a13d1dfbc918146c1354315c", sym_visibility = "private"}> ({
    ^bb0(%arg136: !runtime.scope, %arg137: !data.field_vector<"bls12-381.fr">, %arg138: !algebra.field<"bls12-381.fr">, %arg139: ui64):
      %250 = "func.call"(%arg136, %arg137, %arg138, %arg139) <{callee = @zkl_8184464d79b9512ca72dac4d64d1ba3d187fd1efb0b8118690b5a104ab35f351}> {runtime.site = "s2"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%250)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%251: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %252 = "exec.returned"(%251) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%252) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%253: !exec.stop):  // pred: ^bb0
      %254 = "exec.failed"(%253) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%254) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zks_dab24f1af4cf6ec12b12d53d6ef952d45bf4866eaa489b84bfcce536b42b3f2a", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_8184464d79b9512ca72dac4d64d1ba3d187fd1efb0b8118690b5a104ab35f351", sym_visibility = "private"}> ({
    ^bb0(%arg132: !runtime.scope, %arg133: !data.field_vector<"bls12-381.fr">, %arg134: !algebra.field<"bls12-381.fr">, %arg135: ui64):
      %241 = "exec.apply"(%arg132, %arg133, %arg134) <{binding = @zkl_binding_9, parameters = [], site = "s0"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%241)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%242: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %243 = "exec.compute"(%arg132) <{callee = @zkl_e38306e1154810613f8b855b4e24394048cbbd4c4b2723722235b0e03496f137, site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%243)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%244: !exec.stop):  // 3 preds: ^bb0, ^bb1, ^bb3
      %245 = "exec.failed"(%244) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%245) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%246: !algebra.field<"bls12-381.fr">):  // pred: ^bb1
      %247 = "func.call"(%arg132, %242, %246, %arg135) <{callee = @zkl_fbd2531b804047766f8107241edd0ea81368b70795e44e4d8e07484d142783bb}> {runtime.site = "s2"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%247)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb4(%248: !data.field_vector<"bls12-381.fr">):  // pred: ^bb3
      %249 = "exec.returned"(%248) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%249) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7212h636f6e7374616e745f726f77", []]} : () -> ()
    "func.func"() <{function_type = () -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_e38306e1154810613f8b855b4e24394048cbbd4c4b2723722235b0e03496f137", sym_visibility = "private"}> ({
      %240 = "algebra.constant"() <{value = #algebra.literal<<"bls12-381.fr">, 0 : ui255> : !algebra.field<"bls12-381.fr">}> : () -> !algebra.field<"bls12-381.fr">
      "func.return"(%240) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_3469bbe358bfad3d167fe48bcafbbc14c8c1d7293ef83ba9b5a8953626c1c272", sym_visibility = "private"}> ({
    ^bb0(%arg128: !runtime.scope, %arg129: !data.field_vector<"bls12-381.fr">, %arg130: ui64, %arg131: !data.field_vector<"bls12-381.fr">):
      %235 = "exec.fold"(%arg128, %arg131, %arg129, %arg130) <{domain = @finite_zkl_3469bbe358bfad3d167fe48bcafbbc14c8c1d7293ef83ba9b5a8953626c1c272_s0_domain, site = "s0", step = @finite_zkl_3469bbe358bfad3d167fe48bcafbbc14c8c1d7293ef83ba9b5a8953626c1c272_s0_body}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%235)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%236: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %237 = "exec.returned"(%236) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%237) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%238: !exec.stop):  // pred: ^bb0
      %239 = "exec.failed"(%238) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%239) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_3469bbe358bfad3d167fe48bcafbbc14c8c1d7293ef83ba9b5a8953626c1c272_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg127: !data.field_vector<"bls12-381.fr">):
      %234 = "data.domain_elements"(%arg127) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%234) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "finite_zkl_3469bbe358bfad3d167fe48bcafbbc14c8c1d7293ef83ba9b5a8953626c1c272_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg122: !runtime.scope, %arg123: !data.field_vector<"bls12-381.fr">, %arg124: !algebra.field<"bls12-381.fr">, %arg125: !data.field_vector<"bls12-381.fr">, %arg126: ui64):
      %229 = "func.call"(%arg122, %arg123, %arg124, %arg126) <{callee = @zkl_f9bc3972b3acce79409bfe72125c3b04de4dbb81a13d1dfbc918146c1354315c}> {runtime.site = "body"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%229)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%230: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %231 = "exec.returned"(%230) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%231) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%232: !exec.stop):  // pred: ^bb0
      %233 = "exec.failed"(%232) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%233) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["finite_zkl_3469bbe358bfad3d167fe48bcafbbc14c8c1d7293ef83ba9b5a8953626c1c272_s0_body", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_6ba53ec68a0230031d706e4a93e78f80425c51108d34ecc0a5aa5681eded9c8e", sym_visibility = "private"}> ({
    ^bb0(%arg119: !runtime.scope, %arg120: !data.field_vector<"bls12-381.fr">, %arg121: ui64):
      %219 = "exec.compute"(%arg119) <{callee = @zkl_e38306e1154810613f8b855b4e24394048cbbd4c4b2723722235b0e03496f137, site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%219)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%220: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %221 = "exec.apply"(%arg119) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s1"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%221)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%222: !exec.stop):  // 3 preds: ^bb0, ^bb1, ^bb3
      %223 = "exec.failed"(%222) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%223) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb3(%224: ui64):  // pred: ^bb1
      %225 = "func.call"(%arg119, %220, %224, %arg121, %arg120) <{callee = @zkl_6f8eb32a4f0b93bfe3d0d50d004bd6c86105c5dd9a81d4d8d243770d376651c8}> {runtime.site = "s5"} : (!runtime.scope, !algebra.field<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
      "exec.dispatch"(%225)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb4(%226: !algebra.field<"bls12-381.fr">, %227: ui64):  // pred: ^bb3
      %228 = "exec.returned"(%226) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%228) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b727h656c656d656e74", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, ui64, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>, no_inline, sym_name = "zkl_09043a1369ab6c082f8534fc9d21f34f77067e68b9a4c2a907a132342ff59811", sym_visibility = "private"}> ({
    ^bb0(%arg114: !runtime.scope, %arg115: !algebra.field<"bls12-381.fr">, %arg116: ui64, %arg117: !algebra.field<"bls12-381.fr">, %arg118: ui64):
      %193 = "exec.apply"(%arg114, %arg116, %arg118) <{binding = @zkl_binding_4, parameters = [], site = "s3"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%193)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%194: i1):  // pred: ^bb0
      %195 = "exec.test"(%arg114, %194) <{site = "s6"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%195)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%196: !exec.stop):  // 10 preds: ^bb0, ^bb1, ^bb4, ^bb5, ^bb6, ^bb7, ^bb8, ^bb10, ^bb11, ^bb13
      %197 = "exec.failed"(%196) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%197) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb3(%198: i1):  // pred: ^bb1
      "cf.cond_br"(%198)[^bb4, ^bb5] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb4:  // pred: ^bb3
      %199 = "runtime.enter_scope"(%arg114, %arg115, %arg117) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "then", site = "s6"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%199)[^bb7, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb5:  // pred: ^bb3
      %200 = "runtime.enter_scope"(%arg114, %arg115, %arg117) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "else", site = "s6"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%200)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6(%201: !algebra.field<"bls12-381.fr">):  // 2 preds: ^bb9, ^bb12
      %202 = "exec.apply"(%arg114) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s11"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%202)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb7(%203: !runtime.scope):  // pred: ^bb4
      %204 = "func.call"(%203, %arg115, %arg117) <{callee = @zkl_control_24}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      %205 = "runtime.exit_scope"(%203, %204) : (!runtime.scope, !exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!algebra.field<"bls12-381.fr">)>)>
      "exec.dispatch"(%205)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!algebra.field<"bls12-381.fr">)>)>) -> ()
    ^bb8(%206: !runtime.transfer<(!algebra.field<"bls12-381.fr">)>):  // pred: ^bb7
      %207 = "runtime.accept_transfer"(%arg114, %206) : (!runtime.scope, !runtime.transfer<(!algebra.field<"bls12-381.fr">)>) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%207)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb9(%208: !algebra.field<"bls12-381.fr">):  // pred: ^bb8
      "cf.br"(%208)[^bb6] : (!algebra.field<"bls12-381.fr">) -> ()
    ^bb10(%209: !runtime.scope):  // pred: ^bb5
      %210 = "func.call"(%209, %arg115, %arg117) <{callee = @zkl_control_25}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      %211 = "runtime.exit_scope"(%209, %210) : (!runtime.scope, !exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!algebra.field<"bls12-381.fr">)>)>
      "exec.dispatch"(%211)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!algebra.field<"bls12-381.fr">)>)>) -> ()
    ^bb11(%212: !runtime.transfer<(!algebra.field<"bls12-381.fr">)>):  // pred: ^bb10
      %213 = "runtime.accept_transfer"(%arg114, %212) : (!runtime.scope, !runtime.transfer<(!algebra.field<"bls12-381.fr">)>) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%213)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb12(%214: !algebra.field<"bls12-381.fr">):  // pred: ^bb11
      "cf.br"(%214)[^bb6] : (!algebra.field<"bls12-381.fr">) -> ()
    ^bb13(%215: ui64):  // pred: ^bb6
      %216 = "exec.apply"(%arg114, %arg116, %215) <{binding = @zkl_binding_7, parameters = [], site = "s12"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%216)[^bb14, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb14(%217: ui64):  // pred: ^bb13
      %218 = "exec.returned"(%201, %217) : (!algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%218) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>) -> ()
    }) {runtime.origin = ["zks_09bf7b2d0f9a7fa09310de095093a32f6884e18e73addb2f7bae58f6b7c6de5b", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_24", sym_visibility = "private"}> ({
    ^bb0(%arg111: !runtime.scope, %arg112: !algebra.field<"bls12-381.fr">, %arg113: !algebra.field<"bls12-381.fr">):
      %192 = "exec.complete"(%arg111, %arg113) : (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%192) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_25", sym_visibility = "private"}> ({
    ^bb0(%arg108: !runtime.scope, %arg109: !algebra.field<"bls12-381.fr">, %arg110: !algebra.field<"bls12-381.fr">):
      %191 = "exec.complete"(%arg108, %arg109) : (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%191) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>, no_inline, sym_name = "zkl_6f8eb32a4f0b93bfe3d0d50d004bd6c86105c5dd9a81d4d8d243770d376651c8", sym_visibility = "private"}> ({
    ^bb0(%arg103: !runtime.scope, %arg104: !algebra.field<"bls12-381.fr">, %arg105: ui64, %arg106: ui64, %arg107: !data.field_vector<"bls12-381.fr">):
      %185 = "exec.fold"(%arg103, %arg107, %arg104, %arg105, %arg106) <{domain = @finite_zkl_6f8eb32a4f0b93bfe3d0d50d004bd6c86105c5dd9a81d4d8d243770d376651c8_s0_domain, site = "s0", step = @finite_zkl_6f8eb32a4f0b93bfe3d0d50d004bd6c86105c5dd9a81d4d8d243770d376651c8_s0_body}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
      "exec.dispatch"(%185)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb1(%186: !algebra.field<"bls12-381.fr">, %187: ui64):  // pred: ^bb0
      %188 = "exec.returned"(%186, %187) : (!algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%188) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb2(%189: !exec.stop):  // pred: ^bb0
      %190 = "exec.failed"(%189) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%190) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_6f8eb32a4f0b93bfe3d0d50d004bd6c86105c5dd9a81d4d8d243770d376651c8_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg102: !data.field_vector<"bls12-381.fr">):
      %184 = "data.domain_elements"(%arg102) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%184) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, ui64, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>, no_inline, sym_name = "finite_zkl_6f8eb32a4f0b93bfe3d0d50d004bd6c86105c5dd9a81d4d8d243770d376651c8_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg96: !runtime.scope, %arg97: !algebra.field<"bls12-381.fr">, %arg98: ui64, %arg99: !algebra.field<"bls12-381.fr">, %arg100: !data.field_vector<"bls12-381.fr">, %arg101: ui64):
      %178 = "func.call"(%arg96, %arg97, %arg98, %arg99, %arg101) <{callee = @zkl_09043a1369ab6c082f8534fc9d21f34f77067e68b9a4c2a907a132342ff59811}> {runtime.site = "body"} : (!runtime.scope, !algebra.field<"bls12-381.fr">, ui64, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
      "exec.dispatch"(%178)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb1(%179: !algebra.field<"bls12-381.fr">, %180: ui64):  // pred: ^bb0
      %181 = "exec.returned"(%179, %180) : (!algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%181) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb2(%182: !exec.stop):  // pred: ^bb0
      %183 = "exec.failed"(%182) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%183) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>) -> ()
    }) {runtime.origin = ["finite_zkl_6f8eb32a4f0b93bfe3d0d50d004bd6c86105c5dd9a81d4d8d243770d376651c8_s0_body", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_c15efd5f24b71cb9e6e3766d00c208e0a0014177a6ae1e9dd67b23bda4eff8ab", sym_visibility = "private"}> ({
    ^bb0(%arg94: !algebra.field<"bls12-381.fr">, %arg95: !algebra.field<"bls12-381.fr">):
      %177 = "algebra.field_subtract"(%arg94, %arg95) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%177) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_c8eacd293248ba42cad22bd955e2dec7c6105efe1dabf391c3a74b436be7412e", sym_visibility = "private"}> ({
    ^bb0(%arg91: !algebra.field<"bls12-381.fr">, %arg92: !algebra.field<"bls12-381.fr">, %arg93: !algebra.field<"bls12-381.fr">):
      %175 = "algebra.field_subtract"(%arg92, %arg91) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %176 = "algebra.field_multiply"(%175, %arg93) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%176) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_3d3958243128671a7ae06c730aba5c78b4cae61932510ab43ba5bcabe7324295", sym_visibility = "private"}> ({
    ^bb0(%arg88: !runtime.scope, %arg89: !data.field_vector<"bls12-381.fr">, %arg90: ui64):
      %162 = "exec.apply"(%arg88) <{binding = @zkl_binding_8, parameters = [], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%162)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%163: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %164 = "exec.compute"(%arg88) <{callee = @zkl_e38306e1154810613f8b855b4e24394048cbbd4c4b2723722235b0e03496f137, site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%164)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%165: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %166 = "exec.failed"(%165) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%166) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%167: !algebra.field<"bls12-381.fr">):  // pred: ^bb1
      %168 = "exec.apply"(%arg88) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s2"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%168)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%169: ui64):  // pred: ^bb3
      %170 = "func.call"(%arg88, %163, %167, %169, %arg90, %arg89) <{callee = @zkl_d1c2bba308747260f914c193c146ad509308d619c2f75ba22eb051531fbbe7ca}> {runtime.site = "s6"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
      "exec.dispatch"(%170)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb5(%171: !data.field_vector<"bls12-381.fr">, %172: !algebra.field<"bls12-381.fr">, %173: ui64):  // pred: ^bb4
      %174 = "exec.returned"(%171) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%174) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7210h73686966745f726f7773", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>, no_inline, sym_name = "zkl_abd6f98141af14ddf8b9152129fb3a9fb361b5735ade780e8d1c876d68deb283", sym_visibility = "private"}> ({
    ^bb0(%arg82: !runtime.scope, %arg83: !data.field_vector<"bls12-381.fr">, %arg84: !algebra.field<"bls12-381.fr">, %arg85: ui64, %arg86: !algebra.field<"bls12-381.fr">, %arg87: ui64):
      %130 = "exec.apply"(%arg82, %arg85, %arg87) <{binding = @zkl_binding_3, parameters = [], site = "s4"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%130)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%131: ui64):  // pred: ^bb0
      %132 = "exec.apply"(%arg82) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s5"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%132)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%133: !exec.stop):  // 13 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb6, ^bb7, ^bb8, ^bb9, ^bb10, ^bb12, ^bb13, ^bb15, ^bb16
      %134 = "exec.failed"(%133) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%134) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb3(%135: ui64):  // pred: ^bb1
      %136 = "exec.apply"(%arg82, %131, %135) <{binding = @zkl_binding_4, parameters = [], site = "s6"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%136)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb4(%137: i1):  // pred: ^bb3
      %138 = "exec.test"(%arg82, %137) <{site = "s8"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%138)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb5(%139: i1):  // pred: ^bb4
      "cf.cond_br"(%139)[^bb6, ^bb7] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb6:  // pred: ^bb5
      %140 = "runtime.enter_scope"(%arg82, %arg84) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "then", site = "s8"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%140)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // pred: ^bb5
      %141 = "runtime.enter_scope"(%arg82, %arg84) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "else", site = "s8"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%141)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb8(%142: !algebra.field<"bls12-381.fr">):  // 2 preds: ^bb11, ^bb14
      %143 = "exec.apply"(%arg82, %arg83, %142) <{binding = @zkl_binding_9, parameters = [], site = "s13"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%143)[^bb15, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb9(%144: !runtime.scope):  // pred: ^bb6
      %145 = "func.call"(%144, %arg84) <{callee = @zkl_control_26}> : (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      %146 = "runtime.exit_scope"(%144, %145) : (!runtime.scope, !exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!algebra.field<"bls12-381.fr">)>)>
      "exec.dispatch"(%146)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!algebra.field<"bls12-381.fr">)>)>) -> ()
    ^bb10(%147: !runtime.transfer<(!algebra.field<"bls12-381.fr">)>):  // pred: ^bb9
      %148 = "runtime.accept_transfer"(%arg82, %147) : (!runtime.scope, !runtime.transfer<(!algebra.field<"bls12-381.fr">)>) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%148)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb11(%149: !algebra.field<"bls12-381.fr">):  // pred: ^bb10
      "cf.br"(%149)[^bb8] : (!algebra.field<"bls12-381.fr">) -> ()
    ^bb12(%150: !runtime.scope):  // pred: ^bb7
      %151 = "func.call"(%150, %arg84) <{callee = @zkl_control_27}> : (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      %152 = "runtime.exit_scope"(%150, %151) : (!runtime.scope, !exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!algebra.field<"bls12-381.fr">)>)>
      "exec.dispatch"(%152)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!algebra.field<"bls12-381.fr">)>)>) -> ()
    ^bb13(%153: !runtime.transfer<(!algebra.field<"bls12-381.fr">)>):  // pred: ^bb12
      %154 = "runtime.accept_transfer"(%arg82, %153) : (!runtime.scope, !runtime.transfer<(!algebra.field<"bls12-381.fr">)>) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%154)[^bb14, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb14(%155: !algebra.field<"bls12-381.fr">):  // pred: ^bb13
      "cf.br"(%155)[^bb8] : (!algebra.field<"bls12-381.fr">) -> ()
    ^bb15(%156: !data.field_vector<"bls12-381.fr">):  // pred: ^bb8
      %157 = "exec.apply"(%arg82) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s15"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%157)[^bb16, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb16(%158: ui64):  // pred: ^bb15
      %159 = "exec.apply"(%arg82, %arg85, %158) <{binding = @zkl_binding_7, parameters = [], site = "s16"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%159)[^bb17, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb17(%160: ui64):  // pred: ^bb16
      %161 = "exec.returned"(%156, %arg86, %160) : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%161) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>) -> ()
    }) {runtime.origin = ["zks_8581fd068387f06c481369dff1456320f16962167c6391f3d8bc1fe2a6daf333", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_26", sym_visibility = "private"}> ({
    ^bb0(%arg80: !runtime.scope, %arg81: !algebra.field<"bls12-381.fr">):
      %125 = "exec.compute"(%arg80) <{callee = @zkl_e38306e1154810613f8b855b4e24394048cbbd4c4b2723722235b0e03496f137, site = "s9"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%125)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%126: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %127 = "exec.complete"(%arg80, %126) : (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%127) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%128: !exec.stop):  // pred: ^bb0
      %129 = "exec.failed"(%128) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%129) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_27", sym_visibility = "private"}> ({
    ^bb0(%arg78: !runtime.scope, %arg79: !algebra.field<"bls12-381.fr">):
      %124 = "exec.complete"(%arg78, %arg79) : (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%124) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>, no_inline, sym_name = "zkl_d1c2bba308747260f914c193c146ad509308d619c2f75ba22eb051531fbbe7ca", sym_visibility = "private"}> ({
    ^bb0(%arg72: !runtime.scope, %arg73: !data.field_vector<"bls12-381.fr">, %arg74: !algebra.field<"bls12-381.fr">, %arg75: ui64, %arg76: ui64, %arg77: !data.field_vector<"bls12-381.fr">):
      %117 = "exec.fold"(%arg72, %arg77, %arg73, %arg74, %arg75, %arg76) <{domain = @finite_zkl_d1c2bba308747260f914c193c146ad509308d619c2f75ba22eb051531fbbe7ca_s0_domain, site = "s0", step = @finite_zkl_d1c2bba308747260f914c193c146ad509308d619c2f75ba22eb051531fbbe7ca_s0_body}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
      "exec.dispatch"(%117)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb1(%118: !data.field_vector<"bls12-381.fr">, %119: !algebra.field<"bls12-381.fr">, %120: ui64):  // pred: ^bb0
      %121 = "exec.returned"(%118, %119, %120) : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%121) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb2(%122: !exec.stop):  // pred: ^bb0
      %123 = "exec.failed"(%122) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%123) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_d1c2bba308747260f914c193c146ad509308d619c2f75ba22eb051531fbbe7ca_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg71: !data.field_vector<"bls12-381.fr">):
      %116 = "data.domain_elements"(%arg71) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%116) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>, no_inline, sym_name = "finite_zkl_d1c2bba308747260f914c193c146ad509308d619c2f75ba22eb051531fbbe7ca_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg64: !runtime.scope, %arg65: !data.field_vector<"bls12-381.fr">, %arg66: !algebra.field<"bls12-381.fr">, %arg67: ui64, %arg68: !algebra.field<"bls12-381.fr">, %arg69: !data.field_vector<"bls12-381.fr">, %arg70: ui64):
      %109 = "func.call"(%arg64, %arg65, %arg66, %arg67, %arg68, %arg70) <{callee = @zkl_abd6f98141af14ddf8b9152129fb3a9fb361b5735ade780e8d1c876d68deb283}> {runtime.site = "body"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
      "exec.dispatch"(%109)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb1(%110: !data.field_vector<"bls12-381.fr">, %111: !algebra.field<"bls12-381.fr">, %112: ui64):  // pred: ^bb0
      %113 = "exec.returned"(%110, %111, %112) : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%113) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb2(%114: !exec.stop):  // pred: ^bb0
      %115 = "exec.failed"(%114) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%115) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>) -> ()
    }) {runtime.origin = ["finite_zkl_d1c2bba308747260f914c193c146ad509308d619c2f75ba22eb051531fbbe7ca_s0_body", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_02aa9bd9900f843069baf97f23f4f5ccab54b136c8fed5b90842e4c46b7e5fcd", sym_visibility = "private"}> ({
    ^bb0(%arg62: !algebra.field<"bls12-381.fr">, %arg63: !algebra.field<"bls12-381.fr">):
      %108 = "algebra.field_add"(%arg62, %arg63) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%108) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_ca5df6081733f8afff4ae42147eb8eba3338d5a96600a7155f619346f19e4b47", sym_visibility = "private"}> ({
    ^bb0(%arg59: !runtime.scope, %arg60: !data.field_vector<"bls12-381.fr">, %arg61: ui64):
      %99 = "exec.apply"(%arg59) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%99)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%100: ui64):  // pred: ^bb0
      %101 = "exec.apply"(%arg59, %arg61, %100) <{binding = @zkl_binding_7, parameters = [], site = "s1"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%101)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%102: !exec.stop):  // 3 preds: ^bb0, ^bb1, ^bb3
      %103 = "exec.failed"(%102) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%103) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb3(%104: ui64):  // pred: ^bb1
      %105 = "func.call"(%arg59, %arg60, %104) <{callee = @zkl_6ba53ec68a0230031d706e4a93e78f80425c51108d34ecc0a5aa5681eded9c8e}> {runtime.site = "s2"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%105)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb4(%106: !algebra.field<"bls12-381.fr">):  // pred: ^bb3
      %107 = "exec.returned"(%106) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%107) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7213h656c656d656e745f6166746572", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_6ec6b9d6cb41b6bf4ef8e898ba1b283d099252f7de2db0b173f26714e3a46216", sym_visibility = "private"}> ({
    ^bb0(%arg57: !runtime.scope, %arg58: !data.field_vector<"bls12-381.fr">):
      %94 = "exec.apply"(%arg57, %arg58) <{binding = @zkl_binding_10, parameters = [], site = "s0"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%94)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%95: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %96 = "exec.returned"(%95) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%96) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%97: !exec.stop):  // pred: ^bb0
      %98 = "exec.failed"(%97) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%98) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6310h7072696d6974697665736h766563746f723h73756d", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_161d519d8d5fe2674feddb6e6d14269c9cca82ff216b6b3205ade46cc8b8d35f", sym_visibility = "private"}> ({
    ^bb0(%arg52: !runtime.scope, %arg53: !data.field_vector<"bls12-381.fr">, %arg54: !data.field_vector<"bls12-381.fr">, %arg55: !data.field_vector<"bls12-381.fr">, %arg56: !data.field_vector<"bls12-381.fr">):
      %59 = "exec.apply"(%arg52, %arg54) <{binding = @zkl_binding_2, parameters = [], site = "s0"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%59)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%60: ui64):  // pred: ^bb0
      %61 = "exec.apply"(%arg52, %arg55) <{binding = @zkl_binding_2, parameters = [], site = "s1"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%61)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%62: !exec.stop):  // 12 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb10, ^bb11, ^bb12
      %63 = "exec.failed"(%62) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%63) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb3(%64: ui64):  // pred: ^bb1
      %65 = "exec.apply"(%arg52, %60, %64) <{binding = @zkl_binding_7, parameters = [], site = "s2"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%65)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%66: ui64):  // pred: ^bb3
      %67 = "exec.apply"(%arg52, %arg56) <{binding = @zkl_binding_2, parameters = [], site = "s3"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%67)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%68: ui64):  // pred: ^bb4
      %69 = "exec.apply"(%arg52, %66, %68) <{binding = @zkl_binding_7, parameters = [], site = "s4"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%69)[^bb6, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb6(%70: ui64):  // pred: ^bb5
      %71 = "exec.apply"(%arg52) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s5"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%71)[^bb7, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb7(%72: ui64):  // pred: ^bb6
      %73 = "func.call"(%arg52, %arg53, %70, %72) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a}> {runtime.site = "s6"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%73)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb8(%74: !data.field_vector<"bls12-381.fr">, %75: ui64, %76: ui64):  // pred: ^bb7
      %77 = "func.call"(%arg52, %74, %75, %76, %arg54) <{callee = @zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be}> {runtime.site = "s8"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%77)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb9(%78: !data.field_vector<"bls12-381.fr">, %79: ui64, %80: ui64):  // pred: ^bb8
      %81 = "func.call"(%arg52, %78, %79, %80, %arg55) <{callee = @zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be}> {runtime.site = "s9"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%81)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb10(%82: !data.field_vector<"bls12-381.fr">, %83: ui64, %84: ui64):  // pred: ^bb9
      %85 = "func.call"(%arg52, %82, %83, %84, %arg56) <{callee = @zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be}> {runtime.site = "s10"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%85)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb11(%86: !data.field_vector<"bls12-381.fr">, %87: ui64, %88: ui64):  // pred: ^bb10
      %89 = "exec.compute"(%arg52, %86, %87, %88) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33, site = "s11"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%89)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb12(%90: !data.field_vector<"bls12-381.fr">):  // pred: ^bb11
      %91 = "exec.apply"(%arg52, %90) <{binding = @zkl_binding_10, parameters = [], site = "s12"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%91)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb13(%92: !algebra.field<"bls12-381.fr">):  // pred: ^bb12
      %93 = "exec.returned"(%92) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%93) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7215h6576616c756174655f776972696e67", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_1f2e31017a1a0403a56241b1d83eac39d1ecc40b298cd066516f78ae9c5b3434", sym_visibility = "private"}> ({
    ^bb0(%arg48: !runtime.scope, %arg49: !data.field_vector<"bls12-381.fr">, %arg50: !data.field_vector<"bls12-381.fr">, %arg51: !algebra.field<"bls12-381.fr">):
      %54 = "exec.collect"(%arg48, %arg49, %arg50, %arg51) <{body = @zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_body, domain = @zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_domain, site = "s0"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%54)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%55: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %56 = "exec.returned"(%55) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%56) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%57: !exec.stop):  // pred: ^bb0
      %58 = "exec.failed"(%57) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%58) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7210h6c696e655f706f696e74", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_21465134b1aa848c616c790eff1907b1a442ba76730b77da2be48acd923d6ff7", sym_visibility = "private"}> ({
    ^bb0(%arg45: !runtime.scope, %arg46: !data.field_vector<"bls12-381.fr">, %arg47: !algebra.field<"bls12-381.fr">):
      %45 = "exec.compute"(%arg45) <{callee = @zkl_acc5a50f3a300b126874f48e782cbb903e9f900ea776915474c16f8e7ecd49b5, site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%45)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%46: !algebra.field<"bls12-381.fr">, %47: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %48 = "func.call"(%arg45, %46, %47, %arg47, %arg46) <{callee = @zkl_ab1606681303f98565b6712556333e7dae847022aa12fe8b12138aeca5af88a1}> {runtime.site = "s2"} : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%48)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%49: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %50 = "exec.failed"(%49) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%50) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb3(%51: !algebra.field<"bls12-381.fr">, %52: !algebra.field<"bls12-381.fr">):  // pred: ^bb1
      %53 = "exec.returned"(%51) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%53) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7221h6576616c756174655f636f656666696369656e7473", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_bcbdb252ffc9abd0563757a6a45f0dccb9a7c345ecbfb58b787c5137455bd42e", sym_visibility = "private"}> ({
    ^bb0(%arg40: !runtime.scope, %arg41: !algebra.field<"bls12-381.fr">, %arg42: !algebra.field<"bls12-381.fr">, %arg43: !algebra.field<"bls12-381.fr">, %arg44: !algebra.field<"bls12-381.fr">):
      %39 = "exec.compute"(%arg40, %arg41, %arg42, %arg43, %arg44) <{callee = @zkl_82e44b33934fd674fa24fbb7f5705f2364f5020774fe25318dd2b968f9d001e4, site = "s4"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%39)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%40: !algebra.field<"bls12-381.fr">, %41: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %42 = "exec.returned"(%40, %41) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%42) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%43: !exec.stop):  // pred: ^bb0
      %44 = "exec.failed"(%43) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%44) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zks_c896eee882b0de19255b06dc85cce9b3173549e68e26b71cdd01e723c9c5b52d", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), sym_name = "zkl_82e44b33934fd674fa24fbb7f5705f2364f5020774fe25318dd2b968f9d001e4", sym_visibility = "private"}> ({
    ^bb0(%arg36: !algebra.field<"bls12-381.fr">, %arg37: !algebra.field<"bls12-381.fr">, %arg38: !algebra.field<"bls12-381.fr">, %arg39: !algebra.field<"bls12-381.fr">):
      %36 = "algebra.field_multiply"(%arg38, %arg37) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %37 = "algebra.field_add"(%arg36, %36) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %38 = "algebra.field_multiply"(%arg37, %arg39) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%37, %38) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = () -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), sym_name = "zkl_acc5a50f3a300b126874f48e782cbb903e9f900ea776915474c16f8e7ecd49b5", sym_visibility = "private"}> ({
      %34 = "algebra.constant"() <{value = #algebra.literal<<"bls12-381.fr">, 0 : ui255> : !algebra.field<"bls12-381.fr">}> : () -> !algebra.field<"bls12-381.fr">
      %35 = "algebra.constant"() <{value = #algebra.literal<<"bls12-381.fr">, 1 : ui255> : !algebra.field<"bls12-381.fr">}> : () -> !algebra.field<"bls12-381.fr">
      "func.return"(%34, %35) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_ab1606681303f98565b6712556333e7dae847022aa12fe8b12138aeca5af88a1", sym_visibility = "private"}> ({
    ^bb0(%arg31: !runtime.scope, %arg32: !algebra.field<"bls12-381.fr">, %arg33: !algebra.field<"bls12-381.fr">, %arg34: !algebra.field<"bls12-381.fr">, %arg35: !data.field_vector<"bls12-381.fr">):
      %28 = "exec.fold"(%arg31, %arg35, %arg32, %arg33, %arg34) <{domain = @finite_zkl_ab1606681303f98565b6712556333e7dae847022aa12fe8b12138aeca5af88a1_s0_domain, site = "s0", step = @finite_zkl_ab1606681303f98565b6712556333e7dae847022aa12fe8b12138aeca5af88a1_s0_body}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%28)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%29: !algebra.field<"bls12-381.fr">, %30: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %31 = "exec.returned"(%29, %30) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%31) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%32: !exec.stop):  // pred: ^bb0
      %33 = "exec.failed"(%32) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%33) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_ab1606681303f98565b6712556333e7dae847022aa12fe8b12138aeca5af88a1_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg30: !data.field_vector<"bls12-381.fr">):
      %27 = "data.domain_elements"(%arg30) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%27) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "finite_zkl_ab1606681303f98565b6712556333e7dae847022aa12fe8b12138aeca5af88a1_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg24: !runtime.scope, %arg25: !algebra.field<"bls12-381.fr">, %arg26: !algebra.field<"bls12-381.fr">, %arg27: !algebra.field<"bls12-381.fr">, %arg28: !data.field_vector<"bls12-381.fr">, %arg29: !algebra.field<"bls12-381.fr">):
      %21 = "func.call"(%arg24, %arg25, %arg26, %arg27, %arg29) <{callee = @zkl_bcbdb252ffc9abd0563757a6a45f0dccb9a7c345ecbfb58b787c5137455bd42e}> {runtime.site = "body"} : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%21)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%22: !algebra.field<"bls12-381.fr">, %23: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %24 = "exec.returned"(%22, %23) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%24) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%25: !exec.stop):  // pred: ^bb0
      %26 = "exec.failed"(%25) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%26) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["finite_zkl_ab1606681303f98565b6712556333e7dae847022aa12fe8b12138aeca5af88a1_s0_body", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_744f32fd2e4e542d6467fe3f764e183881171708947eb2bd852cea6f32a0407e", sym_visibility = "private"}> ({
    ^bb0(%arg18: !runtime.scope, %arg19: !runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, %arg20: !data.field_vector<"bls12-381.fr">, %arg21: !algebra.field<"bls12-381.fr">, %arg22: !data.field_vector<"bls12-381.fr">, %arg23: !algebra.field<"bls12-381.fr">):
      %16 = "exec.apply"(%arg18, %arg19) <{binding = @zkl_binding_16, parameters = [], site = "s1_repack_0"}> : (!runtime.scope, !runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">)>
      "exec.dispatch"(%16)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">)>) -> ()
    ^bb1(%17: !runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">):  // pred: ^bb0
      %18 = "exec.returned"(%17, %arg22, %arg23) : (!runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%18) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%19: !exec.stop):  // pred: ^bb0
      %20 = "exec.failed"(%19) : (!exec.stop) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%20) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7213h616476616e63655f6c61796572", []]} : () -> ()
    "protocol.func"() <{contracts = [["target", "input_value", [@zkl_cb10975ebbde52f87ba3f031d71fbab61676c0ccc3b05423f90b82c03f36e3ff, [["input", 0, "role00000000"], ["input", 2, "role00000000"], ["input", 3, "role00000000"]]], unit, ["output", 0, "role00000000"]]], function_type = (!data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, input_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"]], origin = ["gkr::Input", [["F", ["field", "bls12-381.fr"]]]], output_roles = [["role00000000"]], roles = ["role00000000"], sym_name = "zkl_9719be65739d901a935dbaa0f3f8323a785562f7eee1e60cc8c8c9676f8fdb55"}> ({
    ^bb0(%arg14: !data.field_vector<"bls12-381.fr">, %arg15: !runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, %arg16: !data.field_vector<"bls12-381.fr">, %arg17: !algebra.field<"bls12-381.fr">):
      %15 = "protocol.local_call"(%arg14, %arg15, %arg16, %arg17) <{callee = @zkl_d74cb9bd9ed782590145b66a573f8104fca0e842c109c7d034296431308fc6b9, role = "role00000000", site = "s0"}> : (!data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "protocol.return"(%15) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "zkf_d1b83b15191b85497fc6003ecffb377b2ff71a9228a1114a266874f0ba672708", sym_visibility = "private"}> ({
    ^bb0(%arg11: !data.field_vector<"bls12-381.fr">, %arg12: !data.field_vector<"bls12-381.fr">, %arg13: !algebra.field<"bls12-381.fr">):
      %11 = "algebra.multilinear_restrict_prefix"(%arg11, %arg12) : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !data.field_vector<"bls12-381.fr">
      %12 = "algebra.constant"() <{value = #algebra.literal<<"bls12-381.fr">, 0 : ui255> : !algebra.field<"bls12-381.fr">}> : () -> !algebra.field<"bls12-381.fr">
      %13 = "data.finite_fold"(%11, %12) <{domain = @finite_zkl_cb10975ebbde52f87ba3f031d71fbab61676c0ccc3b05423f90b82c03f36e3ff_s2_domain, step = @finite_zkl_cb10975ebbde52f87ba3f031d71fbab61676c0ccc3b05423f90b82c03f36e3ff_s2_body}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %14 = "algebra.field_equal"(%arg13, %13) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "func.return"(%14) : (i1) -> ()
    }) : () -> ()
    "data.domain"() <{function_type = (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_cb10975ebbde52f87ba3f031d71fbab61676c0ccc3b05423f90b82c03f36e3ff_s2_domain", sym_visibility = "private"}> ({
    ^bb0(%arg10: !data.field_vector<"bls12-381.fr">):
      %10 = "data.domain_elements"(%arg10) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%10) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "finite_zkl_cb10975ebbde52f87ba3f031d71fbab61676c0ccc3b05423f90b82c03f36e3ff_s2_body", sym_visibility = "private"}> ({
    ^bb0(%arg7: !algebra.field<"bls12-381.fr">, %arg8: !algebra.field<"bls12-381.fr">, %arg9: !data.field_vector<"bls12-381.fr">):
      %9 = "func.call"(%arg7, %arg8) <{callee = @zkl_293773d0130047867a66c9eaf450957dc940a0b0b9ee8988021422577cf8335f}> : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%9) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_293773d0130047867a66c9eaf450957dc940a0b0b9ee8988021422577cf8335f", sym_visibility = "private"}> ({
    ^bb0(%arg5: !algebra.field<"bls12-381.fr">, %arg6: !algebra.field<"bls12-381.fr">):
      %8 = "algebra.field_add"(%arg5, %arg6) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%8) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_d74cb9bd9ed782590145b66a573f8104fca0e842c109c7d034296431308fc6b9", sym_visibility = "private"}> ({
    ^bb0(%arg0: !runtime.scope, %arg1: !data.field_vector<"bls12-381.fr">, %arg2: !runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">, %arg3: !data.field_vector<"bls12-381.fr">, %arg4: !algebra.field<"bls12-381.fr">):
      %0 = "exec.apply"(%arg0, %arg2) <{binding = @zkl_binding_17, parameters = [], site = "s0_unpack_0"}> : (!runtime.scope, !runtime.capability<resource_unit, "zkl_resource_3e5b7b20b823dd23a44ff31f00bc1157fe46b6c75eff2e990729abf5b47767eb">) -> !exec.outcome<>
      "exec.dispatch"(%0)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb1:  // pred: ^bb0
      %1 = "func.call"(%arg0, %arg1, %arg3) <{callee = @zkl_28c1498dbf9d83fc38ed7b21a89d56146297abcbf1ac78968a8b454c9eef5496}> {runtime.site = "s3"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%1)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%2: !exec.stop):  // 3 preds: ^bb0, ^bb1, ^bb3
      %3 = "exec.failed"(%2) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%3) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%4: !algebra.field<"bls12-381.fr">):  // pred: ^bb1
      %5 = "exec.apply"(%arg0, %4, %arg4) <{binding = @zkl_binding_18, parameters = [], site = "s5"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>
      "exec.dispatch"(%5)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb4(%6: i1):  // pred: ^bb3
      %7 = "exec.returned"(%6) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%7) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.origin = ["s3h676b7211h636865636b5f696e707574", []]} : () -> ()
    "relation.declare"() <{key = "shape", kind = "gkr.circuit/0", purposes = ["parameter", "parameter", "parameter", "parameter", "parameter", "parameter", "parameter"], revision = "0", signature = (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, ui64, ui64) -> i1, static_arguments = [["field", "bls12-381.fr"], ["nat", "4"], ["nat", "4"]], sym_name = "zkl_cb1c10731e59161b14394fbb472272285b0bbba78877994f53fa6955497a3df4"}> : () -> ()
    "relation.declare"() <{key = "outputs", kind = "gkr.circuit/0", purposes = ["parameter", "parameter", "parameter", "parameter", "parameter", "parameter", "statement"], revision = "0", signature = (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, ui64, ui64, !data.field_vector<"bls12-381.fr">) -> i1, static_arguments = [["field", "bls12-381.fr"]], sym_name = "zkl_5effead4fa609f078c405b9340f603e2dc77b3e9155c76d7032b9f0b55bf1801"}> : () -> ()
    "relation.declare"() <{formula = @zkf_029bdd6bcc5b1485783f1674f8c6e15543fd2d268649f211eab729158162c828, key = "zkl_30326558223483c2b755cae1fef2fb9e26e5ee8894b87d6977fe6482997b20fd", kind = "zkc.language.formula/0", purposes = ["parameter", "parameter", "parameter", "parameter"], revision = "f0a4f3382f9934391a4be93557e85429dd1e9395560c2767c3358aa1fb461bad", signature = (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> i1, static_arguments = [], sym_name = "zkl_30326558223483c2b755cae1fef2fb9e26e5ee8894b87d6977fe6482997b20fd"}> : () -> ()
    "relation.declare"() <{key = "residual", kind = "gkr.rounds/0", purposes = ["parameter", "parameter", "parameter", "parameter", "statement", "statement"], revision = "0", signature = (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, static_arguments = [["field", "bls12-381.fr"]], sym_name = "zkl_e276fa0fd61d1145b2034d7e5681d41484daeb4a120f83771eba638587b04670"}> : () -> ()
    "relation.declare"() <{formula = @zkf_d1b83b15191b85497fc6003ecffb377b2ff71a9228a1114a266874f0ba672708, key = "zkl_cb10975ebbde52f87ba3f031d71fbab61676c0ccc3b05423f90b82c03f36e3ff", kind = "zkc.language.formula/0", purposes = ["parameter", "statement", "statement"], revision = "728df64dc19da9e2da6621a36cc4b84667459e235b2a4ce316858c1049abe46a", signature = (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, static_arguments = [], sym_name = "zkl_cb10975ebbde52f87ba3f031d71fbab61676c0ccc3b05423f90b82c03f36e3ff"}> : () -> ()
  }) : () -> ()
}) : () -> ()

