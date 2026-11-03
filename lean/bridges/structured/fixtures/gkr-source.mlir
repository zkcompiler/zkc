"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>, source_declarations = [[[["nominal", "record", "gkr::LayerClaim", [["field", "bls12-381.fr"]]], "linear", false, [["point", ["builtin", "vector", [["field", "bls12-381.fr"]]], unit], ["value", ["field", "bls12-381.fr"], unit]], [], "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea"], [["nominal", "record", "gkr::Gates", [["field", "bls12-381.fr"]]], "ordinary", false, [["add", ["builtin", "vector", [["field", "bls12-381.fr"]]], unit], ["mul", ["builtin", "vector", [["field", "bls12-381.fr"]]], unit], ["left", ["builtin", "vector", [["field", "bls12-381.fr"]]], unit], ["right", ["builtin", "vector", [["field", "bls12-381.fr"]]], unit]], [], unit], [["nominal", "record", "gkr::Pending", [["field", "bls12-381.fr"]]], "linear", false, [["point", ["builtin", "vector", [["field", "bls12-381.fr"]]], unit], ["value", ["field", "bls12-381.fr"], unit]], [], "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134"], [["nominal", "record", "zkc::multilinear::Table", [["field", "bls12-381.fr"]]], "ordinary", false, [["entries", ["builtin", "vector", [["field", "bls12-381.fr"]]], unit], ["dimensions", ["index"], unit], ["columns", ["index"], unit]], [], unit]], [["zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [["inputs", ["builtin", "vector", [["field", "bls12-381.fr"]]], ["role00000000", "role00000001"], 0 : ui64, 1 : ui64, ["data", ["role00000000", "role00000001"]]], ["outputs", ["builtin", "vector", [["field", "bls12-381.fr"]]], ["role00000001"], 1 : ui64, 1 : ui64, ["data", ["role00000001"]]], ["add", ["builtin", "vector", [["field", "bls12-381.fr"]]], ["role00000000", "role00000001"], 2 : ui64, 1 : ui64, ["data", ["role00000000", "role00000001"]]], ["mul", ["builtin", "vector", [["field", "bls12-381.fr"]]], ["role00000000", "role00000001"], 3 : ui64, 1 : ui64, ["data", ["role00000000", "role00000001"]]], ["layers", ["index"], ["role00000000", "role00000001"], 4 : ui64, 1 : ui64, ["data", ["role00000000", "role00000001"]]], ["selector", ["index"], ["role00000000", "role00000001"], 5 : ui64, 1 : ui64, ["data", ["role00000000", "role00000001"]]], ["width", ["index"], ["role00000000", "role00000001"], 6 : ui64, 1 : ui64, ["data", ["role00000000", "role00000001"]]]], [["accepted", ["bool"], ["role00000001"], 0 : ui64, 1 : ui64, ["data", ["role00000001"]]]]], ["zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", [["gates", ["nominal", "record", "gkr::Gates", [["field", "bls12-381.fr"]]], ["role00000000"], 0 : ui64, 4 : ui64, ["data", ["role00000000"]]], ["claim", ["nominal", "record", "gkr::Pending", [["field", "bls12-381.fr"]]], ["role00000001"], 4 : ui64, 3 : ui64, ["data", ["role00000001"]]], ["rounds", ["index"], ["role00000000", "role00000001"], 7 : ui64, 1 : ui64, ["data", ["role00000000", "role00000001"]]]], [["point", ["builtin", "vector", [["field", "bls12-381.fr"]]], ["role00000000"], 0 : ui64, 1 : ui64, ["data", ["role00000000"]]], ["residual", ["nominal", "record", "gkr::Gates", [["field", "bls12-381.fr"]]], ["role00000000"], 1 : ui64, 4 : ui64, ["data", ["role00000000"]]], ["evaluation", ["nominal", "record", "gkr::Pending", [["field", "bls12-381.fr"]]], ["role00000001"], 5 : ui64, 3 : ui64, ["data", ["role00000001"]]]]], ["zkl_9719be65739d901a935dbaa0f3f8323a785562f7eee1e60cc8c8c9676f8fdb55", [["values", ["builtin", "vector", [["field", "bls12-381.fr"]]], ["role00000000"], 0 : ui64, 1 : ui64, ["data", ["role00000000"]]], ["claim", ["nominal", "record", "gkr::LayerClaim", [["field", "bls12-381.fr"]]], ["role00000000"], 1 : ui64, 3 : ui64, ["data", ["role00000000"]]]], [["accepted", ["bool"], ["role00000000"], 0 : ui64, 1 : ui64, ["data", ["role00000000"]]]]]], [["gkr::Gates", "54b87fd6ff23cb1eafe060c001a96dd78b1797c190a509bdc713c274be042d9b"], ["gkr::LayerClaim", "54b87fd6ff23cb1eafe060c001a96dd78b1797c190a509bdc713c274be042d9b"], ["gkr::Pending", "54b87fd6ff23cb1eafe060c001a96dd78b1797c190a509bdc713c274be042d9b"], ["zkc::multilinear::Table", "a568766f66b8088201c0c521621df6d49be54fd6e8c10ae1ceb6af4698899482"]]]}> ({
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "field.equal", function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>, implementation = "", sym_name = "zkl_binding_18"}> : () -> ()
    "runtime.binding"() <{arguments = ["zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea"], contract = "resource_unit.consume", function_type = (!runtime.scope, !runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">) -> !exec.outcome<>, implementation = "", sym_name = "zkl_binding_17"}> : () -> ()
    "runtime.binding"() <{arguments = ["zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea"], contract = "resource_unit.pass", function_type = (!runtime.scope, !runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">)>, implementation = "", sym_name = "zkl_binding_16"}> : () -> ()
    "runtime.binding"() <{arguments = ["zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134"], contract = "resource_unit.consume", function_type = (!runtime.scope, !runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">) -> !exec.outcome<>, implementation = "", sym_name = "zkl_binding_15"}> : () -> ()
    "runtime.binding"() <{arguments = ["zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134"], contract = "resource_unit.create", function_type = (!runtime.scope) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">)>, implementation = "", sym_name = "zkl_binding_14"}> : () -> ()
    "runtime.binding"() <{arguments = ["zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea"], contract = "resource_unit.create", function_type = (!runtime.scope) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">)>, implementation = "", sym_name = "zkl_binding_13"}> : () -> ()
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
    ^bb0(%arg486: !data.field_vector<"bls12-381.fr">, %arg487: !data.field_vector<"bls12-381.fr">, %arg488: !data.field_vector<"bls12-381.fr">, %arg489: !data.field_vector<"bls12-381.fr">, %arg490: ui64, %arg491: ui64, %arg492: ui64, %arg493: !protocol.service_ref<"random.bls12-381.fr/0">):
      %1180 = "data.index"() <{value = 4 : ui64}> : () -> ui64
      %1181 = "protocol.local_call"(%1180, %arg492) <{callee = @s3h7a6b637h696e64696365734h6c657373, role = "role00000001", site = "s1"}> : (ui64, ui64) -> i1
      %1182 = "arith.constant"() <{value = false}> : () -> i1
      %1183 = "arith.cmpi"(%1181, %1182) <{predicate = 0 : i64}> : (i1, i1) -> i1
      "protocol.guard"(%1183) <{owner = "role00000001", site = "s4"}> : (i1) -> ()
      %1184 = "data.index"() <{value = 4 : ui64}> : () -> ui64
      %1185 = "protocol.local_call"(%1184, %arg490) <{callee = @s3h7a6b637h696e64696365734h6c657373, role = "role00000001", site = "s6"}> : (ui64, ui64) -> i1
      %1186 = "arith.constant"() <{value = false}> : () -> i1
      %1187 = "arith.cmpi"(%1185, %1186) <{predicate = 0 : i64}> : (i1, i1) -> i1
      "protocol.guard"(%1187) <{owner = "role00000001", site = "s9"}> : (i1) -> ()
      %1188 = "data.index"() <{value = 1 : ui64}> : () -> ui64
      %1189 = "protocol.local_call"(%arg486, %arg492, %1188) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655, role = "role00000001", site = "s11"}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> i1
      "protocol.guard"(%1189) <{owner = "role00000001", site = "s12"}> : (i1) -> ()
      %1190 = "data.index"() <{value = 1 : ui64}> : () -> ui64
      %1191 = "protocol.local_call"(%arg487, %arg492, %1190) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655, role = "role00000001", site = "s14"}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> i1
      "protocol.guard"(%1191) <{owner = "role00000001", site = "s15"}> : (i1) -> ()
      %1192 = "protocol.local_call"(%arg491, %arg492) <{callee = @s3h7a6b637h7072656c7564659h696e6465785f616464, role = "role00000001", site = "s16"}> : (ui64, ui64) -> ui64
      %1193 = "protocol.local_call"(%1192, %arg492) <{callee = @s3h7a6b637h7072656c7564659h696e6465785f616464, role = "role00000001", site = "s17"}> : (ui64, ui64) -> ui64
      %1194 = "protocol.local_call"(%1193, %arg492) <{callee = @s3h7a6b637h7072656c7564659h696e6465785f616464, role = "role00000001", site = "s18"}> : (ui64, ui64) -> ui64
      %1195 = "data.index"() <{value = 1 : ui64}> : () -> ui64
      %1196 = "protocol.local_call"(%arg488, %1194, %1195) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655, role = "role00000001", site = "s20"}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> i1
      "protocol.guard"(%1196) <{owner = "role00000001", site = "s21"}> : (i1) -> ()
      %1197 = "protocol.local_call"(%arg491, %arg492) <{callee = @s3h7a6b637h7072656c7564659h696e6465785f616464, role = "role00000001", site = "s22"}> : (ui64, ui64) -> ui64
      %1198 = "protocol.local_call"(%1197, %arg492) <{callee = @s3h7a6b637h7072656c7564659h696e6465785f616464, role = "role00000001", site = "s23"}> : (ui64, ui64) -> ui64
      %1199 = "protocol.local_call"(%1198, %arg492) <{callee = @s3h7a6b637h7072656c7564659h696e6465785f616464, role = "role00000001", site = "s24"}> : (ui64, ui64) -> ui64
      %1200 = "data.index"() <{value = 1 : ui64}> : () -> ui64
      %1201 = "protocol.local_call"(%arg489, %1199, %1200) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655, role = "role00000001", site = "s26"}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> i1
      "protocol.guard"(%1201) <{owner = "role00000001", site = "s27"}> : (i1) -> ()
      %1202 = "protocol.local_call"(%arg491) <{callee = @s3h676b7212h706f7765725f6f665f74776f, role = "role00000001", site = "s28"}> : (ui64) -> ui64
      %1203 = "protocol.local_call"(%1202, %arg490) <{callee = @s3h7a6b637h696e64696365734h6c657373, role = "role00000001", site = "s29"}> : (ui64, ui64) -> i1
      %1204 = "arith.constant"() <{value = false}> : () -> i1
      %1205 = "arith.cmpi"(%1203, %1204) <{predicate = 0 : i64}> : (i1, i1) -> i1
      "protocol.guard"(%1205) <{owner = "role00000001", site = "s32"}> : (i1) -> ()
      %1206 = "protocol.local_call"() <{callee = @zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f, role = "role00000001", site = "s33"}> : () -> !data.field_vector<"bls12-381.fr">
      %1207 = "protocol.local_call"() <{callee = @zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f, role = "role00000000", site = "s35"}> : () -> !data.field_vector<"bls12-381.fr">
      %1208:2 = "protocol.repeat"(%arg492, %1206, %1207, %arg493) <{carried = 2 : i64, carried_roles = [["role00000001"], ["role00000000"]], maximum = 4 : i64, roles = ["role00000000", "role00000001"], site = "s37"}> ({
      ^bb0(%arg509: ui64, %arg510: !data.field_vector<"bls12-381.fr">, %arg511: !data.field_vector<"bls12-381.fr">, %arg512: !protocol.service_ref<"random.bls12-381.fr/0">):
        %1253 = "protocol.query"(%arg512) <{method = "draw", owner = "role00000001", site = "label_6f7574707574"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
        %1254 = "protocol.exchange"(%1253) <{receiver = "role00000000", sender = "role00000001", site = "label_6f75747075745f64656c6976657279_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1255 = "protocol.restrict_roles"(%1254) <{roles = ["role00000000"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1256 = "protocol.local_call"(%arg510, %1253) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000001", site = "s42"}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !data.field_vector<"bls12-381.fr">
        %1257 = "protocol.local_call"(%arg511, %1255) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000000", site = "s44"}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !data.field_vector<"bls12-381.fr">
        "protocol.yield"(%1256, %1257) : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> ()
      }) : (ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)
      %1209 = "protocol.local_call"(%arg487, %1208#0) <{callee = @zkl_28c1498dbf9d83fc38ed7b21a89d56146297abcbf1ac78968a8b454c9eef5496, role = "role00000001", site = "s48"}> : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %1210:3 = "protocol.local_call"(%1208#0, %1209) <{callee = @zkl_7b9dfa97fa3e158d428459ec12d8a2d5aa171a060ab79f314eeccc53ee772b17, role = "role00000001", site = "s49"}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %1211:4 = "protocol.repeat"(%arg490, %1208#1, %1210#0, %1210#1, %1210#2, %arg486, %arg488, %arg489, %arg490, %arg491, %arg492, %arg493) <{carried = 4 : i64, carried_roles = [["role00000000"], ["role00000001"], ["role00000001"], ["role00000001"]], maximum = 4 : i64, roles = ["role00000000", "role00000001"], site = "s57"}> ({
      ^bb0(%arg494: ui64, %arg495: !data.field_vector<"bls12-381.fr">, %arg496: !runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, %arg497: !data.field_vector<"bls12-381.fr">, %arg498: !algebra.field<"bls12-381.fr">, %arg499: !data.field_vector<"bls12-381.fr">, %arg500: !data.field_vector<"bls12-381.fr">, %arg501: !data.field_vector<"bls12-381.fr">, %arg502: ui64, %arg503: ui64, %arg504: ui64, %arg505: !protocol.service_ref<"random.bls12-381.fr/0">):
        %1213:5 = "protocol.local_call"(%arg496, %arg497, %arg498) <{callee = @zkl_e0f7a4e58ae24eb13e9b2033c42c179b2766ff6cdb4ae1470bf7ef9b1721d646, role = "role00000001", site = "s58"}> : (!runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %1214 = "protocol.local_call"(%arg500, %arg501, %arg499, %arg502, %arg503, %arg504, %arg494) <{callee = @zkl_8c63ad97d926a7762c597860addde408bcd2077ea9cda1b99df123dc13e64af6, role = "role00000000", site = "s62"}> : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, ui64, ui64, ui64) -> !data.field_vector<"bls12-381.fr">
        %1215 = "protocol.local_call"(%arg500, %arg494, %arg503) <{callee = @zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e, role = "role00000000", site = "s64"}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !data.field_vector<"bls12-381.fr">
        %1216 = "protocol.local_call"(%arg501, %arg494, %arg503) <{callee = @zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e, role = "role00000000", site = "s65"}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !data.field_vector<"bls12-381.fr">
        %1217:4 = "protocol.local_call"(%1215, %1216, %arg495, %1214, %arg504) <{callee = @zkl_d1f2756b99b17aad26e4b85a966eec4c9419609618b22e3ee7f8a3349cb1e33b, role = "role00000000", site = "s66"}> : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64) -> (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)
        %1218:3 = "protocol.local_call"(%1213#4) <{callee = @zkl_e1405e1bb4604e60f337203132c746492bf7c31b55302426ae19c2c021c2da1a, role = "role00000001", site = "s69"}> : (!algebra.field<"bls12-381.fr">) -> (!runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %1219:8 = "protocol.apply"(%1217#0, %1217#1, %1217#2, %1217#3, %1218#0, %1218#1, %1218#2, %arg504, %arg505) <{callee = @zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba, roles = ["role00000000", "role00000001"], site = "label_6c656674"}> : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %1220:8 = "protocol.apply"(%1219#1, %1219#2, %1219#3, %1219#4, %1219#5, %1219#6, %1219#7, %arg504, %arg505) <{callee = @zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba, roles = ["role00000000", "role00000001"], site = "label_7269676874"}> : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %1221:2 = "protocol.local_call"(%1220#5, %1220#6, %1220#7) <{callee = @zkl_bd4f0d76e787de675c5732a4a96fc396d45486f32b3dcda5182ccc324969c825, role = "role00000001", site = "s78"}> : (!runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %1222:2 = "protocol.local_call"(%1221#0) <{callee = @zkl_cfcf40daaab145a916368cf7a01eccd9ba0e536fbbc30a06c4a25e7ec96ecbe7, role = "role00000001", site = "s81"}> : (!data.field_vector<"bls12-381.fr">) -> (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)
        %1223 = "protocol.local_call"(%1214, %1219#0, %1220#0, %arg504) <{callee = @zkl_91fe8ea73b5db3432f90fc8fe9725c8455fce8782b4cc4d2839d05826de71b8f, role = "role00000000", site = "s83"}> : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64) -> !data.field_vector<"bls12-381.fr">
        %1224 = "data.index"() <{value = 0 : ui64}> : () -> ui64
        %1225 = "protocol.local_call"(%1223, %1224) <{callee = @zkl_6ba53ec68a0230031d706e4a93e78f80425c51108d34ecc0a5aa5681eded9c8e, role = "role00000000", site = "s86"}> : (!data.field_vector<"bls12-381.fr">, ui64) -> !algebra.field<"bls12-381.fr">
        %1226 = "protocol.exchange"(%1225) <{receiver = "role00000001", sender = "role00000000", site = "label_6c696e655f636f6e7374616e74_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1227 = "protocol.restrict_roles"(%1226) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1228 = "protocol.local_call"() <{callee = @zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f, role = "role00000001", site = "s89"}> : () -> !data.field_vector<"bls12-381.fr">
        %1229 = "protocol.local_call"(%1228, %1227) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000001", site = "s90"}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !data.field_vector<"bls12-381.fr">
        %1230 = "protocol.repeat"(%arg504, %1229, %1223) <{carried = 1 : i64, carried_roles = [["role00000001"]], maximum = 4 : i64, roles = ["role00000000", "role00000001"], site = "s93"}> ({
        ^bb0(%arg506: ui64, %arg507: !data.field_vector<"bls12-381.fr">, %arg508: !data.field_vector<"bls12-381.fr">):
          %1249 = "protocol.local_call"(%arg508, %arg506) <{callee = @zkl_ca5df6081733f8afff4ae42147eb8eba3338d5a96600a7155f619346f19e4b47, role = "role00000000", site = "s94"}> : (!data.field_vector<"bls12-381.fr">, ui64) -> !algebra.field<"bls12-381.fr">
          %1250 = "protocol.exchange"(%1249) <{receiver = "role00000001", sender = "role00000000", site = "label_6c696e655f636f656666696369656e74_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
          %1251 = "protocol.restrict_roles"(%1250) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
          %1252 = "protocol.local_call"(%arg507, %1251) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000001", site = "s97"}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !data.field_vector<"bls12-381.fr">
          "protocol.yield"(%1252) : (!data.field_vector<"bls12-381.fr">) -> ()
        }) : (ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !data.field_vector<"bls12-381.fr">
        %1231 = "protocol.local_call"(%1230) <{callee = @zkl_6ec6b9d6cb41b6bf4ef8e898ba1b283d099252f7de2db0b173f26714e3a46216, role = "role00000001", site = "s101"}> : (!data.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1232 = "protocol.local_call"(%arg500, %arg494, %arg503) <{callee = @zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e, role = "role00000001", site = "s103"}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !data.field_vector<"bls12-381.fr">
        %1233 = "protocol.local_call"(%1232, %1213#3, %1222#0, %1222#1) <{callee = @zkl_161d519d8d5fe2674feddb6e6d14269c9cca82ff216b6b3205ade46cc8b8d35f, role = "role00000001", site = "s107"}> : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1234 = "protocol.local_call"(%arg501, %arg494, %arg503) <{callee = @zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e, role = "role00000001", site = "s109"}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !data.field_vector<"bls12-381.fr">
        %1235 = "protocol.local_call"(%1234, %1213#3, %1222#0, %1222#1) <{callee = @zkl_161d519d8d5fe2674feddb6e6d14269c9cca82ff216b6b3205ade46cc8b8d35f, role = "role00000001", site = "s113"}> : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1236 = "algebra.field_add"(%1227, %1231) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1237 = "algebra.field_multiply"(%1233, %1236) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1238 = "algebra.field_multiply"(%1235, %1227) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1239 = "algebra.field_multiply"(%1238, %1231) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1240 = "algebra.field_add"(%1237, %1239) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1241 = "algebra.field_equal"(%1221#1, %1240) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
        "protocol.guard"(%1241) <{owner = "role00000001", site = "s122"}> : (i1) -> ()
        %1242 = "protocol.query"(%arg505) <{method = "draw", owner = "role00000001", site = "label_6c696e655f6368616c6c656e6765"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
        %1243 = "protocol.exchange"(%1242) <{receiver = "role00000000", sender = "role00000001", site = "label_6c696e655f64656c6976657279_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1244 = "protocol.restrict_roles"(%1243) <{roles = ["role00000000"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1245 = "protocol.local_call"(%1222#0, %1222#1, %1242) <{callee = @zkl_1f2e31017a1a0403a56241b1d83eac39d1ecc40b298cd066516f78ae9c5b3434, role = "role00000001", site = "s130"}> : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !data.field_vector<"bls12-381.fr">
        %1246 = "protocol.local_call"(%1230, %1242) <{callee = @zkl_21465134b1aa848c616c790eff1907b1a442ba76730b77da2be48acd923d6ff7, role = "role00000001", site = "s131"}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %1247:3 = "protocol.local_call"(%1213#0, %1213#1, %1213#2, %1245, %1246) <{callee = @zkl_744f32fd2e4e542d6467fe3f764e183881171708947eb2bd852cea6f32a0407e, role = "role00000001", site = "s132"}> : (!runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %1248 = "protocol.local_call"(%1219#0, %1220#0, %1244) <{callee = @zkl_1f2e31017a1a0403a56241b1d83eac39d1ecc40b298cd066516f78ae9c5b3434, role = "role00000000", site = "s134"}> : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !data.field_vector<"bls12-381.fr">
        "protocol.yield"(%1248, %1247#0, %1247#1, %1247#2) : (!data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
      }) : (ui64, !data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, ui64, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %1212 = "protocol.apply"(%arg486, %1211#1, %1211#2, %1211#3) <{callee = @zkl_9719be65739d901a935dbaa0f3f8323a785562f7eee1e60cc8c8c9676f8fdb55, roles = ["role00000001"], site = "label_696e707574"}> : (!data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "protocol.return"(%1212) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "s3h7a6b637h696e64696365734h6c657373", sym_visibility = "private"}> ({
    ^bb0(%arg483: !runtime.scope, %arg484: ui64, %arg485: ui64):
      %1175 = "exec.apply"(%arg483, %arg484, %arg485) <{binding = @zkl_binding_0, parameters = [], site = "s0"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1175)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1176: i1):  // pred: ^bb0
      %1177 = "exec.returned"(%1176) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%1177) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%1178: !exec.stop):  // pred: ^bb0
      %1179 = "exec.failed"(%1178) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%1179) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.origin = ["s3h7a6b637h696e64696365734h6c657373", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", sym_visibility = "private"}> ({
    ^bb0(%arg479: !runtime.scope, %arg480: !data.field_vector<"bls12-381.fr">, %arg481: ui64, %arg482: ui64):
      %1117 = "exec.apply"(%arg479) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1117)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1118: ui64):  // pred: ^bb0
      %1119 = "func.call"(%arg479, %1118, %arg482) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s1"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1119)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%1120: !exec.stop):  // 23 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12, ^bb15, ^bb16, ^bb17, ^bb18, ^bb19, ^bb21, ^bb22, ^bb25, ^bb26, ^bb28, ^bb29, ^bb31, ^bb32
      %1121 = "exec.failed"(%1120) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%1121) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%1122: i1):  // pred: ^bb1
      %1123 = "exec.test"(%arg479, %1122) <{site = "s3"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1123)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb4(%1124: i1):  // pred: ^bb3
      "cf.cond_br"(%1124)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %1125 = "runtime.enter_scope"(%arg479, %arg481) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "then", site = "s3"}> : (!runtime.scope, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1125)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %1126 = "runtime.enter_scope"(%arg479, %arg481) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "else", site = "s3"}> : (!runtime.scope, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1126)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7(%1127: i1):  // 2 preds: ^bb10, ^bb13
      %1128 = "exec.test"(%arg479, %1127) <{site = "s11"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1128)[^bb14, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb8(%1129: !runtime.scope):  // pred: ^bb5
      %1130 = "func.call"(%1129, %arg481) <{callee = @zkl_control_0}> : (!runtime.scope, ui64) -> !exec.outcome<(i1)>
      %1131 = "runtime.exit_scope"(%1129, %1130) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%1131)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb9(%1132: !runtime.transfer<(i1)>):  // pred: ^bb8
      %1133 = "runtime.accept_transfer"(%arg479, %1132) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1133)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb10(%1134: i1):  // pred: ^bb9
      "cf.br"(%1134)[^bb7] : (i1) -> ()
    ^bb11(%1135: !runtime.scope):  // pred: ^bb6
      %1136 = "func.call"(%1135, %arg481) <{callee = @zkl_control_1}> : (!runtime.scope, ui64) -> !exec.outcome<(i1)>
      %1137 = "runtime.exit_scope"(%1135, %1136) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%1137)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb12(%1138: !runtime.transfer<(i1)>):  // pred: ^bb11
      %1139 = "runtime.accept_transfer"(%arg479, %1138) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1139)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb13(%1140: i1):  // pred: ^bb12
      "cf.br"(%1140)[^bb7] : (i1) -> ()
    ^bb14(%1141: i1):  // pred: ^bb7
      "cf.cond_br"(%1141)[^bb15, ^bb16] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb15:  // pred: ^bb14
      %1142 = "runtime.enter_scope"(%arg479, %arg480, %arg482) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "then", site = "s11"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1142)[^bb18, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb16:  // pred: ^bb14
      %1143 = "runtime.enter_scope"(%arg479, %arg480, %arg482) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "else", site = "s11"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1143)[^bb21, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb17(%1144: i1):  // 2 preds: ^bb20, ^bb23
      %1145 = "exec.test"(%arg479, %1144) <{site = "s22"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1145)[^bb24, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb18(%1146: !runtime.scope):  // pred: ^bb15
      %1147 = "func.call"(%1146, %arg480, %arg482) <{callee = @zkl_control_2}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>
      %1148 = "runtime.exit_scope"(%1146, %1147) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%1148)[^bb19, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb19(%1149: !runtime.transfer<(i1)>):  // pred: ^bb18
      %1150 = "runtime.accept_transfer"(%arg479, %1149) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1150)[^bb20, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb20(%1151: i1):  // pred: ^bb19
      "cf.br"(%1151)[^bb17] : (i1) -> ()
    ^bb21(%1152: !runtime.scope):  // pred: ^bb16
      %1153 = "func.call"(%1152, %arg480, %arg482) <{callee = @zkl_control_3}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>
      %1154 = "runtime.exit_scope"(%1152, %1153) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%1154)[^bb22, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb22(%1155: !runtime.transfer<(i1)>):  // pred: ^bb21
      %1156 = "runtime.accept_transfer"(%arg479, %1155) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1156)[^bb23, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb23(%1157: i1):  // pred: ^bb22
      "cf.br"(%1157)[^bb17] : (i1) -> ()
    ^bb24(%1158: i1):  // pred: ^bb17
      "cf.cond_br"(%1158)[^bb25, ^bb26] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb25:  // pred: ^bb24
      %1159 = "runtime.enter_scope"(%arg479, %arg480, %arg481, %arg482) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "then", site = "s22"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1159)[^bb28, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb26:  // pred: ^bb24
      %1160 = "runtime.enter_scope"(%arg479, %arg480, %arg481, %arg482) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "else", site = "s22"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1160)[^bb31, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb27(%1161: i1):  // 2 preds: ^bb30, ^bb33
      %1162 = "exec.returned"(%1161) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%1162) : (!exec.outcome<(i1)>) -> ()
    ^bb28(%1163: !runtime.scope):  // pred: ^bb25
      %1164 = "func.call"(%1163, %arg480, %arg481, %arg482) <{callee = @zkl_control_4}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      %1165 = "runtime.exit_scope"(%1163, %1164) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%1165)[^bb29, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb29(%1166: !runtime.transfer<(i1)>):  // pred: ^bb28
      %1167 = "runtime.accept_transfer"(%arg479, %1166) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1167)[^bb30, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb30(%1168: i1):  // pred: ^bb29
      "cf.br"(%1168)[^bb27] : (i1) -> ()
    ^bb31(%1169: !runtime.scope):  // pred: ^bb26
      %1170 = "func.call"(%1169, %arg480, %arg481, %arg482) <{callee = @zkl_control_5}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      %1171 = "runtime.exit_scope"(%1169, %1170) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%1171)[^bb32, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb32(%1172: !runtime.transfer<(i1)>):  // pred: ^bb31
      %1173 = "runtime.accept_transfer"(%arg479, %1172) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1173)[^bb33, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb33(%1174: i1):  // pred: ^bb32
      "cf.br"(%1174)[^bb27] : (i1) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_0", sym_visibility = "private"}> ({
    ^bb0(%arg477: !runtime.scope, %arg478: ui64):
      %1110 = "exec.apply"(%arg477) <{binding = @zkl_binding_1, parameters = [64 : ui64], site = "s4"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1110)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1111: ui64):  // pred: ^bb0
      %1112 = "func.call"(%arg477, %arg478, %1111) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s5"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1112)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%1113: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %1114 = "exec.failed"(%1113) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%1114) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%1115: i1):  // pred: ^bb1
      %1116 = "exec.complete"(%arg477, %1115) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%1116) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_1", sym_visibility = "private"}> ({
    ^bb0(%arg475: !runtime.scope, %arg476: ui64):
      %1105 = "exec.boolean"(%arg475) <{site = "s7", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1105)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1106: i1):  // pred: ^bb0
      %1107 = "exec.complete"(%arg475, %1106) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%1107) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%1108: !exec.stop):  // pred: ^bb0
      %1109 = "exec.failed"(%1108) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%1109) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_2", sym_visibility = "private"}> ({
    ^bb0(%arg472: !runtime.scope, %arg473: !data.field_vector<"bls12-381.fr">, %arg474: ui64):
      %1094 = "exec.apply"(%arg472, %arg473) <{binding = @zkl_binding_2, parameters = [], site = "s12"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1094)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1095: ui64):  // pred: ^bb0
      %1096 = "exec.apply"(%arg472, %1095, %arg474) <{binding = @zkl_binding_3, parameters = [], site = "s13"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1096)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%1097: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %1098 = "exec.failed"(%1097) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%1098) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%1099: ui64):  // pred: ^bb1
      %1100 = "exec.apply"(%arg472) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s14"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1100)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%1101: ui64):  // pred: ^bb3
      %1102 = "exec.apply"(%arg472, %1099, %1101) <{binding = @zkl_binding_4, parameters = [], site = "s15"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1102)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb5(%1103: i1):  // pred: ^bb4
      %1104 = "exec.complete"(%arg472, %1103) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%1104) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_3", sym_visibility = "private"}> ({
    ^bb0(%arg469: !runtime.scope, %arg470: !data.field_vector<"bls12-381.fr">, %arg471: ui64):
      %1089 = "exec.boolean"(%arg469) <{site = "s17", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1089)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1090: i1):  // pred: ^bb0
      %1091 = "exec.complete"(%arg469, %1090) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%1091) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%1092: !exec.stop):  // pred: ^bb0
      %1093 = "exec.failed"(%1092) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%1093) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_4", sym_visibility = "private"}> ({
    ^bb0(%arg465: !runtime.scope, %arg466: !data.field_vector<"bls12-381.fr">, %arg467: ui64, %arg468: ui64):
      %1078 = "exec.apply"(%arg465, %arg466) <{binding = @zkl_binding_2, parameters = [], site = "s23"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1078)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1079: ui64):  // pred: ^bb0
      %1080 = "exec.apply"(%arg465, %1079, %arg468) <{binding = @zkl_binding_5, parameters = [], site = "s24"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1080)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%1081: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %1082 = "exec.failed"(%1081) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%1082) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%1083: ui64):  // pred: ^bb1
      %1084 = "func.call"(%arg465, %arg467) <{callee = @s3h7a6b6311h6d756c74696c696e6561724h726f7773}> {runtime.site = "s25"} : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1084)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%1085: ui64):  // pred: ^bb3
      %1086 = "exec.apply"(%arg465, %1083, %1085) <{binding = @zkl_binding_4, parameters = [], site = "s26"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1086)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb5(%1087: i1):  // pred: ^bb4
      %1088 = "exec.complete"(%arg465, %1087) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%1088) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_5", sym_visibility = "private"}> ({
    ^bb0(%arg461: !runtime.scope, %arg462: !data.field_vector<"bls12-381.fr">, %arg463: ui64, %arg464: ui64):
      %1073 = "exec.boolean"(%arg461) <{site = "s28", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1073)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1074: i1):  // pred: ^bb0
      %1075 = "exec.complete"(%arg461, %1074) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%1075) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%1076: !exec.stop):  // pred: ^bb0
      %1077 = "exec.failed"(%1076) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%1077) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "s3h7a6b6311h6d756c74696c696e6561724h726f7773", sym_visibility = "private"}> ({
    ^bb0(%arg459: !runtime.scope, %arg460: ui64):
      %1026 = "exec.apply"(%arg459) <{binding = @zkl_binding_1, parameters = [64 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1026)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1027: ui64):  // pred: ^bb0
      %1028 = "func.call"(%arg459, %arg460, %1027) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s1"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1028)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%1029: !exec.stop):  // 14 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12, ^bb14, ^bb15, ^bb19, ^bb21
      %1030 = "exec.failed"(%1029) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%1030) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%1031: i1):  // pred: ^bb1
      %1032 = "exec.test"(%arg459, %1031) <{site = "s2"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%1032)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb4(%1033: i1):  // pred: ^bb3
      "cf.cond_br"(%1033)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %1034 = "runtime.enter_scope"(%arg459) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s2"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1034)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %1035 = "runtime.enter_scope"(%arg459) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s2"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1035)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // 2 preds: ^bb10, ^bb13
      %1036 = "exec.apply"(%arg459) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s3"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1036)[^bb14, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb8(%1037: !runtime.scope):  // pred: ^bb5
      %1038 = "func.call"(%1037) <{callee = @zkl_control_6}> : (!runtime.scope) -> !exec.outcome<>
      %1039 = "runtime.exit_scope"(%1037, %1038) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%1039)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb9(%1040: !runtime.transfer<>):  // pred: ^bb8
      %1041 = "runtime.accept_transfer"(%arg459, %1040) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%1041)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb10:  // pred: ^bb9
      "cf.br"()[^bb7] : () -> ()
    ^bb11(%1042: !runtime.scope):  // pred: ^bb6
      %1043 = "func.call"(%1042) <{callee = @zkl_control_7}> : (!runtime.scope) -> !exec.outcome<>
      %1044 = "runtime.exit_scope"(%1042, %1043) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%1044)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb12(%1045: !runtime.transfer<>):  // pred: ^bb11
      %1046 = "runtime.accept_transfer"(%arg459, %1045) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%1046)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb13:  // pred: ^bb12
      "cf.br"()[^bb7] : () -> ()
    ^bb14(%1047: ui64):  // pred: ^bb7
      %1048 = "exec.apply"(%arg459) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s5"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1048)[^bb15, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb15(%1049: ui64):  // pred: ^bb14
      %1050 = "exec.range"(%arg459, %1049, %arg460) <{site = "s6"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%1050)[^bb16, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i64, i64)>) -> ()
    ^bb16(%1051: i64, %1052: i64):  // pred: ^bb15
      %1053 = "runtime.borrow_transfer"(%arg459, %1047) : (!runtime.scope, ui64) -> !runtime.transfer<(ui64)>
      "cf.br"(%1051, %1053)[^bb17] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb17(%1054: i64, %1055: !runtime.transfer<(ui64)>):  // 2 preds: ^bb16, ^bb20
      %1056 = "arith.cmpi"(%1054, %1052) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%1056, %1055)[^bb18, ^bb19] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(ui64)>) -> ()
    ^bb18:  // pred: ^bb17
      %1057 = "runtime.iteration"(%arg459, %1054) <{site = "s6"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1057)[^bb22, ^bb21] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb19(%1058: !runtime.transfer<(ui64)>):  // pred: ^bb17
      %1059 = "runtime.accept_transfer"(%arg459, %1058) : (!runtime.scope, !runtime.transfer<(ui64)>) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1059)[^bb25, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb20(%1060: !runtime.transfer<(ui64)>):  // pred: ^bb24
      %1061 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %1062 = "arith.addi"(%1054, %1061) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%1062, %1060)[^bb17] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb21(%1063: !exec.stop):  // 3 preds: ^bb18, ^bb22, ^bb23
      "runtime.release_transfer"(%1055) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%1063)[^bb2] : (!exec.stop) -> ()
    ^bb22(%1064: ui64):  // pred: ^bb18
      %1065 = "runtime.transfer_values"(%1055) : (!runtime.transfer<(ui64)>) -> ui64
      %1066 = "runtime.enter_scope"(%arg459, %1054, %1064, %1065) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 2>, site = "s6"}> : (!runtime.scope, i64, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1066)[^bb23, ^bb21] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb23(%1067: !runtime.scope):  // pred: ^bb22
      %1068 = "func.call"(%1067, %1064, %1065) <{callee = @zkl_control_8}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      %1069 = "runtime.exit_scope"(%1067, %1068) : (!runtime.scope, !exec.outcome<(ui64)>) -> !exec.outcome<(!runtime.transfer<(ui64)>)>
      "exec.dispatch"(%1069)[^bb24, ^bb21] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(ui64)>)>) -> ()
    ^bb24(%1070: !runtime.transfer<(ui64)>):  // pred: ^bb23
      "runtime.release_transfer"(%1055) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%1070)[^bb20] : (!runtime.transfer<(ui64)>) -> ()
    ^bb25(%1071: ui64):  // pred: ^bb19
      %1072 = "exec.returned"(%1071) : (ui64) -> !exec.outcome<(ui64)>
      "func.return"(%1072) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561724h726f7773", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_6", sym_visibility = "private"}> ({
    ^bb0(%arg458: !runtime.scope):
      %1025 = "exec.complete"(%arg458) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%1025) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_7", sym_visibility = "private"}> ({
    ^bb0(%arg457: !runtime.scope):
      %1022 = "exec.reject"(%arg457) <{reason = "reject", site = "s2_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%1022)[^bb1] : (!exec.stop) -> ()
    ^bb1(%1023: !exec.stop):  // pred: ^bb0
      %1024 = "exec.failed"(%1023) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%1024) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "zkl_control_8", sym_visibility = "private"}> ({
    ^bb0(%arg454: !runtime.scope, %arg455: ui64, %arg456: ui64):
      %1015 = "exec.apply"(%arg454) <{binding = @zkl_binding_1, parameters = [2 : ui64], site = "s7"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1015)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1016: ui64):  // pred: ^bb0
      %1017 = "exec.apply"(%arg454, %arg456, %1016) <{binding = @zkl_binding_6, parameters = [], site = "s8"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1017)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%1018: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %1019 = "exec.failed"(%1018) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%1019) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%1020: ui64):  // pred: ^bb1
      %1021 = "exec.complete"(%arg454, %1020) : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "func.return"(%1021) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "s3h7a6b637h7072656c7564659h696e6465785f616464", sym_visibility = "private"}> ({
    ^bb0(%arg451: !runtime.scope, %arg452: ui64, %arg453: ui64):
      %1010 = "exec.apply"(%arg451, %arg452, %arg453) <{binding = @zkl_binding_7, parameters = [], site = "s0"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%1010)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1011: ui64):  // pred: ^bb0
      %1012 = "exec.returned"(%1011) : (ui64) -> !exec.outcome<(ui64)>
      "func.return"(%1012) : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%1013: !exec.stop):  // pred: ^bb0
      %1014 = "exec.failed"(%1013) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%1014) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b637h7072656c7564659h696e6465785f616464", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "s3h676b7212h706f7765725f6f665f74776f", sym_visibility = "private"}> ({
    ^bb0(%arg449: !runtime.scope, %arg450: ui64):
      %981 = "exec.apply"(%arg449) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%981)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%982: ui64):  // pred: ^bb0
      %983 = "exec.apply"(%arg449) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s2"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%983)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%984: !exec.stop):  // 5 preds: ^bb0, ^bb1, ^bb3, ^bb7, ^bb9
      %985 = "exec.failed"(%984) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%985) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%986: ui64):  // pred: ^bb1
      %987 = "exec.range"(%arg449, %986, %arg450) <{site = "s3"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%987)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i64, i64)>) -> ()
    ^bb4(%988: i64, %989: i64):  // pred: ^bb3
      %990 = "runtime.borrow_transfer"(%arg449, %982) : (!runtime.scope, ui64) -> !runtime.transfer<(ui64)>
      "cf.br"(%988, %990)[^bb5] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb5(%991: i64, %992: !runtime.transfer<(ui64)>):  // 2 preds: ^bb4, ^bb8
      %993 = "arith.cmpi"(%991, %989) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%993, %992)[^bb6, ^bb7] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(ui64)>) -> ()
    ^bb6:  // pred: ^bb5
      %994 = "runtime.iteration"(%arg449, %991) <{site = "s3"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%994)[^bb10, ^bb9] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb7(%995: !runtime.transfer<(ui64)>):  // pred: ^bb5
      %996 = "runtime.accept_transfer"(%arg449, %995) : (!runtime.scope, !runtime.transfer<(ui64)>) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%996)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb8(%997: !runtime.transfer<(ui64)>):  // pred: ^bb12
      %998 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %999 = "arith.addi"(%991, %998) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%999, %997)[^bb5] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb9(%1000: !exec.stop):  // 3 preds: ^bb6, ^bb10, ^bb11
      "runtime.release_transfer"(%992) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%1000)[^bb2] : (!exec.stop) -> ()
    ^bb10(%1001: ui64):  // pred: ^bb6
      %1002 = "runtime.transfer_values"(%992) : (!runtime.transfer<(ui64)>) -> ui64
      %1003 = "runtime.enter_scope"(%arg449, %991, %1001, %1002) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 2>, site = "s3"}> : (!runtime.scope, i64, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%1003)[^bb11, ^bb9] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb11(%1004: !runtime.scope):  // pred: ^bb10
      %1005 = "func.call"(%1004, %1001, %1002) <{callee = @zkl_control_9}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      %1006 = "runtime.exit_scope"(%1004, %1005) : (!runtime.scope, !exec.outcome<(ui64)>) -> !exec.outcome<(!runtime.transfer<(ui64)>)>
      "exec.dispatch"(%1006)[^bb12, ^bb9] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(ui64)>)>) -> ()
    ^bb12(%1007: !runtime.transfer<(ui64)>):  // pred: ^bb11
      "runtime.release_transfer"(%992) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%1007)[^bb8] : (!runtime.transfer<(ui64)>) -> ()
    ^bb13(%1008: ui64):  // pred: ^bb7
      %1009 = "exec.returned"(%1008) : (ui64) -> !exec.outcome<(ui64)>
      "func.return"(%1009) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.origin = ["s3h676b7212h706f7765725f6f665f74776f", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "zkl_control_9", sym_visibility = "private"}> ({
    ^bb0(%arg446: !runtime.scope, %arg447: ui64, %arg448: ui64):
      %974 = "exec.apply"(%arg446) <{binding = @zkl_binding_1, parameters = [2 : ui64], site = "s4"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%974)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%975: ui64):  // pred: ^bb0
      %976 = "exec.apply"(%arg446, %arg448, %975) <{binding = @zkl_binding_6, parameters = [], site = "s5"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%976)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%977: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %978 = "exec.failed"(%977) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%978) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%979: ui64):  // pred: ^bb1
      %980 = "exec.complete"(%arg446, %979) : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "func.return"(%980) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", sym_visibility = "private"}> ({
    ^bb0(%arg445: !runtime.scope):
      %969 = "exec.apply"(%arg445) <{binding = @zkl_binding_8, parameters = [], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%969)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%970: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %971 = "exec.returned"(%970) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%971) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%972: !exec.stop):  // pred: ^bb0
      %973 = "exec.failed"(%972) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%973) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6310h7072696d6974697665736h766563746f725h656d707479", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", sym_visibility = "private"}> ({
    ^bb0(%arg442: !runtime.scope, %arg443: !data.field_vector<"bls12-381.fr">, %arg444: !algebra.field<"bls12-381.fr">):
      %964 = "exec.apply"(%arg442, %arg443, %arg444) <{binding = @zkl_binding_9, parameters = [], site = "s0"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%964)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%965: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %966 = "exec.returned"(%965) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%966) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%967: !exec.stop):  // pred: ^bb0
      %968 = "exec.failed"(%967) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%968) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6310h7072696d6974697665736h766563746f726h617070656e64", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_28c1498dbf9d83fc38ed7b21a89d56146297abcbf1ac78968a8b454c9eef5496", sym_visibility = "private"}> ({
    ^bb0(%arg439: !runtime.scope, %arg440: !data.field_vector<"bls12-381.fr">, %arg441: !data.field_vector<"bls12-381.fr">):
      %945 = "exec.apply"(%arg439, %arg441) <{binding = @zkl_binding_2, parameters = [], site = "s0"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%945)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%946: ui64):  // pred: ^bb0
      %947 = "exec.apply"(%arg439) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s1"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%947)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%948: !exec.stop):  // 6 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6
      %949 = "exec.failed"(%948) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%949) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb3(%950: ui64):  // pred: ^bb1
      %951 = "func.call"(%arg439, %arg440, %946, %950) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a}> {runtime.site = "s2"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%951)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb4(%952: !data.field_vector<"bls12-381.fr">, %953: ui64, %954: ui64):  // pred: ^bb3
      %955 = "func.call"(%arg439, %952, %953, %954, %arg441) <{callee = @zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be}> {runtime.site = "s4"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%955)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb5(%956: !data.field_vector<"bls12-381.fr">, %957: ui64, %958: ui64):  // pred: ^bb4
      %959 = "exec.compute"(%arg439, %956, %957, %958) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33, site = "s5"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%959)[^bb6, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb6(%960: !data.field_vector<"bls12-381.fr">):  // pred: ^bb5
      %961 = "exec.apply"(%arg439, %960) <{binding = @zkl_binding_10, parameters = [], site = "s6"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%961)[^bb7, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb7(%962: !algebra.field<"bls12-381.fr">):  // pred: ^bb6
      %963 = "exec.returned"(%962) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%963) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b728h6576616c75617465", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", sym_visibility = "private"}> ({
    ^bb0(%arg435: !runtime.scope, %arg436: !data.field_vector<"bls12-381.fr">, %arg437: ui64, %arg438: ui64):
      %926 = "func.call"(%arg435, %arg436, %arg437, %arg438) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655}> {runtime.site = "s0"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%926)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%927: i1):  // pred: ^bb0
      %928 = "exec.test"(%arg435, %927) <{site = "s1"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%928)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%929: !exec.stop):  // 8 preds: ^bb0, ^bb1, ^bb4, ^bb5, ^bb7, ^bb8, ^bb10, ^bb11
      %930 = "exec.failed"(%929) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%930) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb3(%931: i1):  // pred: ^bb1
      "cf.cond_br"(%931)[^bb4, ^bb5] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb4:  // pred: ^bb3
      %932 = "runtime.enter_scope"(%arg435) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%932)[^bb7, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb5:  // pred: ^bb3
      %933 = "runtime.enter_scope"(%arg435) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%933)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // 2 preds: ^bb9, ^bb12
      %934 = "exec.returned"(%arg436, %arg437, %arg438) : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%934) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb7(%935: !runtime.scope):  // pred: ^bb4
      %936 = "func.call"(%935) <{callee = @zkl_control_10}> : (!runtime.scope) -> !exec.outcome<>
      %937 = "runtime.exit_scope"(%935, %936) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%937)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb8(%938: !runtime.transfer<>):  // pred: ^bb7
      %939 = "runtime.accept_transfer"(%arg435, %938) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%939)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb9:  // pred: ^bb8
      "cf.br"()[^bb6] : () -> ()
    ^bb10(%940: !runtime.scope):  // pred: ^bb5
      %941 = "func.call"(%940) <{callee = @zkl_control_11}> : (!runtime.scope) -> !exec.outcome<>
      %942 = "runtime.exit_scope"(%940, %941) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%942)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb11(%943: !runtime.transfer<>):  // pred: ^bb10
      %944 = "runtime.accept_transfer"(%arg435, %943) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%944)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb12:  // pred: ^bb11
      "cf.br"()[^bb6] : () -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561725h7461626c65", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_10", sym_visibility = "private"}> ({
    ^bb0(%arg434: !runtime.scope):
      %925 = "exec.complete"(%arg434) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%925) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_11", sym_visibility = "private"}> ({
    ^bb0(%arg433: !runtime.scope):
      %922 = "exec.reject"(%arg433) <{reason = "reject", site = "s1_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%922)[^bb1] : (!exec.stop) -> ()
    ^bb1(%923: !exec.stop):  // pred: ^bb0
      %924 = "exec.failed"(%923) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%924) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be", sym_visibility = "private"}> ({
    ^bb0(%arg428: !runtime.scope, %arg429: !data.field_vector<"bls12-381.fr">, %arg430: ui64, %arg431: ui64, %arg432: !data.field_vector<"bls12-381.fr">):
      %915 = "func.call"(%arg428, %arg429, %arg430, %arg431, %arg432) <{callee = @zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2}> {runtime.site = "s0"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%915)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb1(%916: !data.field_vector<"bls12-381.fr">, %917: ui64, %918: ui64):  // pred: ^bb0
      %919 = "exec.returned"(%916, %917, %918) : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%919) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb2(%920: !exec.stop):  // pred: ^bb0
      %921 = "exec.failed"(%920) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%921) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e65617210h6669785f707265666978", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_195a79478f48dffc2a6917273d8317df0fabae786920a46fa2ac6b2737144299", sym_visibility = "private"}> ({
    ^bb0(%arg423: !runtime.scope, %arg424: !data.field_vector<"bls12-381.fr">, %arg425: ui64, %arg426: ui64, %arg427: !algebra.field<"bls12-381.fr">):
      %908 = "func.call"(%arg423, %arg424, %arg425, %arg426, %arg427) <{callee = @zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d}> {runtime.site = "s2"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%908)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb1(%909: !data.field_vector<"bls12-381.fr">, %910: ui64, %911: ui64):  // pred: ^bb0
      %912 = "exec.returned"(%909, %910, %911) : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%912) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb2(%913: !exec.stop):  // pred: ^bb0
      %914 = "exec.failed"(%913) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%914) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["zks_50b2228592370f9a2bce2e71277fbb9bf36d691d6ece4416923708e3a0c063ae", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d", sym_visibility = "private"}> ({
    ^bb0(%arg418: !runtime.scope, %arg419: !data.field_vector<"bls12-381.fr">, %arg420: ui64, %arg421: ui64, %arg422: !algebra.field<"bls12-381.fr">):
      %896 = "func.call"(%arg418, %arg419, %arg420, %arg421) <{callee = @zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087}> {runtime.site = "s0"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%896)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%897: !data.field_vector<"bls12-381.fr">, %898: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %899 = "exec.collect"(%arg418, %897, %898, %arg422) <{body = @zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body, domain = @zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_domain, site = "s4"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%899)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%900: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %901 = "exec.failed"(%900) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%901) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb3(%902: !data.field_vector<"bls12-381.fr">):  // pred: ^bb1
      %903 = "exec.apply"(%arg418) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s7"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%903)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%904: ui64):  // pred: ^bb3
      %905 = "exec.apply"(%arg418, %arg420, %904) <{binding = @zkl_binding_11, parameters = [], site = "s8"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%905)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%906: ui64):  // pred: ^bb4
      %907 = "exec.returned"(%902, %906, %arg421) : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%907) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561729h6669785f6669727374", []]} : () -> ()
    "data.domain"() <{function_type = (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, sym_name = "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_domain", sym_visibility = "private"}> ({
    ^bb0(%arg416: !data.field_vector<"bls12-381.fr">, %arg417: !data.field_vector<"bls12-381.fr">):
      %893 = "data.domain_elements"(%arg416) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %894 = "data.domain_elements"(%arg417) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %895 = "data.domain_zip"(%893, %894) : (!data.domain<!algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%895) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body", sym_visibility = "private"}> ({
    ^bb0(%arg410: !runtime.scope, %arg411: !algebra.field<"bls12-381.fr">, %arg412: !algebra.field<"bls12-381.fr">, %arg413: !data.field_vector<"bls12-381.fr">, %arg414: !data.field_vector<"bls12-381.fr">, %arg415: !algebra.field<"bls12-381.fr">):
      %888 = "exec.compute"(%arg410, %arg411, %arg412, %arg415) <{callee = @zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5, site = "body"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%888)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%889: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %890 = "exec.returned"(%889) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%890) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%891: !exec.stop):  // pred: ^bb0
      %892 = "exec.failed"(%891) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%892) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087", sym_visibility = "private"}> ({
    ^bb0(%arg406: !runtime.scope, %arg407: !data.field_vector<"bls12-381.fr">, %arg408: ui64, %arg409: ui64):
      %864 = "exec.apply"(%arg406) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%864)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%865: ui64):  // pred: ^bb0
      %866 = "func.call"(%arg406, %865, %arg408) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s2"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%866)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%867: !exec.stop):  // 10 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12
      %868 = "exec.failed"(%867) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "func.return"(%868) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%869: i1):  // pred: ^bb1
      %870 = "exec.test"(%arg406, %869) <{site = "s3"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%870)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb4(%871: i1):  // pred: ^bb3
      "cf.cond_br"(%871)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %872 = "runtime.enter_scope"(%arg406) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s3"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%872)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %873 = "runtime.enter_scope"(%arg406) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s3"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%873)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // 2 preds: ^bb10, ^bb13
      %874 = "exec.apply"(%arg406, %arg407) <{binding = @zkl_binding_12, parameters = [], site = "s5"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%874)[^bb14, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%875: !runtime.scope):  // pred: ^bb5
      %876 = "func.call"(%875) <{callee = @zkl_control_12}> : (!runtime.scope) -> !exec.outcome<>
      %877 = "runtime.exit_scope"(%875, %876) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%877)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb9(%878: !runtime.transfer<>):  // pred: ^bb8
      %879 = "runtime.accept_transfer"(%arg406, %878) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%879)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb10:  // pred: ^bb9
      "cf.br"()[^bb7] : () -> ()
    ^bb11(%880: !runtime.scope):  // pred: ^bb6
      %881 = "func.call"(%880) <{callee = @zkl_control_13}> : (!runtime.scope) -> !exec.outcome<>
      %882 = "runtime.exit_scope"(%880, %881) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%882)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb12(%883: !runtime.transfer<>):  // pred: ^bb11
      %884 = "runtime.accept_transfer"(%arg406, %883) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%884)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb13:  // pred: ^bb12
      "cf.br"()[^bb7] : () -> ()
    ^bb14(%885: !data.field_vector<"bls12-381.fr">, %886: !data.field_vector<"bls12-381.fr">):  // pred: ^bb7
      %887 = "exec.returned"(%885, %886) : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "func.return"(%887) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561726h68616c766573", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_12", sym_visibility = "private"}> ({
    ^bb0(%arg405: !runtime.scope):
      %863 = "exec.complete"(%arg405) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%863) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_13", sym_visibility = "private"}> ({
    ^bb0(%arg404: !runtime.scope):
      %860 = "exec.reject"(%arg404) <{reason = "reject", site = "s3_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%860)[^bb1] : (!exec.stop) -> ()
    ^bb1(%861: !exec.stop):  // pred: ^bb0
      %862 = "exec.failed"(%861) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%862) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5", sym_visibility = "private"}> ({
    ^bb0(%arg401: !algebra.field<"bls12-381.fr">, %arg402: !algebra.field<"bls12-381.fr">, %arg403: !algebra.field<"bls12-381.fr">):
      %857 = "algebra.field_subtract"(%arg402, %arg401) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %858 = "algebra.field_multiply"(%857, %arg403) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %859 = "algebra.field_add"(%arg401, %858) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%859) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2", sym_visibility = "private"}> ({
    ^bb0(%arg396: !runtime.scope, %arg397: !data.field_vector<"bls12-381.fr">, %arg398: ui64, %arg399: ui64, %arg400: !data.field_vector<"bls12-381.fr">):
      %850 = "exec.fold"(%arg396, %arg400, %arg397, %arg398, %arg399) <{domain = @finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_domain, site = "s0", step = @finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%850)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb1(%851: !data.field_vector<"bls12-381.fr">, %852: ui64, %853: ui64):  // pred: ^bb0
      %854 = "exec.returned"(%851, %852, %853) : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%854) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb2(%855: !exec.stop):  // pred: ^bb0
      %856 = "exec.failed"(%855) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%856) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg395: !data.field_vector<"bls12-381.fr">):
      %849 = "data.domain_elements"(%arg395) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%849) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg389: !runtime.scope, %arg390: !data.field_vector<"bls12-381.fr">, %arg391: ui64, %arg392: ui64, %arg393: !algebra.field<"bls12-381.fr">, %arg394: !data.field_vector<"bls12-381.fr">):
      %842 = "func.call"(%arg389, %arg390, %arg391, %arg392, %arg393) <{callee = @zkl_195a79478f48dffc2a6917273d8317df0fabae786920a46fa2ac6b2737144299}> {runtime.site = "body"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%842)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb1(%843: !data.field_vector<"bls12-381.fr">, %844: ui64, %845: ui64):  // pred: ^bb0
      %846 = "exec.returned"(%843, %844, %845) : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%846) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb2(%847: !exec.stop):  // pred: ^bb0
      %848 = "exec.failed"(%847) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%848) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body", []]} : () -> ()
    "func.func"() <{function_type = (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !data.field_vector<"bls12-381.fr">, sym_name = "zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", sym_visibility = "private"}> ({
    ^bb0(%arg386: !data.field_vector<"bls12-381.fr">, %arg387: ui64, %arg388: ui64):
      "func.return"(%arg386) : (!data.field_vector<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_7b9dfa97fa3e158d428459ec12d8a2d5aa171a060ab79f314eeccc53ee772b17", sym_visibility = "private"}> ({
    ^bb0(%arg383: !runtime.scope, %arg384: !data.field_vector<"bls12-381.fr">, %arg385: !algebra.field<"bls12-381.fr">):
      %837 = "exec.apply"(%arg383) <{binding = @zkl_binding_13, parameters = [], site = "s0_create_0"}> : (!runtime.scope) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">)>
      "exec.dispatch"(%837)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">)>) -> ()
    ^bb1(%838: !runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">):  // pred: ^bb0
      %839 = "exec.returned"(%838, %arg384, %arg385) : (!runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%839) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%840: !exec.stop):  // pred: ^bb0
      %841 = "exec.failed"(%840) : (!exec.stop) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%841) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7211h6c617965725f636c61696d", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_e0f7a4e58ae24eb13e9b2033c42c179b2766ff6cdb4ae1470bf7ef9b1721d646", sym_visibility = "private"}> ({
    ^bb0(%arg379: !runtime.scope, %arg380: !runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, %arg381: !data.field_vector<"bls12-381.fr">, %arg382: !algebra.field<"bls12-381.fr">):
      %836 = "exec.returned"(%arg380, %arg381, %arg382, %arg381, %arg382) : (!runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%836) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7210h6f70656e5f6c61796572", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, ui64, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_8c63ad97d926a7762c597860addde408bcd2077ea9cda1b99df123dc13e64af6", sym_visibility = "private"}> ({
    ^bb0(%arg371: !runtime.scope, %arg372: !data.field_vector<"bls12-381.fr">, %arg373: !data.field_vector<"bls12-381.fr">, %arg374: !data.field_vector<"bls12-381.fr">, %arg375: ui64, %arg376: ui64, %arg377: ui64, %arg378: ui64):
      %802 = "exec.apply"(%arg371) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s2"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%802)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%803: ui64):  // pred: ^bb0
      %804 = "exec.apply"(%arg371, %arg375, %arg378) <{binding = @zkl_binding_11, parameters = [], site = "s3"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%804)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%805: !exec.stop):  // 7 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb9, ^bb11
      %806 = "exec.failed"(%805) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%806) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%807: ui64):  // pred: ^bb1
      %808 = "exec.apply"(%arg371) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s4"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%808)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%809: ui64):  // pred: ^bb3
      %810 = "exec.apply"(%arg371, %807, %809) <{binding = @zkl_binding_11, parameters = [], site = "s5"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%810)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%811: ui64):  // pred: ^bb4
      %812 = "exec.range"(%arg371, %803, %811) <{site = "s10"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%812)[^bb6, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i64, i64)>) -> ()
    ^bb6(%813: i64, %814: i64):  // pred: ^bb5
      %815 = "runtime.borrow_transfer"(%arg371, %arg374, %arg375) : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>
      "cf.br"(%813, %815)[^bb7] : (i64, !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb7(%816: i64, %817: !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>):  // 2 preds: ^bb6, ^bb10
      %818 = "arith.cmpi"(%816, %814) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%818, %817)[^bb8, ^bb9] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb8:  // pred: ^bb7
      %819 = "runtime.iteration"(%arg371, %816) <{site = "s10"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%819)[^bb12, ^bb11] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb9(%820: !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>):  // pred: ^bb7
      %821 = "runtime.accept_transfer"(%arg371, %820) : (!runtime.scope, !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>
      "exec.dispatch"(%821)[^bb15, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb10(%822: !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>):  // pred: ^bb14
      %823 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %824 = "arith.addi"(%816, %823) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%824, %822)[^bb7] : (i64, !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb11(%825: !exec.stop):  // 3 preds: ^bb8, ^bb12, ^bb13
      "runtime.release_transfer"(%817) : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
      "cf.br"(%825)[^bb2] : (!exec.stop) -> ()
    ^bb12(%826: ui64):  // pred: ^bb8
      %827:2 = "runtime.transfer_values"(%817) : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> (!data.field_vector<"bls12-381.fr">, ui64)
      %828 = "runtime.enter_scope"(%arg371, %816, %826, %827#0, %827#1, %arg372, %arg373, %arg376, %arg377) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 7>, site = "s10"}> : (!runtime.scope, i64, ui64, !data.field_vector<"bls12-381.fr">, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%828)[^bb13, ^bb11] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb13(%829: !runtime.scope):  // pred: ^bb12
      %830 = "func.call"(%829, %826, %827#0, %827#1, %arg372, %arg373, %arg376, %arg377) <{callee = @zkl_control_14}> : (!runtime.scope, ui64, !data.field_vector<"bls12-381.fr">, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>
      %831 = "runtime.exit_scope"(%829, %830) : (!runtime.scope, !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>) -> !exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>)>
      "exec.dispatch"(%831)[^bb14, ^bb11] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>)>) -> ()
    ^bb14(%832: !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>):  // pred: ^bb13
      "runtime.release_transfer"(%817) : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
      "cf.br"(%832)[^bb10] : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb15(%833: !data.field_vector<"bls12-381.fr">, %834: ui64):  // pred: ^bb9
      %835 = "exec.returned"(%833) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%835) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7212h76616c7565735f62656c6f77", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, !data.field_vector<"bls12-381.fr">, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>, no_inline, sym_name = "zkl_control_14", sym_visibility = "private"}> ({
    ^bb0(%arg363: !runtime.scope, %arg364: ui64, %arg365: !data.field_vector<"bls12-381.fr">, %arg366: ui64, %arg367: !data.field_vector<"bls12-381.fr">, %arg368: !data.field_vector<"bls12-381.fr">, %arg369: ui64, %arg370: ui64):
      %789 = "exec.apply"(%arg363) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s11"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%789)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%790: ui64):  // pred: ^bb0
      %791 = "exec.apply"(%arg363, %arg366, %790) <{binding = @zkl_binding_11, parameters = [], site = "s12"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%791)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%792: !exec.stop):  // 5 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5
      %793 = "exec.failed"(%792) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>
      "func.return"(%793) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb3(%794: ui64):  // pred: ^bb1
      %795 = "func.call"(%arg363, %arg367, %794, %arg369) <{callee = @zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e}> {runtime.site = "s14"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%795)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb4(%796: !data.field_vector<"bls12-381.fr">):  // pred: ^bb3
      %797 = "func.call"(%arg363, %arg368, %794, %arg369) <{callee = @zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e}> {runtime.site = "s15"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%797)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb5(%798: !data.field_vector<"bls12-381.fr">):  // pred: ^bb4
      %799 = "func.call"(%arg363, %796, %798, %arg365, %arg370) <{callee = @zkl_3a99bc0fa1dab7cb27c9ec80754c3782b0a32e76ddc961a50e12c24c6cbff683}> {runtime.site = "s16"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%799)[^bb6, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb6(%800: !data.field_vector<"bls12-381.fr">):  // pred: ^bb5
      %801 = "exec.complete"(%arg363, %800, %794) : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>
      "func.return"(%801) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", sym_visibility = "private"}> ({
    ^bb0(%arg359: !runtime.scope, %arg360: !data.field_vector<"bls12-381.fr">, %arg361: ui64, %arg362: ui64):
      %761 = "exec.apply"(%arg359) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s2"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%761)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%762: ui64):  // pred: ^bb0
      %763 = "exec.range"(%arg359, %762, %arg362) <{site = "s4"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%763)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i64, i64)>) -> ()
    ^bb2(%764: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb6, ^bb8
      %765 = "exec.failed"(%764) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%765) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%766: i64, %767: i64):  // pred: ^bb1
      %768 = "runtime.borrow_transfer"(%arg359, %arg360, %arg362) : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>
      "cf.br"(%766, %768)[^bb4] : (i64, !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb4(%769: i64, %770: !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>):  // 2 preds: ^bb3, ^bb7
      %771 = "arith.cmpi"(%769, %767) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%771, %770)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb5:  // pred: ^bb4
      %772 = "runtime.iteration"(%arg359, %769) <{site = "s4"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%772)[^bb9, ^bb8] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb6(%773: !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>):  // pred: ^bb4
      %774 = "runtime.accept_transfer"(%arg359, %773) : (!runtime.scope, !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>
      "exec.dispatch"(%774)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb7(%775: !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>):  // pred: ^bb11
      %776 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %777 = "arith.addi"(%769, %776) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%777, %775)[^bb4] : (i64, !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb8(%778: !exec.stop):  // 3 preds: ^bb5, ^bb9, ^bb10
      "runtime.release_transfer"(%770) : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
      "cf.br"(%778)[^bb2] : (!exec.stop) -> ()
    ^bb9(%779: ui64):  // pred: ^bb5
      %780:2 = "runtime.transfer_values"(%770) : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> (!data.field_vector<"bls12-381.fr">, ui64)
      %781 = "runtime.enter_scope"(%arg359, %769, %779, %780#0, %780#1, %arg361) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 4>, site = "s4"}> : (!runtime.scope, i64, ui64, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%781)[^bb10, ^bb8] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb10(%782: !runtime.scope):  // pred: ^bb9
      %783 = "func.call"(%782, %779, %780#0, %780#1, %arg361) <{callee = @zkl_control_15}> : (!runtime.scope, ui64, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>
      %784 = "runtime.exit_scope"(%782, %783) : (!runtime.scope, !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>) -> !exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>)>
      "exec.dispatch"(%784)[^bb11, ^bb8] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>)>) -> ()
    ^bb11(%785: !runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>):  // pred: ^bb10
      "runtime.release_transfer"(%770) : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
      "cf.br"(%785)[^bb7] : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb12(%786: !data.field_vector<"bls12-381.fr">, %787: ui64):  // pred: ^bb6
      %788 = "exec.returned"(%786) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%788) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7212h73656c6563745f626c6f636b", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>, no_inline, sym_name = "zkl_control_15", sym_visibility = "private"}> ({
    ^bb0(%arg354: !runtime.scope, %arg355: ui64, %arg356: !data.field_vector<"bls12-381.fr">, %arg357: ui64, %arg358: ui64):
      %722 = "exec.apply"(%arg354) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s5"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%722)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%723: ui64):  // pred: ^bb0
      %724 = "exec.apply"(%arg354, %arg357, %723) <{binding = @zkl_binding_11, parameters = [], site = "s6"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%724)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%725: !exec.stop):  // 16 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb10, ^bb12, ^bb13, ^bb15, ^bb16, ^bb18, ^bb19
      %726 = "exec.failed"(%725) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>
      "func.return"(%726) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb3(%727: ui64):  // pred: ^bb1
      %728 = "func.call"(%arg354, %727) <{callee = @s3h676b7212h706f7765725f6f665f74776f}> {runtime.site = "s8"} : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%728)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%729: ui64):  // pred: ^bb3
      %730 = "exec.apply"(%arg354, %arg358, %729) <{binding = @zkl_binding_5, parameters = [], site = "s9"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%730)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%731: ui64):  // pred: ^bb4
      %732 = "exec.apply"(%arg354) <{binding = @zkl_binding_1, parameters = [2 : ui64], site = "s10"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%732)[^bb6, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb6(%733: ui64):  // pred: ^bb5
      %734 = "exec.apply"(%arg354, %731, %733) <{binding = @zkl_binding_3, parameters = [], site = "s11"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%734)[^bb7, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb7(%735: ui64):  // pred: ^bb6
      %736 = "exec.apply"(%arg354, %arg356) <{binding = @zkl_binding_12, parameters = [], site = "s13"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%736)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%737: !data.field_vector<"bls12-381.fr">, %738: !data.field_vector<"bls12-381.fr">):  // pred: ^bb7
      %739 = "exec.apply"(%arg354) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s15"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%739)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb9(%740: ui64):  // pred: ^bb8
      %741 = "exec.apply"(%arg354, %735, %740) <{binding = @zkl_binding_4, parameters = [], site = "s16"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%741)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb10(%742: i1):  // pred: ^bb9
      %743 = "exec.test"(%arg354, %742) <{site = "s19"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%743)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb11(%744: i1):  // pred: ^bb10
      "cf.cond_br"(%744)[^bb12, ^bb13] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb12:  // pred: ^bb11
      %745 = "runtime.enter_scope"(%arg354, %737, %738) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "then", site = "s19"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%745)[^bb15, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb13:  // pred: ^bb11
      %746 = "runtime.enter_scope"(%arg354, %737, %738) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "else", site = "s19"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%746)[^bb18, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb14(%747: !data.field_vector<"bls12-381.fr">):  // 2 preds: ^bb17, ^bb20
      %748 = "exec.complete"(%arg354, %747, %727) : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>
      "func.return"(%748) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64)>) -> ()
    ^bb15(%749: !runtime.scope):  // pred: ^bb12
      %750 = "func.call"(%749, %737, %738) <{callee = @zkl_control_16}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      %751 = "runtime.exit_scope"(%749, %750) : (!runtime.scope, !exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>)>
      "exec.dispatch"(%751)[^bb16, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>)>) -> ()
    ^bb16(%752: !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>):  // pred: ^bb15
      %753 = "runtime.accept_transfer"(%arg354, %752) : (!runtime.scope, !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%753)[^bb17, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb17(%754: !data.field_vector<"bls12-381.fr">):  // pred: ^bb16
      "cf.br"(%754)[^bb14] : (!data.field_vector<"bls12-381.fr">) -> ()
    ^bb18(%755: !runtime.scope):  // pred: ^bb13
      %756 = "func.call"(%755, %737, %738) <{callee = @zkl_control_17}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      %757 = "runtime.exit_scope"(%755, %756) : (!runtime.scope, !exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>)>
      "exec.dispatch"(%757)[^bb19, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>)>) -> ()
    ^bb19(%758: !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>):  // pred: ^bb18
      %759 = "runtime.accept_transfer"(%arg354, %758) : (!runtime.scope, !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%759)[^bb20, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb20(%760: !data.field_vector<"bls12-381.fr">):  // pred: ^bb19
      "cf.br"(%760)[^bb14] : (!data.field_vector<"bls12-381.fr">) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_16", sym_visibility = "private"}> ({
    ^bb0(%arg351: !runtime.scope, %arg352: !data.field_vector<"bls12-381.fr">, %arg353: !data.field_vector<"bls12-381.fr">):
      %721 = "exec.complete"(%arg351, %arg353) : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%721) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_17", sym_visibility = "private"}> ({
    ^bb0(%arg348: !runtime.scope, %arg349: !data.field_vector<"bls12-381.fr">, %arg350: !data.field_vector<"bls12-381.fr">):
      %720 = "exec.complete"(%arg348, %arg349) : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%720) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_3a99bc0fa1dab7cb27c9ec80754c3782b0a32e76ddc961a50e12c24c6cbff683", sym_visibility = "private"}> ({
    ^bb0(%arg343: !runtime.scope, %arg344: !data.field_vector<"bls12-381.fr">, %arg345: !data.field_vector<"bls12-381.fr">, %arg346: !data.field_vector<"bls12-381.fr">, %arg347: ui64):
      %685 = "func.call"(%arg343, %arg347) <{callee = @s3h676b7212h706f7765725f6f665f74776f}> {runtime.site = "s0"} : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%685)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%686: ui64):  // pred: ^bb0
      %687 = "func.call"(%arg343, %arg346, %686) <{callee = @zkl_afd97de07c9ccae9db68186ebf66098aed7daffb4b11c598d0da5cd116df8490}> {runtime.site = "s2"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%687)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%688: !exec.stop):  // 8 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb10, ^bb12
      %689 = "exec.failed"(%688) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%689) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%690: !data.field_vector<"bls12-381.fr">):  // pred: ^bb1
      %691 = "func.call"(%arg343, %arg346, %686) <{callee = @zkl_33f3047479634e63ecd16a0855f88ad8af019c37d677a4ffe6f5bacc63307947}> {runtime.site = "s4"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%691)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb4(%692: !data.field_vector<"bls12-381.fr">):  // pred: ^bb3
      %693 = "exec.apply"(%arg343) <{binding = @zkl_binding_8, parameters = [], site = "s6"}> : (!runtime.scope) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%693)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb5(%694: !data.field_vector<"bls12-381.fr">):  // pred: ^bb4
      %695 = "exec.apply"(%arg343) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s8"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%695)[^bb6, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb6(%696: ui64):  // pred: ^bb5
      %697 = "exec.range"(%arg343, %696, %686) <{site = "s14"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%697)[^bb7, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i64, i64)>) -> ()
    ^bb7(%698: i64, %699: i64):  // pred: ^bb6
      %700 = "runtime.borrow_transfer"(%arg343, %694) : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>
      "cf.br"(%698, %700)[^bb8] : (i64, !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%701: i64, %702: !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>):  // 2 preds: ^bb7, ^bb11
      %703 = "arith.cmpi"(%701, %699) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%703, %702)[^bb9, ^bb10] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb9:  // pred: ^bb8
      %704 = "runtime.iteration"(%arg343, %701) <{site = "s14"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%704)[^bb13, ^bb12] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb10(%705: !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>):  // pred: ^bb8
      %706 = "runtime.accept_transfer"(%arg343, %705) : (!runtime.scope, !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%706)[^bb16, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb11(%707: !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>):  // pred: ^bb15
      %708 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %709 = "arith.addi"(%701, %708) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%709, %707)[^bb8] : (i64, !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb12(%710: !exec.stop):  // 3 preds: ^bb9, ^bb13, ^bb14
      "runtime.release_transfer"(%702) : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
      "cf.br"(%710)[^bb2] : (!exec.stop) -> ()
    ^bb13(%711: ui64):  // pred: ^bb9
      %712 = "runtime.transfer_values"(%702) : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> !data.field_vector<"bls12-381.fr">
      %713 = "runtime.enter_scope"(%arg343, %701, %711, %712, %arg344, %arg345, %arg347, %690, %692) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 7>, site = "s14"}> : (!runtime.scope, i64, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%713)[^bb14, ^bb12] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb14(%714: !runtime.scope):  // pred: ^bb13
      %715 = "func.call"(%714, %711, %712, %arg344, %arg345, %arg347, %690, %692) <{callee = @zkl_control_18}> : (!runtime.scope, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      %716 = "runtime.exit_scope"(%714, %715) : (!runtime.scope, !exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>)>
      "exec.dispatch"(%716)[^bb15, ^bb12] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>)>) -> ()
    ^bb15(%717: !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>):  // pred: ^bb14
      "runtime.release_transfer"(%702) : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
      "cf.br"(%717)[^bb11] : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb16(%718: !data.field_vector<"bls12-381.fr">):  // pred: ^bb10
      %719 = "exec.returned"(%718) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%719) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7212h6c617965725f76616c756573", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_18", sym_visibility = "private"}> ({
    ^bb0(%arg335: !runtime.scope, %arg336: ui64, %arg337: !data.field_vector<"bls12-381.fr">, %arg338: !data.field_vector<"bls12-381.fr">, %arg339: !data.field_vector<"bls12-381.fr">, %arg340: ui64, %arg341: !data.field_vector<"bls12-381.fr">, %arg342: !data.field_vector<"bls12-381.fr">):
      %672 = "func.call"(%arg335, %arg338, %arg336, %arg340) <{callee = @zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e}> {runtime.site = "s15"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%672)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%673: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %674 = "func.call"(%arg335, %arg339, %arg336, %arg340) <{callee = @zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e}> {runtime.site = "s17"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%674)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%675: !exec.stop):  // 5 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5
      %676 = "exec.failed"(%675) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%676) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%677: !data.field_vector<"bls12-381.fr">):  // pred: ^bb1
      %678 = "exec.collect"(%arg335, %673, %677, %arg341, %arg342) <{body = @zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_body, domain = @zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_domain, site = "s19"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%678)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb4(%679: !data.field_vector<"bls12-381.fr">):  // pred: ^bb3
      %680 = "exec.apply"(%arg335, %679) <{binding = @zkl_binding_10, parameters = [], site = "s20"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%680)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb5(%681: !algebra.field<"bls12-381.fr">):  // pred: ^bb4
      %682 = "exec.apply"(%arg335, %arg337, %681) <{binding = @zkl_binding_9, parameters = [], site = "s21"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%682)[^bb6, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb6(%683: !data.field_vector<"bls12-381.fr">):  // pred: ^bb5
      %684 = "exec.complete"(%arg335, %683) : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%684) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "data.domain"() <{function_type = (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, sym_name = "zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_domain", sym_visibility = "private"}> ({
    ^bb0(%arg331: !data.field_vector<"bls12-381.fr">, %arg332: !data.field_vector<"bls12-381.fr">, %arg333: !data.field_vector<"bls12-381.fr">, %arg334: !data.field_vector<"bls12-381.fr">):
      %665 = "data.domain_elements"(%arg331) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %666 = "data.domain_elements"(%arg332) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %667 = "data.domain_zip"(%665, %666) : (!data.domain<!algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      %668 = "data.domain_elements"(%arg333) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %669 = "data.domain_zip"(%667, %668) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      %670 = "data.domain_elements"(%arg334) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %671 = "data.domain_zip"(%669, %670) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%671) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_body", sym_visibility = "private"}> ({
    ^bb0(%arg322: !runtime.scope, %arg323: !algebra.field<"bls12-381.fr">, %arg324: !algebra.field<"bls12-381.fr">, %arg325: !algebra.field<"bls12-381.fr">, %arg326: !algebra.field<"bls12-381.fr">, %arg327: !data.field_vector<"bls12-381.fr">, %arg328: !data.field_vector<"bls12-381.fr">, %arg329: !data.field_vector<"bls12-381.fr">, %arg330: !data.field_vector<"bls12-381.fr">):
      %660 = "exec.compute"(%arg322, %arg323, %arg324, %arg325, %arg326) <{callee = @zkl_6b3d366572d1ba53650a202f39ff52a2f298a1591829443fbeaa34ef3974f084, site = "body"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%660)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%661: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %662 = "exec.returned"(%661) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%662) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%663: !exec.stop):  // pred: ^bb0
      %664 = "exec.failed"(%663) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%664) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_body", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_afd97de07c9ccae9db68186ebf66098aed7daffb4b11c598d0da5cd116df8490", sym_visibility = "private"}> ({
    ^bb0(%arg319: !runtime.scope, %arg320: !data.field_vector<"bls12-381.fr">, %arg321: ui64):
      %653 = "exec.apply"(%arg319) <{binding = @zkl_binding_8, parameters = [], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%653)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%654: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %655 = "func.call"(%arg319, %654, %arg321, %arg320) <{callee = @zkl_33e26704899171b0d3e366f86377dfc6602b55f53021ce20930f7ae9e8061294}> {runtime.site = "s2"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%655)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%656: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %657 = "exec.failed"(%656) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%657) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%658: !data.field_vector<"bls12-381.fr">):  // pred: ^bb1
      %659 = "exec.returned"(%658) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%659) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b729h7265706c6963617465", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_e7a7efcd14676d32c0e577ff1097f611a3dc84c74ecaa8bfdbebb25968971255", sym_visibility = "private"}> ({
    ^bb0(%arg315: !runtime.scope, %arg316: !data.field_vector<"bls12-381.fr">, %arg317: !algebra.field<"bls12-381.fr">, %arg318: ui64):
      %648 = "func.call"(%arg315, %arg316, %arg317, %arg318) <{callee = @zkl_fbd2531b804047766f8107241edd0ea81368b70795e44e4d8e07484d142783bb}> {runtime.site = "s2"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%648)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%649: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %650 = "exec.returned"(%649) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%650) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%651: !exec.stop):  // pred: ^bb0
      %652 = "exec.failed"(%651) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%652) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zks_99cdc30b104640f79094177f26387b3c04df24c083a5fa7125a3fd69fc1eb459", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_fbd2531b804047766f8107241edd0ea81368b70795e44e4d8e07484d142783bb", sym_visibility = "private"}> ({
    ^bb0(%arg311: !runtime.scope, %arg312: !data.field_vector<"bls12-381.fr">, %arg313: !algebra.field<"bls12-381.fr">, %arg314: ui64):
      %621 = "exec.apply"(%arg311) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s1"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%621)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%622: ui64):  // pred: ^bb0
      %623 = "exec.range"(%arg311, %622, %arg314) <{site = "s3"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%623)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i64, i64)>) -> ()
    ^bb2(%624: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb6, ^bb8
      %625 = "exec.failed"(%624) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%625) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%626: i64, %627: i64):  // pred: ^bb1
      %628 = "runtime.borrow_transfer"(%arg311, %arg312) : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>
      "cf.br"(%626, %628)[^bb4] : (i64, !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb4(%629: i64, %630: !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>):  // 2 preds: ^bb3, ^bb7
      %631 = "arith.cmpi"(%629, %627) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%631, %630)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb5:  // pred: ^bb4
      %632 = "runtime.iteration"(%arg311, %629) <{site = "s3"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%632)[^bb9, ^bb8] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb6(%633: !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>):  // pred: ^bb4
      %634 = "runtime.accept_transfer"(%arg311, %633) : (!runtime.scope, !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%634)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb7(%635: !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>):  // pred: ^bb11
      %636 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %637 = "arith.addi"(%629, %636) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%637, %635)[^bb4] : (i64, !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%638: !exec.stop):  // 3 preds: ^bb5, ^bb9, ^bb10
      "runtime.release_transfer"(%630) : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
      "cf.br"(%638)[^bb2] : (!exec.stop) -> ()
    ^bb9(%639: ui64):  // pred: ^bb5
      %640 = "runtime.transfer_values"(%630) : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> !data.field_vector<"bls12-381.fr">
      %641 = "runtime.enter_scope"(%arg311, %629, %639, %640, %arg313) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 3>, site = "s3"}> : (!runtime.scope, i64, ui64, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%641)[^bb10, ^bb8] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb10(%642: !runtime.scope):  // pred: ^bb9
      %643 = "func.call"(%642, %639, %640, %arg313) <{callee = @zkl_control_19}> : (!runtime.scope, ui64, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      %644 = "runtime.exit_scope"(%642, %643) : (!runtime.scope, !exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>)>
      "exec.dispatch"(%644)[^bb11, ^bb8] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>)>) -> ()
    ^bb11(%645: !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>):  // pred: ^bb10
      "runtime.release_transfer"(%630) : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
      "cf.br"(%645)[^bb7] : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb12(%646: !data.field_vector<"bls12-381.fr">):  // pred: ^bb6
      %647 = "exec.returned"(%646) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%647) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7212h7265706561745f76616c7565", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_19", sym_visibility = "private"}> ({
    ^bb0(%arg307: !runtime.scope, %arg308: ui64, %arg309: !data.field_vector<"bls12-381.fr">, %arg310: !algebra.field<"bls12-381.fr">):
      %616 = "exec.apply"(%arg307, %arg309, %arg310) <{binding = @zkl_binding_9, parameters = [], site = "s4"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%616)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%617: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %618 = "exec.complete"(%arg307, %617) : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%618) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%619: !exec.stop):  // pred: ^bb0
      %620 = "exec.failed"(%619) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%620) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_33e26704899171b0d3e366f86377dfc6602b55f53021ce20930f7ae9e8061294", sym_visibility = "private"}> ({
    ^bb0(%arg303: !runtime.scope, %arg304: !data.field_vector<"bls12-381.fr">, %arg305: ui64, %arg306: !data.field_vector<"bls12-381.fr">):
      %611 = "exec.fold"(%arg303, %arg306, %arg304, %arg305) <{domain = @finite_zkl_33e26704899171b0d3e366f86377dfc6602b55f53021ce20930f7ae9e8061294_s0_domain, site = "s0", step = @finite_zkl_33e26704899171b0d3e366f86377dfc6602b55f53021ce20930f7ae9e8061294_s0_body}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%611)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%612: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %613 = "exec.returned"(%612) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%613) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%614: !exec.stop):  // pred: ^bb0
      %615 = "exec.failed"(%614) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%615) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_33e26704899171b0d3e366f86377dfc6602b55f53021ce20930f7ae9e8061294_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg302: !data.field_vector<"bls12-381.fr">):
      %610 = "data.domain_elements"(%arg302) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%610) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "finite_zkl_33e26704899171b0d3e366f86377dfc6602b55f53021ce20930f7ae9e8061294_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg297: !runtime.scope, %arg298: !data.field_vector<"bls12-381.fr">, %arg299: !algebra.field<"bls12-381.fr">, %arg300: !data.field_vector<"bls12-381.fr">, %arg301: ui64):
      %605 = "func.call"(%arg297, %arg298, %arg299, %arg301) <{callee = @zkl_e7a7efcd14676d32c0e577ff1097f611a3dc84c74ecaa8bfdbebb25968971255}> {runtime.site = "body"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%605)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%606: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %607 = "exec.returned"(%606) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%607) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%608: !exec.stop):  // pred: ^bb0
      %609 = "exec.failed"(%608) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%609) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["finite_zkl_33e26704899171b0d3e366f86377dfc6602b55f53021ce20930f7ae9e8061294_s0_body", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_33f3047479634e63ecd16a0855f88ad8af019c37d677a4ffe6f5bacc63307947", sym_visibility = "private"}> ({
    ^bb0(%arg294: !runtime.scope, %arg295: !data.field_vector<"bls12-381.fr">, %arg296: ui64):
      %576 = "exec.apply"(%arg294) <{binding = @zkl_binding_8, parameters = [], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%576)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%577: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %578 = "exec.apply"(%arg294) <{binding = @zkl_binding_1, parameters = [0 : ui64], site = "s2"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%578)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%579: !exec.stop):  // 5 preds: ^bb0, ^bb1, ^bb3, ^bb7, ^bb9
      %580 = "exec.failed"(%579) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%580) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%581: ui64):  // pred: ^bb1
      %582 = "exec.range"(%arg294, %581, %arg296) <{site = "s4"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%582)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i64, i64)>) -> ()
    ^bb4(%583: i64, %584: i64):  // pred: ^bb3
      %585 = "runtime.borrow_transfer"(%arg294, %577) : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>
      "cf.br"(%583, %585)[^bb5] : (i64, !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb5(%586: i64, %587: !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>):  // 2 preds: ^bb4, ^bb8
      %588 = "arith.cmpi"(%586, %584) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%588, %587)[^bb6, ^bb7] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb6:  // pred: ^bb5
      %589 = "runtime.iteration"(%arg294, %586) <{site = "s4"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%589)[^bb10, ^bb9] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb7(%590: !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>):  // pred: ^bb5
      %591 = "runtime.accept_transfer"(%arg294, %590) : (!runtime.scope, !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%591)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%592: !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>):  // pred: ^bb12
      %593 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %594 = "arith.addi"(%586, %593) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%594, %592)[^bb5] : (i64, !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb9(%595: !exec.stop):  // 3 preds: ^bb6, ^bb10, ^bb11
      "runtime.release_transfer"(%587) : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
      "cf.br"(%595)[^bb2] : (!exec.stop) -> ()
    ^bb10(%596: ui64):  // pred: ^bb6
      %597 = "runtime.transfer_values"(%587) : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> !data.field_vector<"bls12-381.fr">
      %598 = "runtime.enter_scope"(%arg294, %586, %596, %597, %arg295) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 3>, site = "s4"}> : (!runtime.scope, i64, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%598)[^bb11, ^bb9] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb11(%599: !runtime.scope):  // pred: ^bb10
      %600 = "func.call"(%599, %596, %597, %arg295) <{callee = @zkl_control_20}> : (!runtime.scope, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      %601 = "runtime.exit_scope"(%599, %600) : (!runtime.scope, !exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>)>
      "exec.dispatch"(%601)[^bb12, ^bb9] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>)>) -> ()
    ^bb12(%602: !runtime.transfer<(!data.field_vector<"bls12-381.fr">)>):  // pred: ^bb11
      "runtime.release_transfer"(%587) : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
      "cf.br"(%602)[^bb8] : (!runtime.transfer<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb13(%603: !data.field_vector<"bls12-381.fr">):  // pred: ^bb7
      %604 = "exec.returned"(%603) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%604) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b724h74696c65", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_control_20", sym_visibility = "private"}> ({
    ^bb0(%arg290: !runtime.scope, %arg291: ui64, %arg292: !data.field_vector<"bls12-381.fr">, %arg293: !data.field_vector<"bls12-381.fr">):
      %571 = "func.call"(%arg290, %arg292, %arg293) <{callee = @zkl_5939bc7a1ddcd11f8e2153f23b3ed89c16434b9b99db1512543ee10e7b59b248}> {runtime.site = "s5"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%571)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%572: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %573 = "exec.complete"(%arg290, %572) : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%573) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%574: !exec.stop):  // pred: ^bb0
      %575 = "exec.failed"(%574) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%575) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_ac1d3513b06c1d4950d126f678b9482e4ca13944fc4b35442d1a33796d064b0c", sym_visibility = "private"}> ({
    ^bb0(%arg287: !runtime.scope, %arg288: !data.field_vector<"bls12-381.fr">, %arg289: !algebra.field<"bls12-381.fr">):
      %566 = "exec.apply"(%arg287, %arg288, %arg289) <{binding = @zkl_binding_9, parameters = [], site = "s2"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%566)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%567: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %568 = "exec.returned"(%567) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%568) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%569: !exec.stop):  // pred: ^bb0
      %570 = "exec.failed"(%569) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%570) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zks_42e44eec4fd7419218a6cf70cf462d528dfc3e199764475009d12bc09d4ada97", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_5939bc7a1ddcd11f8e2153f23b3ed89c16434b9b99db1512543ee10e7b59b248", sym_visibility = "private"}> ({
    ^bb0(%arg284: !runtime.scope, %arg285: !data.field_vector<"bls12-381.fr">, %arg286: !data.field_vector<"bls12-381.fr">):
      %561 = "exec.fold"(%arg284, %arg286, %arg285) <{domain = @finite_zkl_5939bc7a1ddcd11f8e2153f23b3ed89c16434b9b99db1512543ee10e7b59b248_s0_domain, site = "s0", step = @finite_zkl_5939bc7a1ddcd11f8e2153f23b3ed89c16434b9b99db1512543ee10e7b59b248_s0_body}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%561)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%562: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %563 = "exec.returned"(%562) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%563) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%564: !exec.stop):  // pred: ^bb0
      %565 = "exec.failed"(%564) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%565) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_5939bc7a1ddcd11f8e2153f23b3ed89c16434b9b99db1512543ee10e7b59b248_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg283: !data.field_vector<"bls12-381.fr">):
      %560 = "data.domain_elements"(%arg283) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%560) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "finite_zkl_5939bc7a1ddcd11f8e2153f23b3ed89c16434b9b99db1512543ee10e7b59b248_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg279: !runtime.scope, %arg280: !data.field_vector<"bls12-381.fr">, %arg281: !algebra.field<"bls12-381.fr">, %arg282: !data.field_vector<"bls12-381.fr">):
      %555 = "func.call"(%arg279, %arg280, %arg281) <{callee = @zkl_ac1d3513b06c1d4950d126f678b9482e4ca13944fc4b35442d1a33796d064b0c}> {runtime.site = "body"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%555)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%556: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %557 = "exec.returned"(%556) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%557) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%558: !exec.stop):  // pred: ^bb0
      %559 = "exec.failed"(%558) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%559) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["finite_zkl_5939bc7a1ddcd11f8e2153f23b3ed89c16434b9b99db1512543ee10e7b59b248_s0_body", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_6b3d366572d1ba53650a202f39ff52a2f298a1591829443fbeaa34ef3974f084", sym_visibility = "private"}> ({
    ^bb0(%arg275: !algebra.field<"bls12-381.fr">, %arg276: !algebra.field<"bls12-381.fr">, %arg277: !algebra.field<"bls12-381.fr">, %arg278: !algebra.field<"bls12-381.fr">):
      %550 = "algebra.field_add"(%arg277, %arg278) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %551 = "algebra.field_multiply"(%arg275, %550) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %552 = "algebra.field_multiply"(%arg276, %arg277) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %553 = "algebra.field_multiply"(%552, %arg278) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %554 = "algebra.field_add"(%551, %553) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%554) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_d1f2756b99b17aad26e4b85a966eec4c9419609618b22e3ee7f8a3349cb1e33b", sym_visibility = "private"}> ({
    ^bb0(%arg269: !runtime.scope, %arg270: !data.field_vector<"bls12-381.fr">, %arg271: !data.field_vector<"bls12-381.fr">, %arg272: !data.field_vector<"bls12-381.fr">, %arg273: !data.field_vector<"bls12-381.fr">, %arg274: ui64):
      %531 = "func.call"(%arg269, %arg274) <{callee = @s3h676b7212h706f7765725f6f665f74776f}> {runtime.site = "s0"} : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%531)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%532: ui64):  // pred: ^bb0
      %533 = "exec.apply"(%arg269, %arg272) <{binding = @zkl_binding_2, parameters = [], site = "s2"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%533)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%534: !exec.stop):  // 8 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb8
      %535 = "exec.failed"(%534) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "func.return"(%535) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%536: ui64):  // pred: ^bb1
      %537 = "exec.apply"(%arg269, %536, %arg274) <{binding = @zkl_binding_7, parameters = [], site = "s3"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%537)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%538: ui64):  // pred: ^bb3
      %539 = "exec.apply"(%arg269, %538, %arg274) <{binding = @zkl_binding_7, parameters = [], site = "s4"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%539)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%540: ui64):  // pred: ^bb4
      %541 = "func.call"(%arg269, %arg270, %540, %arg272) <{callee = @zkl_b16c159516733e0a19ce242015622636ee99dc6084d8c851dfb43c25cee57b59}> {runtime.site = "s6"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%541)[^bb6, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb6(%542: !data.field_vector<"bls12-381.fr">):  // pred: ^bb5
      %543 = "func.call"(%arg269, %arg271, %540, %arg272) <{callee = @zkl_b16c159516733e0a19ce242015622636ee99dc6084d8c851dfb43c25cee57b59}> {runtime.site = "s7"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%543)[^bb7, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb7(%544: !data.field_vector<"bls12-381.fr">):  // pred: ^bb6
      %545 = "func.call"(%arg269, %arg273, %532) <{callee = @zkl_afd97de07c9ccae9db68186ebf66098aed7daffb4b11c598d0da5cd116df8490}> {runtime.site = "s8"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%545)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%546: !data.field_vector<"bls12-381.fr">):  // pred: ^bb7
      %547 = "func.call"(%arg269, %arg273, %532) <{callee = @zkl_33f3047479634e63ecd16a0855f88ad8af019c37d677a4ffe6f5bacc63307947}> {runtime.site = "s9"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%547)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb9(%548: !data.field_vector<"bls12-381.fr">):  // pred: ^bb8
      %549 = "exec.returned"(%542, %544, %546, %548) : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "func.return"(%549) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7211h6c617965725f6761746573", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_b16c159516733e0a19ce242015622636ee99dc6084d8c851dfb43c25cee57b59", sym_visibility = "private"}> ({
    ^bb0(%arg265: !runtime.scope, %arg266: !data.field_vector<"bls12-381.fr">, %arg267: ui64, %arg268: !data.field_vector<"bls12-381.fr">):
      %516 = "exec.apply"(%arg265) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%516)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%517: ui64):  // pred: ^bb0
      %518 = "func.call"(%arg265, %arg266, %arg267, %517) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a}> {runtime.site = "s1"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%518)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb2(%519: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %520 = "exec.failed"(%519) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%520) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%521: !data.field_vector<"bls12-381.fr">, %522: ui64, %523: ui64):  // pred: ^bb1
      %524 = "func.call"(%arg265, %521, %522, %523, %arg268) <{callee = @zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be}> {runtime.site = "s2"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%524)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb4(%525: !data.field_vector<"bls12-381.fr">, %526: ui64, %527: ui64):  // pred: ^bb3
      %528 = "exec.compute"(%arg265, %525, %526, %527) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33, site = "s3"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%528)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb5(%529: !data.field_vector<"bls12-381.fr">):  // pred: ^bb4
      %530 = "exec.returned"(%529) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%530) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b728h7265737472696374", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_e1405e1bb4604e60f337203132c746492bf7c31b55302426ae19c2c021c2da1a", sym_visibility = "private"}> ({
    ^bb0(%arg263: !runtime.scope, %arg264: !algebra.field<"bls12-381.fr">):
      %509 = "exec.apply"(%arg263) <{binding = @zkl_binding_8, parameters = [], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%509)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%510: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %511 = "exec.apply"(%arg263) <{binding = @zkl_binding_14, parameters = [], site = "s1_create_0"}> : (!runtime.scope) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">)>
      "exec.dispatch"(%511)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">)>) -> ()
    ^bb2(%512: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %513 = "exec.failed"(%512) : (!exec.stop) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%513) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb3(%514: !runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">):  // pred: ^bb1
      %515 = "exec.returned"(%514, %510, %arg264) : (!runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%515) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b727h70656e64696e67", []]} : () -> ()
    "protocol.func"() <{contracts = [["input", "shape", [@zkl_30326558223483c2b755cae1fef2fb9e26e5ee8894b87d6977fe6482997b20fd, [["input", 0, "role00000000"], ["input", 1, "role00000000"], ["input", 2, "role00000000"], ["input", 3, "role00000000"]]], unit, unit], ["continuation", "gate_sum", [@zkl_e276fa0fd61d1145b2034d7e5681d41484daeb4a120f83771eba638587b04670, [["input", 0, "role00000000"], ["input", 1, "role00000000"], ["input", 2, "role00000000"], ["input", 3, "role00000000"], ["input", 5, "role00000001"], ["input", 6, "role00000001"]]], [@zkl_e276fa0fd61d1145b2034d7e5681d41484daeb4a120f83771eba638587b04670, [["input", 0, "role00000000"], ["input", 1, "role00000000"], ["input", 2, "role00000000"], ["input", 3, "role00000000"], ["output", 6, "role00000001"], ["output", 7, "role00000001"]]], unit]], function_type = (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), input_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"], ["role00000001"], ["role00000000", "role00000001"], ["role00000001"]], origin = ["gkr::Rounds", [["F", ["field", "bls12-381.fr"]], ["Max", ["nat", "4"]]]], output_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"], ["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba"}> ({
    ^bb0(%arg245: !data.field_vector<"bls12-381.fr">, %arg246: !data.field_vector<"bls12-381.fr">, %arg247: !data.field_vector<"bls12-381.fr">, %arg248: !data.field_vector<"bls12-381.fr">, %arg249: !runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">, %arg250: !data.field_vector<"bls12-381.fr">, %arg251: !algebra.field<"bls12-381.fr">, %arg252: ui64, %arg253: !protocol.service_ref<"random.bls12-381.fr/0">):
      %484 = "protocol.local_call"() <{callee = @zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f, role = "role00000000", site = "s1"}> : () -> !data.field_vector<"bls12-381.fr">
      %485:2 = "protocol.local_call"(%arg249, %arg250, %arg251) <{callee = @zkl_bd4f0d76e787de675c5732a4a96fc396d45486f32b3dcda5182ccc324969c825, role = "role00000001", site = "s3"}> : (!runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %486:7 = "protocol.repeat"(%arg252, %arg245, %arg246, %arg247, %arg248, %484, %485#0, %485#1, %arg253) <{carried = 7 : i64, carried_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"]], maximum = 4 : i64, roles = ["role00000000", "role00000001"], site = "s9"}> ({
      ^bb0(%arg254: ui64, %arg255: !data.field_vector<"bls12-381.fr">, %arg256: !data.field_vector<"bls12-381.fr">, %arg257: !data.field_vector<"bls12-381.fr">, %arg258: !data.field_vector<"bls12-381.fr">, %arg259: !data.field_vector<"bls12-381.fr">, %arg260: !data.field_vector<"bls12-381.fr">, %arg261: !algebra.field<"bls12-381.fr">, %arg262: !protocol.service_ref<"random.bls12-381.fr/0">):
        %488:3 = "protocol.local_call"(%arg255, %arg256, %arg257, %arg258) <{callee = @zkl_e2f65d17b480da5da0270346faa1bd036c7a5f879e30f4b2b6bac1224b05e394, role = "role00000000", site = "s10"}> : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %489 = "protocol.exchange"(%488#0) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %490 = "protocol.restrict_roles"(%489) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %491 = "protocol.exchange"(%488#1) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_1"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %492 = "protocol.restrict_roles"(%491) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %493 = "protocol.exchange"(%488#2) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_2"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %494 = "protocol.restrict_roles"(%493) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %495 = "algebra.field_add"(%490, %490) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %496 = "algebra.field_add"(%495, %492) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %497 = "algebra.field_add"(%496, %494) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %498 = "algebra.field_equal"(%arg261, %497) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
        "protocol.guard"(%498) <{owner = "role00000001", site = "s21"}> : (i1) -> ()
        %499 = "protocol.query"(%arg262) <{method = "draw", owner = "role00000001", site = "label_6368616c6c656e6765"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
        %500 = "protocol.exchange"(%499) <{receiver = "role00000000", sender = "role00000001", site = "label_64656c6976657279_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %501 = "protocol.restrict_roles"(%500) <{roles = ["role00000000"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %502:4 = "protocol.local_call"(%arg255, %arg256, %arg257, %arg258, %501) <{callee = @zkl_36caebca415236dd6aac1763c9a581b89c25a00e62432b484ec92ae08e6a0099, role = "role00000000", site = "s26"}> : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)
        %503 = "protocol.local_call"(%arg259, %501) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000000", site = "s28"}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !data.field_vector<"bls12-381.fr">
        %504 = "protocol.local_call"(%arg260, %499) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000001", site = "s30"}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !data.field_vector<"bls12-381.fr">
        %505 = "algebra.field_multiply"(%499, %494) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %506 = "algebra.field_add"(%492, %505) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %507 = "algebra.field_multiply"(%499, %506) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %508 = "algebra.field_add"(%490, %507) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        "protocol.yield"(%502#0, %502#1, %502#2, %502#3, %503, %504, %508) : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
      }) : (ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %487:3 = "protocol.local_call"(%486#5, %486#6) <{callee = @zkl_bcddf8825098d44ae9ce732a7b45754c16637e2a47a4c9f29ef9a21612daeaa3, role = "role00000001", site = "s42"}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      "protocol.return"(%486#4, %486#0, %486#1, %486#2, %486#3, %487#0, %487#1, %487#2) : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> i1, sym_name = "zkf_029bdd6bcc5b1485783f1674f8c6e15543fd2d268649f211eab729158162c828", sym_visibility = "private"}> ({
    ^bb0(%arg241: !data.field_vector<"bls12-381.fr">, %arg242: !data.field_vector<"bls12-381.fr">, %arg243: !data.field_vector<"bls12-381.fr">, %arg244: !data.field_vector<"bls12-381.fr">):
      %473 = "data.dim"(%arg241) <{axis = 0 : i64}> : (!data.field_vector<"bls12-381.fr">) -> ui64
      %474 = "data.dim"(%arg242) <{axis = 0 : i64}> : (!data.field_vector<"bls12-381.fr">) -> ui64
      %475 = "data.index_equal"(%473, %474) : (ui64, ui64) -> i1
      %476 = "data.dim"(%arg241) <{axis = 0 : i64}> : (!data.field_vector<"bls12-381.fr">) -> ui64
      %477 = "data.dim"(%arg243) <{axis = 0 : i64}> : (!data.field_vector<"bls12-381.fr">) -> ui64
      %478 = "data.index_equal"(%476, %477) : (ui64, ui64) -> i1
      %479 = "arith.andi"(%475, %478) : (i1, i1) -> i1
      %480 = "data.dim"(%arg241) <{axis = 0 : i64}> : (!data.field_vector<"bls12-381.fr">) -> ui64
      %481 = "data.dim"(%arg244) <{axis = 0 : i64}> : (!data.field_vector<"bls12-381.fr">) -> ui64
      %482 = "data.index_equal"(%480, %481) : (ui64, ui64) -> i1
      %483 = "arith.andi"(%479, %482) : (i1, i1) -> i1
      "func.return"(%483) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_bd4f0d76e787de675c5732a4a96fc396d45486f32b3dcda5182ccc324969c825", sym_visibility = "private"}> ({
    ^bb0(%arg237: !runtime.scope, %arg238: !runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">, %arg239: !data.field_vector<"bls12-381.fr">, %arg240: !algebra.field<"bls12-381.fr">):
      %469 = "exec.apply"(%arg237, %arg238) <{binding = @zkl_binding_15, parameters = [], site = "s0_unpack_0"}> : (!runtime.scope, !runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">) -> !exec.outcome<>
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
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_bcddf8825098d44ae9ce732a7b45754c16637e2a47a4c9f29ef9a21612daeaa3", sym_visibility = "private"}> ({
    ^bb0(%arg173: !runtime.scope, %arg174: !data.field_vector<"bls12-381.fr">, %arg175: !algebra.field<"bls12-381.fr">):
      %369 = "exec.apply"(%arg173) <{binding = @zkl_binding_14, parameters = [], site = "s0_create_0"}> : (!runtime.scope) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">)>
      "exec.dispatch"(%369)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">)>) -> ()
    ^bb1(%370: !runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">):  // pred: ^bb0
      %371 = "exec.returned"(%370, %arg174, %arg175) : (!runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%371) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%372: !exec.stop):  // pred: ^bb0
      %373 = "exec.failed"(%372) : (!exec.stop) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%373) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_02dc0a0626e9e1dc01e0d6cecf37170e46db9f35a9a2c9f38748ede75a447134">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
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
      %303 = "func.call"(%arg162, %302, %arg166, %arg163) <{callee = @zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35}> {runtime.site = "s5"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
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
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35", sym_visibility = "private"}> ({
    ^bb0(%arg128: !runtime.scope, %arg129: !data.field_vector<"bls12-381.fr">, %arg130: ui64, %arg131: !data.field_vector<"bls12-381.fr">):
      %235 = "exec.fold"(%arg128, %arg131, %arg129, %arg130) <{domain = @finite_zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35_s0_domain, site = "s0", step = @finite_zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35_s0_body}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%235)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%236: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %237 = "exec.returned"(%236) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%237) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%238: !exec.stop):  // pred: ^bb0
      %239 = "exec.failed"(%238) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%239) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg127: !data.field_vector<"bls12-381.fr">):
      %234 = "data.domain_elements"(%arg127) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%234) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "finite_zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg122: !runtime.scope, %arg123: !data.field_vector<"bls12-381.fr">, %arg124: !algebra.field<"bls12-381.fr">, %arg125: !data.field_vector<"bls12-381.fr">, %arg126: ui64):
      %229 = "func.call"(%arg122, %arg123, %arg124, %arg126) <{callee = @zkl_f9bc3972b3acce79409bfe72125c3b04de4dbb81a13d1dfbc918146c1354315c}> {runtime.site = "body"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%229)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%230: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %231 = "exec.returned"(%230) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%231) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%232: !exec.stop):  // pred: ^bb0
      %233 = "exec.failed"(%232) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%233) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["finite_zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35_s0_body", []]} : () -> ()
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
      %225 = "func.call"(%arg119, %220, %224, %arg121, %arg120) <{callee = @zkl_4d05c370830a894df2470c3859782e53b3322378b124acf8f383759935b54a45}> {runtime.site = "s5"} : (!runtime.scope, !algebra.field<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
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
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>, no_inline, sym_name = "zkl_4d05c370830a894df2470c3859782e53b3322378b124acf8f383759935b54a45", sym_visibility = "private"}> ({
    ^bb0(%arg103: !runtime.scope, %arg104: !algebra.field<"bls12-381.fr">, %arg105: ui64, %arg106: ui64, %arg107: !data.field_vector<"bls12-381.fr">):
      %185 = "exec.fold"(%arg103, %arg107, %arg104, %arg105, %arg106) <{domain = @finite_zkl_4d05c370830a894df2470c3859782e53b3322378b124acf8f383759935b54a45_s0_domain, site = "s0", step = @finite_zkl_4d05c370830a894df2470c3859782e53b3322378b124acf8f383759935b54a45_s0_body}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
      "exec.dispatch"(%185)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb1(%186: !algebra.field<"bls12-381.fr">, %187: ui64):  // pred: ^bb0
      %188 = "exec.returned"(%186, %187) : (!algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%188) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb2(%189: !exec.stop):  // pred: ^bb0
      %190 = "exec.failed"(%189) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%190) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_4d05c370830a894df2470c3859782e53b3322378b124acf8f383759935b54a45_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg102: !data.field_vector<"bls12-381.fr">):
      %184 = "data.domain_elements"(%arg102) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%184) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, ui64, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>, no_inline, sym_name = "finite_zkl_4d05c370830a894df2470c3859782e53b3322378b124acf8f383759935b54a45_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg96: !runtime.scope, %arg97: !algebra.field<"bls12-381.fr">, %arg98: ui64, %arg99: !algebra.field<"bls12-381.fr">, %arg100: !data.field_vector<"bls12-381.fr">, %arg101: ui64):
      %178 = "func.call"(%arg96, %arg97, %arg98, %arg99, %arg101) <{callee = @zkl_09043a1369ab6c082f8534fc9d21f34f77067e68b9a4c2a907a132342ff59811}> {runtime.site = "body"} : (!runtime.scope, !algebra.field<"bls12-381.fr">, ui64, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
      "exec.dispatch"(%178)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb1(%179: !algebra.field<"bls12-381.fr">, %180: ui64):  // pred: ^bb0
      %181 = "exec.returned"(%179, %180) : (!algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%181) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb2(%182: !exec.stop):  // pred: ^bb0
      %183 = "exec.failed"(%182) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%183) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, ui64)>) -> ()
    }) {runtime.origin = ["finite_zkl_4d05c370830a894df2470c3859782e53b3322378b124acf8f383759935b54a45_s0_body", []]} : () -> ()
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
      %170 = "func.call"(%arg88, %163, %167, %169, %arg90, %arg89) <{callee = @zkl_b09f44c87195c8e3d60f4dede007ee713df6eb6126ac95620f16b0ca8ac2c403}> {runtime.site = "s6"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
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
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>, no_inline, sym_name = "zkl_b09f44c87195c8e3d60f4dede007ee713df6eb6126ac95620f16b0ca8ac2c403", sym_visibility = "private"}> ({
    ^bb0(%arg72: !runtime.scope, %arg73: !data.field_vector<"bls12-381.fr">, %arg74: !algebra.field<"bls12-381.fr">, %arg75: ui64, %arg76: ui64, %arg77: !data.field_vector<"bls12-381.fr">):
      %117 = "exec.fold"(%arg72, %arg77, %arg73, %arg74, %arg75, %arg76) <{domain = @finite_zkl_b09f44c87195c8e3d60f4dede007ee713df6eb6126ac95620f16b0ca8ac2c403_s0_domain, site = "s0", step = @finite_zkl_b09f44c87195c8e3d60f4dede007ee713df6eb6126ac95620f16b0ca8ac2c403_s0_body}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
      "exec.dispatch"(%117)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb1(%118: !data.field_vector<"bls12-381.fr">, %119: !algebra.field<"bls12-381.fr">, %120: ui64):  // pred: ^bb0
      %121 = "exec.returned"(%118, %119, %120) : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%121) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb2(%122: !exec.stop):  // pred: ^bb0
      %123 = "exec.failed"(%122) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%123) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_b09f44c87195c8e3d60f4dede007ee713df6eb6126ac95620f16b0ca8ac2c403_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg71: !data.field_vector<"bls12-381.fr">):
      %116 = "data.domain_elements"(%arg71) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%116) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>, no_inline, sym_name = "finite_zkl_b09f44c87195c8e3d60f4dede007ee713df6eb6126ac95620f16b0ca8ac2c403_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg64: !runtime.scope, %arg65: !data.field_vector<"bls12-381.fr">, %arg66: !algebra.field<"bls12-381.fr">, %arg67: ui64, %arg68: !algebra.field<"bls12-381.fr">, %arg69: !data.field_vector<"bls12-381.fr">, %arg70: ui64):
      %109 = "func.call"(%arg64, %arg65, %arg66, %arg67, %arg68, %arg70) <{callee = @zkl_abd6f98141af14ddf8b9152129fb3a9fb361b5735ade780e8d1c876d68deb283}> {runtime.site = "body"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
      "exec.dispatch"(%109)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb1(%110: !data.field_vector<"bls12-381.fr">, %111: !algebra.field<"bls12-381.fr">, %112: ui64):  // pred: ^bb0
      %113 = "exec.returned"(%110, %111, %112) : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%113) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>) -> ()
    ^bb2(%114: !exec.stop):  // pred: ^bb0
      %115 = "exec.failed"(%114) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>
      "func.return"(%115) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64)>) -> ()
    }) {runtime.origin = ["finite_zkl_b09f44c87195c8e3d60f4dede007ee713df6eb6126ac95620f16b0ca8ac2c403_s0_body", []]} : () -> ()
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
      %48 = "func.call"(%arg45, %46, %47, %arg47, %arg46) <{callee = @zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d}> {runtime.site = "s2"} : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
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
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d", sym_visibility = "private"}> ({
    ^bb0(%arg31: !runtime.scope, %arg32: !algebra.field<"bls12-381.fr">, %arg33: !algebra.field<"bls12-381.fr">, %arg34: !algebra.field<"bls12-381.fr">, %arg35: !data.field_vector<"bls12-381.fr">):
      %28 = "exec.fold"(%arg31, %arg35, %arg32, %arg33, %arg34) <{domain = @finite_zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d_s0_domain, site = "s0", step = @finite_zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d_s0_body}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%28)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%29: !algebra.field<"bls12-381.fr">, %30: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %31 = "exec.returned"(%29, %30) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%31) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%32: !exec.stop):  // pred: ^bb0
      %33 = "exec.failed"(%32) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%33) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg30: !data.field_vector<"bls12-381.fr">):
      %27 = "data.domain_elements"(%arg30) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%27) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "finite_zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg24: !runtime.scope, %arg25: !algebra.field<"bls12-381.fr">, %arg26: !algebra.field<"bls12-381.fr">, %arg27: !algebra.field<"bls12-381.fr">, %arg28: !data.field_vector<"bls12-381.fr">, %arg29: !algebra.field<"bls12-381.fr">):
      %21 = "func.call"(%arg24, %arg25, %arg26, %arg27, %arg29) <{callee = @zkl_bcbdb252ffc9abd0563757a6a45f0dccb9a7c345ecbfb58b787c5137455bd42e}> {runtime.site = "body"} : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%21)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%22: !algebra.field<"bls12-381.fr">, %23: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %24 = "exec.returned"(%22, %23) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%24) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%25: !exec.stop):  // pred: ^bb0
      %26 = "exec.failed"(%25) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%26) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["finite_zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d_s0_body", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_744f32fd2e4e542d6467fe3f764e183881171708947eb2bd852cea6f32a0407e", sym_visibility = "private"}> ({
    ^bb0(%arg18: !runtime.scope, %arg19: !runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, %arg20: !data.field_vector<"bls12-381.fr">, %arg21: !algebra.field<"bls12-381.fr">, %arg22: !data.field_vector<"bls12-381.fr">, %arg23: !algebra.field<"bls12-381.fr">):
      %16 = "exec.apply"(%arg18, %arg19) <{binding = @zkl_binding_16, parameters = [], site = "s1_repack_0"}> : (!runtime.scope, !runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">)>
      "exec.dispatch"(%16)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">)>) -> ()
    ^bb1(%17: !runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">):  // pred: ^bb0
      %18 = "exec.returned"(%17, %arg22, %arg23) : (!runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%18) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%19: !exec.stop):  // pred: ^bb0
      %20 = "exec.failed"(%19) : (!exec.stop) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%20) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h676b7213h616476616e63655f6c61796572", []]} : () -> ()
    "protocol.func"() <{contracts = [["target", "input_value", [@zkl_cb10975ebbde52f87ba3f031d71fbab61676c0ccc3b05423f90b82c03f36e3ff, [["input", 0, "role00000000"], ["input", 2, "role00000000"], ["input", 3, "role00000000"]]], unit, ["output", 0, "role00000000"]]], function_type = (!data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, input_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"]], origin = ["gkr::Input", [["F", ["field", "bls12-381.fr"]]]], output_roles = [["role00000000"]], roles = ["role00000000"], sym_name = "zkl_9719be65739d901a935dbaa0f3f8323a785562f7eee1e60cc8c8c9676f8fdb55"}> ({
    ^bb0(%arg14: !data.field_vector<"bls12-381.fr">, %arg15: !runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, %arg16: !data.field_vector<"bls12-381.fr">, %arg17: !algebra.field<"bls12-381.fr">):
      %15 = "protocol.local_call"(%arg14, %arg15, %arg16, %arg17) <{callee = @zkl_d74cb9bd9ed782590145b66a573f8104fca0e842c109c7d034296431308fc6b9, role = "role00000000", site = "s0"}> : (!data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
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
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_d74cb9bd9ed782590145b66a573f8104fca0e842c109c7d034296431308fc6b9", sym_visibility = "private"}> ({
    ^bb0(%arg0: !runtime.scope, %arg1: !data.field_vector<"bls12-381.fr">, %arg2: !runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">, %arg3: !data.field_vector<"bls12-381.fr">, %arg4: !algebra.field<"bls12-381.fr">):
      %0 = "exec.apply"(%arg0, %arg2) <{binding = @zkl_binding_17, parameters = [], site = "s0_unpack_0"}> : (!runtime.scope, !runtime.capability<resource_unit, "zkl_resource_84874222ecf7f94a29e4d960d17e95c115b500b340a8129508b38a0c8d153eea">) -> !exec.outcome<>
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
    "relation.declare"() <{formula = @zkf_029bdd6bcc5b1485783f1674f8c6e15543fd2d268649f211eab729158162c828, key = "zkl_30326558223483c2b755cae1fef2fb9e26e5ee8894b87d6977fe6482997b20fd", kind = "zkc.language.formula/0", purposes = ["parameter", "parameter", "parameter", "parameter"], revision = "648c1322c48f21cd4982d77516ed5ed4b9c0b13e8cf5e8464f811c1223672a5f", signature = (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> i1, static_arguments = [], sym_name = "zkl_30326558223483c2b755cae1fef2fb9e26e5ee8894b87d6977fe6482997b20fd"}> : () -> ()
    "relation.declare"() <{key = "residual", kind = "gkr.rounds/0", purposes = ["parameter", "parameter", "parameter", "parameter", "statement", "statement"], revision = "0", signature = (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, static_arguments = [["field", "bls12-381.fr"]], sym_name = "zkl_e276fa0fd61d1145b2034d7e5681d41484daeb4a120f83771eba638587b04670"}> : () -> ()
    "relation.declare"() <{formula = @zkf_d1b83b15191b85497fc6003ecffb377b2ff71a9228a1114a266874f0ba672708, key = "zkl_cb10975ebbde52f87ba3f031d71fbab61676c0ccc3b05423f90b82c03f36e3ff", kind = "zkc.language.formula/0", purposes = ["parameter", "statement", "statement"], revision = "728df64dc19da9e2da6621a36cc4b84667459e235b2a4ce316858c1049abe46a", signature = (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, static_arguments = [], sym_name = "zkl_cb10975ebbde52f87ba3f031d71fbab61676c0ccc3b05423f90b82c03f36e3ff"}> : () -> ()
  }) : () -> ()
}) : () -> ()

