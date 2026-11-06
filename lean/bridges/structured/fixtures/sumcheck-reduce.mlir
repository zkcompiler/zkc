"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>, source_declarations = [[[["nominal", "record", "sumcheck::Pending", [["field", "bls12-381.fr"]]], "linear", false, [["point", ["builtin", "vector", [["field", "bls12-381.fr"]]], unit], ["value", ["field", "bls12-381.fr"], unit]], [], "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6"], [["nominal", "record", "zkc::multilinear::Table", [["field", "bls12-381.fr"]]], "ordinary", false, [["entries", ["builtin", "vector", [["field", "bls12-381.fr"]]], unit], ["dimensions", ["index"], unit], ["columns", ["index"], unit]], [], unit]], [["zkl_cf3586ba980b617860654dacf2506dd277a78d1dcf5b84bcc6376225e7fe4f45", [["values", ["builtin", "vector", [["field", "bls12-381.fr"]]], ["role00000000"], 0 : ui64, 1 : ui64, ["data", ["role00000000"]]], ["variables", ["index"], ["role00000000"], 1 : ui64, 1 : ui64, ["data", ["role00000000"]]], ["claim", ["field", "bls12-381.fr"], ["role00000001"], 2 : ui64, 1 : ui64, ["data", ["role00000001"]]], ["rounds", ["index"], ["role00000000", "role00000001"], 3 : ui64, 1 : ui64, ["data", ["role00000000", "role00000001"]]]], [["point", ["builtin", "vector", [["field", "bls12-381.fr"]]], ["role00000000"], 0 : ui64, 1 : ui64, ["data", ["role00000000"]]], ["residual", ["builtin", "vector", [["field", "bls12-381.fr"]]], ["role00000000"], 1 : ui64, 1 : ui64, ["data", ["role00000000"]]], ["evaluation", ["nominal", "record", "sumcheck::Pending", [["field", "bls12-381.fr"]]], ["role00000001"], 2 : ui64, 3 : ui64, ["data", ["role00000001"]]]]], ["zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", [["values", ["nominal", "record", "zkc::multilinear::Table", [["field", "bls12-381.fr"]]], ["role00000000"], 0 : ui64, 3 : ui64, ["data", ["role00000000"]]], ["claim", ["nominal", "record", "sumcheck::Pending", [["field", "bls12-381.fr"]]], ["role00000001"], 3 : ui64, 3 : ui64, ["data", ["role00000001"]]], ["rounds", ["index"], ["role00000000", "role00000001"], 6 : ui64, 1 : ui64, ["data", ["role00000000", "role00000001"]]]], [["point", ["builtin", "vector", [["field", "bls12-381.fr"]]], ["role00000000"], 0 : ui64, 1 : ui64, ["data", ["role00000000"]]], ["residual", ["nominal", "record", "zkc::multilinear::Table", [["field", "bls12-381.fr"]]], ["role00000000"], 1 : ui64, 3 : ui64, ["data", ["role00000000"]]], ["evaluation", ["nominal", "record", "sumcheck::Pending", [["field", "bls12-381.fr"]]], ["role00000001"], 4 : ui64, 3 : ui64, ["data", ["role00000001"]]]]]], [["sumcheck::Pending", "7755041130d6ceb96e647d78ac25f7e67d45df1d27871cb103399d282c063f61"], ["zkc::multilinear::Table", "8aa28c4604470c28369b6893e2527323f693924f66cd54f1701edee86bd6bf62"]]]}> ({
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.append", function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, implementation = "", sym_name = "zkl_binding_13"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.sub", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_12"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.split", function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>, implementation = "", sym_name = "zkl_binding_11"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.sum", function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, implementation = "", sym_name = "zkl_binding_10"}> : () -> ()
    "runtime.binding"() <{arguments = ["zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6"], contract = "resource_unit.consume", function_type = (!runtime.scope, !runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">) -> !exec.outcome<>, implementation = "", sym_name = "zkl_binding_9"}> : () -> ()
    "runtime.binding"() <{arguments = ["zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6"], contract = "resource_unit.create", function_type = (!runtime.scope) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">)>, implementation = "", sym_name = "zkl_binding_8"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.empty", function_type = (!runtime.scope) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, implementation = "", sym_name = "zkl_binding_7"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.mul", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_6"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.less", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>, implementation = "", sym_name = "zkl_binding_5"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.div", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_4"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.equal", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>, implementation = "", sym_name = "zkl_binding_3"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.mod", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_2"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.length", function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_1"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.constant", function_type = (!runtime.scope) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_0"}> : () -> ()
    "protocol.func"() <{contracts = [], function_type = (!data.field_vector<"bls12-381.fr">, ui64, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), input_roles = [["role00000000"], ["role00000000"], ["role00000001"], ["role00000000", "role00000001"], ["role00000001"]], origin = ["sums::Reduction", [["F", ["field", "bls12-381.fr"]], ["Max", ["nat", "4"]]]], output_roles = [["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"], ["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_cf3586ba980b617860654dacf2506dd277a78d1dcf5b84bcc6376225e7fe4f45"}> ({
    ^bb0(%arg123: !data.field_vector<"bls12-381.fr">, %arg124: ui64, %arg125: !algebra.field<"bls12-381.fr">, %arg126: ui64, %arg127: !protocol.service_ref<"random.bls12-381.fr/0">):
      %322 = "data.index"() <{value = 1 : ui64}> : () -> ui64
      %323:3 = "protocol.local_call"(%arg123, %arg124, %322) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a, role = "role00000000", site = "s1"}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> (!data.field_vector<"bls12-381.fr">, ui64, ui64)
      %324:3 = "protocol.local_call"(%arg125) <{callee = @zkl_c0a3a2b8b5f989e0e9c138a171631d20dc8bd296769b6ee7636d2d79a8518ba0, role = "role00000001", site = "s3"}> : (!algebra.field<"bls12-381.fr">) -> (!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %325:7 = "protocol.apply"(%323#0, %323#1, %323#2, %324#0, %324#1, %324#2, %arg126, %arg127) <{callee = @zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d, roles = ["role00000000", "role00000001"], site = "s5"}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64, !runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, ui64, !runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %326 = "func.call"(%325#1, %325#2, %325#3) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !data.field_vector<"bls12-381.fr">
      "protocol.return"(%325#0, %326, %325#4, %325#5, %325#6) : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", sym_visibility = "private"}> ({
    ^bb0(%arg119: !runtime.scope, %arg120: !data.field_vector<"bls12-381.fr">, %arg121: ui64, %arg122: ui64):
      %303 = "func.call"(%arg119, %arg120, %arg121, %arg122) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655}> {runtime.site = "s0"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%303)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%304: i1):  // pred: ^bb0
      %305 = "exec.test"(%arg119, %304) <{site = "s1"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%305)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%306: !exec.stop):  // 8 preds: ^bb0, ^bb1, ^bb4, ^bb5, ^bb7, ^bb8, ^bb10, ^bb11
      %307 = "exec.failed"(%306) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%307) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb3(%308: i1):  // pred: ^bb1
      "cf.cond_br"(%308)[^bb4, ^bb5] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb4:  // pred: ^bb3
      %309 = "runtime.enter_scope"(%arg119) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%309)[^bb7, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb5:  // pred: ^bb3
      %310 = "runtime.enter_scope"(%arg119) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%310)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // 2 preds: ^bb9, ^bb12
      %311 = "exec.returned"(%arg120, %arg121, %arg122) : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%311) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb7(%312: !runtime.scope):  // pred: ^bb4
      %313 = "func.call"(%312) <{callee = @zkl_control_0}> : (!runtime.scope) -> !exec.outcome<>
      %314 = "runtime.exit_scope"(%312, %313) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%314)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb8(%315: !runtime.transfer<>):  // pred: ^bb7
      %316 = "runtime.accept_transfer"(%arg119, %315) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%316)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb9:  // pred: ^bb8
      "cf.br"()[^bb6] : () -> ()
    ^bb10(%317: !runtime.scope):  // pred: ^bb5
      %318 = "func.call"(%317) <{callee = @zkl_control_1}> : (!runtime.scope) -> !exec.outcome<>
      %319 = "runtime.exit_scope"(%317, %318) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%319)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb11(%320: !runtime.transfer<>):  // pred: ^bb10
      %321 = "runtime.accept_transfer"(%arg119, %320) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%321)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb12:  // pred: ^bb11
      "cf.br"()[^bb6] : () -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561725h7461626c65", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_0", sym_visibility = "private"}> ({
    ^bb0(%arg118: !runtime.scope):
      %302 = "exec.complete"(%arg118) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%302) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_1", sym_visibility = "private"}> ({
    ^bb0(%arg117: !runtime.scope):
      %299 = "exec.reject"(%arg117) <{reason = "reject", site = "s1_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%299)[^bb1] : (!exec.stop) -> ()
    ^bb1(%300: !exec.stop):  // pred: ^bb0
      %301 = "exec.failed"(%300) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%301) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", sym_visibility = "private"}> ({
    ^bb0(%arg113: !runtime.scope, %arg114: !data.field_vector<"bls12-381.fr">, %arg115: ui64, %arg116: ui64):
      %241 = "exec.apply"(%arg113) <{binding = @zkl_binding_0, parameters = [0 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%241)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%242: ui64):  // pred: ^bb0
      %243 = "func.call"(%arg113, %242, %arg116) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s1"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%243)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%244: !exec.stop):  // 23 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12, ^bb15, ^bb16, ^bb17, ^bb18, ^bb19, ^bb21, ^bb22, ^bb25, ^bb26, ^bb28, ^bb29, ^bb31, ^bb32
      %245 = "exec.failed"(%244) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%245) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%246: i1):  // pred: ^bb1
      %247 = "exec.test"(%arg113, %246) <{site = "s3"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%247)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb4(%248: i1):  // pred: ^bb3
      "cf.cond_br"(%248)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %249 = "runtime.enter_scope"(%arg113, %arg115) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "then", site = "s3"}> : (!runtime.scope, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%249)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %250 = "runtime.enter_scope"(%arg113, %arg115) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "else", site = "s3"}> : (!runtime.scope, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%250)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7(%251: i1):  // 2 preds: ^bb10, ^bb13
      %252 = "exec.test"(%arg113, %251) <{site = "s11"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%252)[^bb14, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb8(%253: !runtime.scope):  // pred: ^bb5
      %254 = "func.call"(%253, %arg115) <{callee = @zkl_control_2}> : (!runtime.scope, ui64) -> !exec.outcome<(i1)>
      %255 = "runtime.exit_scope"(%253, %254) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%255)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb9(%256: !runtime.transfer<(i1)>):  // pred: ^bb8
      %257 = "runtime.accept_transfer"(%arg113, %256) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%257)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb10(%258: i1):  // pred: ^bb9
      "cf.br"(%258)[^bb7] : (i1) -> ()
    ^bb11(%259: !runtime.scope):  // pred: ^bb6
      %260 = "func.call"(%259, %arg115) <{callee = @zkl_control_3}> : (!runtime.scope, ui64) -> !exec.outcome<(i1)>
      %261 = "runtime.exit_scope"(%259, %260) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%261)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb12(%262: !runtime.transfer<(i1)>):  // pred: ^bb11
      %263 = "runtime.accept_transfer"(%arg113, %262) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%263)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb13(%264: i1):  // pred: ^bb12
      "cf.br"(%264)[^bb7] : (i1) -> ()
    ^bb14(%265: i1):  // pred: ^bb7
      "cf.cond_br"(%265)[^bb15, ^bb16] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb15:  // pred: ^bb14
      %266 = "runtime.enter_scope"(%arg113, %arg114, %arg116) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "then", site = "s11"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%266)[^bb18, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb16:  // pred: ^bb14
      %267 = "runtime.enter_scope"(%arg113, %arg114, %arg116) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "else", site = "s11"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%267)[^bb21, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb17(%268: i1):  // 2 preds: ^bb20, ^bb23
      %269 = "exec.test"(%arg113, %268) <{site = "s22"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%269)[^bb24, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb18(%270: !runtime.scope):  // pred: ^bb15
      %271 = "func.call"(%270, %arg114, %arg116) <{callee = @zkl_control_4}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>
      %272 = "runtime.exit_scope"(%270, %271) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%272)[^bb19, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb19(%273: !runtime.transfer<(i1)>):  // pred: ^bb18
      %274 = "runtime.accept_transfer"(%arg113, %273) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%274)[^bb20, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb20(%275: i1):  // pred: ^bb19
      "cf.br"(%275)[^bb17] : (i1) -> ()
    ^bb21(%276: !runtime.scope):  // pred: ^bb16
      %277 = "func.call"(%276, %arg114, %arg116) <{callee = @zkl_control_5}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>
      %278 = "runtime.exit_scope"(%276, %277) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%278)[^bb22, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb22(%279: !runtime.transfer<(i1)>):  // pred: ^bb21
      %280 = "runtime.accept_transfer"(%arg113, %279) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%280)[^bb23, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb23(%281: i1):  // pred: ^bb22
      "cf.br"(%281)[^bb17] : (i1) -> ()
    ^bb24(%282: i1):  // pred: ^bb17
      "cf.cond_br"(%282)[^bb25, ^bb26] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb25:  // pred: ^bb24
      %283 = "runtime.enter_scope"(%arg113, %arg114, %arg115, %arg116) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "then", site = "s22"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%283)[^bb28, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb26:  // pred: ^bb24
      %284 = "runtime.enter_scope"(%arg113, %arg114, %arg115, %arg116) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "else", site = "s22"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%284)[^bb31, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb27(%285: i1):  // 2 preds: ^bb30, ^bb33
      %286 = "exec.returned"(%285) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%286) : (!exec.outcome<(i1)>) -> ()
    ^bb28(%287: !runtime.scope):  // pred: ^bb25
      %288 = "func.call"(%287, %arg114, %arg115, %arg116) <{callee = @zkl_control_6}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      %289 = "runtime.exit_scope"(%287, %288) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%289)[^bb29, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb29(%290: !runtime.transfer<(i1)>):  // pred: ^bb28
      %291 = "runtime.accept_transfer"(%arg113, %290) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%291)[^bb30, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb30(%292: i1):  // pred: ^bb29
      "cf.br"(%292)[^bb27] : (i1) -> ()
    ^bb31(%293: !runtime.scope):  // pred: ^bb26
      %294 = "func.call"(%293, %arg114, %arg115, %arg116) <{callee = @zkl_control_7}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      %295 = "runtime.exit_scope"(%293, %294) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%295)[^bb32, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb32(%296: !runtime.transfer<(i1)>):  // pred: ^bb31
      %297 = "runtime.accept_transfer"(%arg113, %296) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%297)[^bb33, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb33(%298: i1):  // pred: ^bb32
      "cf.br"(%298)[^bb27] : (i1) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_2", sym_visibility = "private"}> ({
    ^bb0(%arg111: !runtime.scope, %arg112: ui64):
      %234 = "exec.apply"(%arg111) <{binding = @zkl_binding_0, parameters = [64 : ui64], site = "s4"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%234)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%235: ui64):  // pred: ^bb0
      %236 = "func.call"(%arg111, %arg112, %235) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s5"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%236)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%237: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %238 = "exec.failed"(%237) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%238) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%239: i1):  // pred: ^bb1
      %240 = "exec.complete"(%arg111, %239) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%240) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_3", sym_visibility = "private"}> ({
    ^bb0(%arg109: !runtime.scope, %arg110: ui64):
      %229 = "exec.boolean"(%arg109) <{site = "s7", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%229)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%230: i1):  // pred: ^bb0
      %231 = "exec.complete"(%arg109, %230) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%231) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%232: !exec.stop):  // pred: ^bb0
      %233 = "exec.failed"(%232) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%233) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_4", sym_visibility = "private"}> ({
    ^bb0(%arg106: !runtime.scope, %arg107: !data.field_vector<"bls12-381.fr">, %arg108: ui64):
      %218 = "exec.apply"(%arg106, %arg107) <{binding = @zkl_binding_1, parameters = [], site = "s12"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%218)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%219: ui64):  // pred: ^bb0
      %220 = "exec.apply"(%arg106, %219, %arg108) <{binding = @zkl_binding_2, parameters = [], site = "s13"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%220)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%221: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %222 = "exec.failed"(%221) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%222) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%223: ui64):  // pred: ^bb1
      %224 = "exec.apply"(%arg106) <{binding = @zkl_binding_0, parameters = [0 : ui64], site = "s14"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%224)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%225: ui64):  // pred: ^bb3
      %226 = "exec.apply"(%arg106, %223, %225) <{binding = @zkl_binding_3, parameters = [], site = "s15"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%226)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb5(%227: i1):  // pred: ^bb4
      %228 = "exec.complete"(%arg106, %227) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%228) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_5", sym_visibility = "private"}> ({
    ^bb0(%arg103: !runtime.scope, %arg104: !data.field_vector<"bls12-381.fr">, %arg105: ui64):
      %213 = "exec.boolean"(%arg103) <{site = "s17", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%213)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%214: i1):  // pred: ^bb0
      %215 = "exec.complete"(%arg103, %214) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%215) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%216: !exec.stop):  // pred: ^bb0
      %217 = "exec.failed"(%216) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%217) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_6", sym_visibility = "private"}> ({
    ^bb0(%arg99: !runtime.scope, %arg100: !data.field_vector<"bls12-381.fr">, %arg101: ui64, %arg102: ui64):
      %202 = "exec.apply"(%arg99, %arg100) <{binding = @zkl_binding_1, parameters = [], site = "s23"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%202)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%203: ui64):  // pred: ^bb0
      %204 = "exec.apply"(%arg99, %203, %arg102) <{binding = @zkl_binding_4, parameters = [], site = "s24"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%204)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%205: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %206 = "exec.failed"(%205) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%206) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%207: ui64):  // pred: ^bb1
      %208 = "func.call"(%arg99, %arg101) <{callee = @s3h7a6b6311h6d756c74696c696e6561724h726f7773}> {runtime.site = "s25"} : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%208)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%209: ui64):  // pred: ^bb3
      %210 = "exec.apply"(%arg99, %207, %209) <{binding = @zkl_binding_3, parameters = [], site = "s26"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%210)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb5(%211: i1):  // pred: ^bb4
      %212 = "exec.complete"(%arg99, %211) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%212) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_7", sym_visibility = "private"}> ({
    ^bb0(%arg95: !runtime.scope, %arg96: !data.field_vector<"bls12-381.fr">, %arg97: ui64, %arg98: ui64):
      %197 = "exec.boolean"(%arg95) <{site = "s28", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%197)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%198: i1):  // pred: ^bb0
      %199 = "exec.complete"(%arg95, %198) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%199) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%200: !exec.stop):  // pred: ^bb0
      %201 = "exec.failed"(%200) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%201) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "s3h7a6b637h696e64696365734h6c657373", sym_visibility = "private"}> ({
    ^bb0(%arg92: !runtime.scope, %arg93: ui64, %arg94: ui64):
      %192 = "exec.apply"(%arg92, %arg93, %arg94) <{binding = @zkl_binding_5, parameters = [], site = "s0"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%192)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%193: i1):  // pred: ^bb0
      %194 = "exec.returned"(%193) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%194) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%195: !exec.stop):  // pred: ^bb0
      %196 = "exec.failed"(%195) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%196) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.origin = ["s3h7a6b637h696e64696365734h6c657373", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "s3h7a6b6311h6d756c74696c696e6561724h726f7773", sym_visibility = "private"}> ({
    ^bb0(%arg90: !runtime.scope, %arg91: ui64):
      %145 = "exec.apply"(%arg90) <{binding = @zkl_binding_0, parameters = [64 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%145)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%146: ui64):  // pred: ^bb0
      %147 = "func.call"(%arg90, %arg91, %146) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s1"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%147)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%148: !exec.stop):  // 14 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12, ^bb14, ^bb15, ^bb19, ^bb21
      %149 = "exec.failed"(%148) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%149) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%150: i1):  // pred: ^bb1
      %151 = "exec.test"(%arg90, %150) <{site = "s2"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%151)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb4(%152: i1):  // pred: ^bb3
      "cf.cond_br"(%152)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %153 = "runtime.enter_scope"(%arg90) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s2"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%153)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %154 = "runtime.enter_scope"(%arg90) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s2"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%154)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // 2 preds: ^bb10, ^bb13
      %155 = "exec.apply"(%arg90) <{binding = @zkl_binding_0, parameters = [1 : ui64], site = "s3"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%155)[^bb14, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb8(%156: !runtime.scope):  // pred: ^bb5
      %157 = "func.call"(%156) <{callee = @zkl_control_8}> : (!runtime.scope) -> !exec.outcome<>
      %158 = "runtime.exit_scope"(%156, %157) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%158)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb9(%159: !runtime.transfer<>):  // pred: ^bb8
      %160 = "runtime.accept_transfer"(%arg90, %159) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%160)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb10:  // pred: ^bb9
      "cf.br"()[^bb7] : () -> ()
    ^bb11(%161: !runtime.scope):  // pred: ^bb6
      %162 = "func.call"(%161) <{callee = @zkl_control_9}> : (!runtime.scope) -> !exec.outcome<>
      %163 = "runtime.exit_scope"(%161, %162) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%163)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb12(%164: !runtime.transfer<>):  // pred: ^bb11
      %165 = "runtime.accept_transfer"(%arg90, %164) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%165)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb13:  // pred: ^bb12
      "cf.br"()[^bb7] : () -> ()
    ^bb14(%166: ui64):  // pred: ^bb7
      %167 = "exec.apply"(%arg90) <{binding = @zkl_binding_0, parameters = [0 : ui64], site = "s5"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%167)[^bb15, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb15(%168: ui64):  // pred: ^bb14
      %169 = "exec.range"(%arg90, %168, %arg91) <{site = "s6"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%169)[^bb16, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i64, i64)>) -> ()
    ^bb16(%170: i64, %171: i64):  // pred: ^bb15
      %172 = "runtime.borrow_transfer"(%arg90, %166) : (!runtime.scope, ui64) -> !runtime.transfer<(ui64)>
      "cf.br"(%170, %172)[^bb17] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb17(%173: i64, %174: !runtime.transfer<(ui64)>):  // 2 preds: ^bb16, ^bb20
      %175 = "arith.cmpi"(%173, %171) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%175, %174)[^bb18, ^bb19] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(ui64)>) -> ()
    ^bb18:  // pred: ^bb17
      %176 = "runtime.iteration"(%arg90, %173) <{site = "s6"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%176)[^bb22, ^bb21] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb19(%177: !runtime.transfer<(ui64)>):  // pred: ^bb17
      %178 = "runtime.accept_transfer"(%arg90, %177) : (!runtime.scope, !runtime.transfer<(ui64)>) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%178)[^bb25, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb20(%179: !runtime.transfer<(ui64)>):  // pred: ^bb24
      %180 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %181 = "arith.addi"(%173, %180) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%181, %179)[^bb17] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb21(%182: !exec.stop):  // 3 preds: ^bb18, ^bb22, ^bb23
      "runtime.release_transfer"(%174) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%182)[^bb2] : (!exec.stop) -> ()
    ^bb22(%183: ui64):  // pred: ^bb18
      %184 = "runtime.transfer_values"(%174) : (!runtime.transfer<(ui64)>) -> ui64
      %185 = "runtime.enter_scope"(%arg90, %173, %183, %184) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 2>, site = "s6"}> : (!runtime.scope, i64, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%185)[^bb23, ^bb21] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb23(%186: !runtime.scope):  // pred: ^bb22
      %187 = "func.call"(%186, %183, %184) <{callee = @zkl_control_10}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      %188 = "runtime.exit_scope"(%186, %187) : (!runtime.scope, !exec.outcome<(ui64)>) -> !exec.outcome<(!runtime.transfer<(ui64)>)>
      "exec.dispatch"(%188)[^bb24, ^bb21] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(ui64)>)>) -> ()
    ^bb24(%189: !runtime.transfer<(ui64)>):  // pred: ^bb23
      "runtime.release_transfer"(%174) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%189)[^bb20] : (!runtime.transfer<(ui64)>) -> ()
    ^bb25(%190: ui64):  // pred: ^bb19
      %191 = "exec.returned"(%190) : (ui64) -> !exec.outcome<(ui64)>
      "func.return"(%191) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561724h726f7773", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_8", sym_visibility = "private"}> ({
    ^bb0(%arg89: !runtime.scope):
      %144 = "exec.complete"(%arg89) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%144) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_9", sym_visibility = "private"}> ({
    ^bb0(%arg88: !runtime.scope):
      %141 = "exec.reject"(%arg88) <{reason = "reject", site = "s2_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%141)[^bb1] : (!exec.stop) -> ()
    ^bb1(%142: !exec.stop):  // pred: ^bb0
      %143 = "exec.failed"(%142) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%143) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "zkl_control_10", sym_visibility = "private"}> ({
    ^bb0(%arg85: !runtime.scope, %arg86: ui64, %arg87: ui64):
      %134 = "exec.apply"(%arg85) <{binding = @zkl_binding_0, parameters = [2 : ui64], site = "s7"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%134)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%135: ui64):  // pred: ^bb0
      %136 = "exec.apply"(%arg85, %arg87, %135) <{binding = @zkl_binding_6, parameters = [], site = "s8"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%136)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%137: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %138 = "exec.failed"(%137) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%138) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%139: ui64):  // pred: ^bb1
      %140 = "exec.complete"(%arg85, %139) : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "func.return"(%140) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_c0a3a2b8b5f989e0e9c138a171631d20dc8bd296769b6ee7636d2d79a8518ba0", sym_visibility = "private"}> ({
    ^bb0(%arg83: !runtime.scope, %arg84: !algebra.field<"bls12-381.fr">):
      %127 = "exec.apply"(%arg83) <{binding = @zkl_binding_7, parameters = [], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%127)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%128: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %129 = "exec.apply"(%arg83) <{binding = @zkl_binding_8, parameters = [], site = "s1_create_0"}> : (!runtime.scope) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">)>
      "exec.dispatch"(%129)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">)>) -> ()
    ^bb2(%130: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %131 = "exec.failed"(%130) : (!exec.stop) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%131) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb3(%132: !runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">):  // pred: ^bb1
      %133 = "exec.returned"(%132, %128, %arg84) : (!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%133) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s8h73756d636865636b7h70656e64696e67", []]} : () -> ()
    "protocol.func"() <{contracts = [["input", "shape", [@zkl_8c866415d5a42d7cb60d6b39dd52568c20001248a901906f13a3d5d9dd8f74ac, [["input", 0, "role00000000"], ["input", 1, "role00000000"], ["input", 2, "role00000000"]]], unit, unit], ["continuation", "initial_sum", [@zkl_f03c5af270c09f9d5e832cdb0dc1d71151cebecfaaa08c6cacd997dde03860e9, [["input", 0, "role00000000"], ["input", 1, "role00000000"], ["input", 2, "role00000000"], ["input", 4, "role00000001"], ["input", 5, "role00000001"]]], [@zkl_f03c5af270c09f9d5e832cdb0dc1d71151cebecfaaa08c6cacd997dde03860e9, [["input", 0, "role00000000"], ["input", 1, "role00000000"], ["input", 2, "role00000000"], ["output", 5, "role00000001"], ["output", 6, "role00000001"]]], unit]], function_type = (!data.field_vector<"bls12-381.fr">, ui64, ui64, !runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, ui64, !runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), input_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"], ["role00000001"], ["role00000000", "role00000001"], ["role00000001"]], origin = ["sumcheck::Reduce", [["F", ["field", "bls12-381.fr"]], ["Max", ["nat", "4"]]]], output_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"], ["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d"}> ({
    ^bb0(%arg67: !data.field_vector<"bls12-381.fr">, %arg68: ui64, %arg69: ui64, %arg70: !runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, %arg71: !data.field_vector<"bls12-381.fr">, %arg72: !algebra.field<"bls12-381.fr">, %arg73: ui64, %arg74: !protocol.service_ref<"random.bls12-381.fr/0">):
      %98 = "func.call"(%arg67, %arg68, %arg69) <{callee = @zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %99 = "data.index"() <{value = 1 : ui64}> : () -> ui64
      %100 = "data.index_equal"(%98, %99) : (ui64, ui64) -> i1
      "protocol.guard"(%100) <{owner = "role00000000", site = "s3"}> : (i1) -> ()
      %101 = "func.call"(%arg67, %arg68, %arg69) <{callee = @zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %102 = "protocol.local_call"(%101, %arg73) <{callee = @s3h7a6b637h696e64696365734h6c657373, role = "role00000000", site = "s5"}> : (ui64, ui64) -> i1
      %103 = "arith.constant"() <{value = false}> : () -> i1
      %104 = "arith.cmpi"(%102, %103) <{predicate = 0 : i64}> : (i1, i1) -> i1
      "protocol.guard"(%104) <{owner = "role00000000", site = "s8"}> : (i1) -> ()
      %105 = "protocol.local_call"() <{callee = @zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f, role = "role00000000", site = "s10"}> : () -> !data.field_vector<"bls12-381.fr">
      %106:2 = "protocol.local_call"(%arg70, %arg71, %arg72) <{callee = @zkl_e8df957aab384c1d5416600c13a571512206e97abfbf6e0e9cddac5c84860d07, role = "role00000001", site = "s12"}> : (!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %107:6 = "protocol.repeat"(%arg73, %arg67, %arg68, %arg69, %105, %106#0, %106#1, %arg74) <{carried = 6 : i64, carried_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"]], maximum = 4 : i64, roles = ["role00000000", "role00000001"], site = "s18"}> ({
      ^bb0(%arg75: ui64, %arg76: !data.field_vector<"bls12-381.fr">, %arg77: ui64, %arg78: ui64, %arg79: !data.field_vector<"bls12-381.fr">, %arg80: !data.field_vector<"bls12-381.fr">, %arg81: !algebra.field<"bls12-381.fr">, %arg82: !protocol.service_ref<"random.bls12-381.fr/0">):
        %109:2 = "protocol.local_call"(%arg76, %arg77, %arg78) <{callee = @zkl_532a609cf36a935835501ca51308940142121e647ca360843a880bf231f04aa6, role = "role00000000", site = "s19"}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %110 = "protocol.exchange"(%109#0) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %111 = "protocol.restrict_roles"(%110) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %112 = "protocol.exchange"(%109#1) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_1"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %113 = "protocol.restrict_roles"(%112) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %114 = "algebra.field_add"(%111, %113) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %115 = "algebra.field_equal"(%arg81, %114) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
        "protocol.guard"(%115) <{owner = "role00000001", site = "s27"}> : (i1) -> ()
        %116 = "protocol.query"(%arg82) <{method = "draw", owner = "role00000001", site = "label_6368616c6c656e6765"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
        %117 = "protocol.exchange"(%116) <{receiver = "role00000000", sender = "role00000001", site = "label_64656c6976657279_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %118 = "protocol.restrict_roles"(%117) <{roles = ["role00000000"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %119:3 = "protocol.local_call"(%arg76, %arg77, %arg78, %118) <{callee = @zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d, role = "role00000000", site = "s32"}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> (!data.field_vector<"bls12-381.fr">, ui64, ui64)
        %120 = "protocol.local_call"(%arg79, %118) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000000", site = "s34"}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !data.field_vector<"bls12-381.fr">
        %121 = "protocol.local_call"(%arg80, %116) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000001", site = "s36"}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !data.field_vector<"bls12-381.fr">
        %122 = "algebra.constant"() <{value = #algebra.literal<<"bls12-381.fr">, 1 : ui255> : !algebra.field<"bls12-381.fr">}> : () -> !algebra.field<"bls12-381.fr">
        %123 = "algebra.field_subtract"(%122, %116) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %124 = "algebra.field_multiply"(%123, %111) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %125 = "algebra.field_multiply"(%116, %113) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %126 = "algebra.field_add"(%124, %125) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        "protocol.yield"(%119#0, %119#1, %119#2, %120, %121, %126) : (!data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
      }) : (ui64, !data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %108:3 = "protocol.local_call"(%107#4, %107#5) <{callee = @zkl_c36a2d2c6bd38573735fb9b90d1a3848c562d2c1f688234e2b669408e9c9eea9, role = "role00000001", site = "s48"}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      "protocol.return"(%107#3, %107#0, %107#1, %107#2, %108#0, %108#1, %108#2) : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, ui64, !runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> i1, sym_name = "zkf_326ab2331715c62ba21cb6a967c927ba6ad7f7f2da5e84eb0e5de0fc610f26ca", sym_visibility = "private"}> ({
    ^bb0(%arg58: !data.field_vector<"bls12-381.fr">, %arg59: ui64, %arg60: ui64):
      %89 = "func.call"(%arg58, %arg59, %arg60) <{callee = @zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %90 = "data.index"() <{value = 1 : ui64}> : () -> ui64
      %91 = "data.index_equal"(%89, %90) : (ui64, ui64) -> i1
      %92 = "data.branch"(%91, %arg58, %arg59, %arg60) <{alternatives = ["then", "else"]}> ({
      ^bb0(%arg64: !data.field_vector<"bls12-381.fr">, %arg65: ui64, %arg66: ui64):
        %94 = "func.call"(%arg64, %arg65, %arg66) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !data.field_vector<"bls12-381.fr">
        %95 = "data.dim"(%94) <{axis = 0 : i64}> : (!data.field_vector<"bls12-381.fr">) -> ui64
        %96 = "func.call"(%arg64, %arg65, %arg66) <{callee = @zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
        %97 = "data.index_power_of_two"(%95, %96) : (ui64, ui64) -> i1
        "data.yield"(%97) : (i1) -> ()
      }, {
      ^bb0(%arg61: !data.field_vector<"bls12-381.fr">, %arg62: ui64, %arg63: ui64):
        %93 = "arith.constant"() <{value = false}> : () -> i1
        "data.yield"(%93) : (i1) -> ()
      }) : (i1, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> i1
      "func.return"(%92) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64, sym_name = "zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275", sym_visibility = "private"}> ({
    ^bb0(%arg55: !data.field_vector<"bls12-381.fr">, %arg56: ui64, %arg57: ui64):
      "func.return"(%arg57) : (ui64) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !data.field_vector<"bls12-381.fr">, sym_name = "zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", sym_visibility = "private"}> ({
    ^bb0(%arg52: !data.field_vector<"bls12-381.fr">, %arg53: ui64, %arg54: ui64):
      "func.return"(%arg52) : (!data.field_vector<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64, sym_name = "zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94", sym_visibility = "private"}> ({
    ^bb0(%arg49: !data.field_vector<"bls12-381.fr">, %arg50: ui64, %arg51: ui64):
      "func.return"(%arg50) : (ui64) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "zkf_c51d11bf318ad26bc2fce7b89eec63f85b98f57e91e0e9e6256f84a573b5b6e6", sym_visibility = "private"}> ({
    ^bb0(%arg44: !data.field_vector<"bls12-381.fr">, %arg45: ui64, %arg46: ui64, %arg47: !data.field_vector<"bls12-381.fr">, %arg48: !algebra.field<"bls12-381.fr">):
      %85 = "func.call"(%arg44, %arg45, %arg46) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !data.field_vector<"bls12-381.fr">
      %86 = "algebra.multilinear_restrict_prefix"(%85, %arg47) : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !data.field_vector<"bls12-381.fr">
      %87 = "func.call"(%86) <{callee = @zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e}> : (!data.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %88 = "algebra.field_equal"(%arg48, %87) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "func.return"(%88) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!data.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e", sym_visibility = "private"}> ({
    ^bb0(%arg43: !data.field_vector<"bls12-381.fr">):
      %83 = "algebra.constant"() <{value = #algebra.literal<<"bls12-381.fr">, 0 : ui255> : !algebra.field<"bls12-381.fr">}> : () -> !algebra.field<"bls12-381.fr">
      %84 = "data.finite_fold"(%arg43, %83) <{domain = @finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_domain, step = @finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_body}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%84) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "data.domain"() <{function_type = (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_domain", sym_visibility = "private"}> ({
    ^bb0(%arg42: !data.field_vector<"bls12-381.fr">):
      %82 = "data.domain_elements"(%arg42) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%82) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_body", sym_visibility = "private"}> ({
    ^bb0(%arg39: !algebra.field<"bls12-381.fr">, %arg40: !algebra.field<"bls12-381.fr">, %arg41: !data.field_vector<"bls12-381.fr">):
      %81 = "func.call"(%arg39, %arg40) <{callee = @zkl_3fc17a64a5bb6e75192d0a1362e9954f0d434a10d0f93e319db6b516835a1005}> : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%81) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_3fc17a64a5bb6e75192d0a1362e9954f0d434a10d0f93e319db6b516835a1005", sym_visibility = "private"}> ({
    ^bb0(%arg37: !algebra.field<"bls12-381.fr">, %arg38: !algebra.field<"bls12-381.fr">):
      %80 = "algebra.field_add"(%arg37, %arg38) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%80) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", sym_visibility = "private"}> ({
    ^bb0(%arg36: !runtime.scope):
      %75 = "exec.apply"(%arg36) <{binding = @zkl_binding_7, parameters = [], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%75)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%76: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %77 = "exec.returned"(%76) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%77) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%78: !exec.stop):  // pred: ^bb0
      %79 = "exec.failed"(%78) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%79) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6310h7072696d6974697665736h766563746f725h656d707479", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_e8df957aab384c1d5416600c13a571512206e97abfbf6e0e9cddac5c84860d07", sym_visibility = "private"}> ({
    ^bb0(%arg32: !runtime.scope, %arg33: !runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, %arg34: !data.field_vector<"bls12-381.fr">, %arg35: !algebra.field<"bls12-381.fr">):
      %71 = "exec.apply"(%arg32, %arg33) <{binding = @zkl_binding_9, parameters = [], site = "s0_unpack_0"}> : (!runtime.scope, !runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">) -> !exec.outcome<>
      "exec.dispatch"(%71)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb1:  // pred: ^bb0
      %72 = "exec.returned"(%arg34, %arg35) : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%72) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%73: !exec.stop):  // pred: ^bb0
      %74 = "exec.failed"(%73) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%74) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s8h73756d636865636b10h6f70656e5f636c61696d", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_532a609cf36a935835501ca51308940142121e647ca360843a880bf231f04aa6", sym_visibility = "private"}> ({
    ^bb0(%arg28: !runtime.scope, %arg29: !data.field_vector<"bls12-381.fr">, %arg30: ui64, %arg31: ui64):
      %61 = "func.call"(%arg28, %arg29, %arg30, %arg31) <{callee = @zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087}> {runtime.site = "s0"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%61)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%62: !data.field_vector<"bls12-381.fr">, %63: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %64 = "exec.apply"(%arg28, %62) <{binding = @zkl_binding_10, parameters = [], site = "s3"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%64)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%65: !exec.stop):  // 3 preds: ^bb0, ^bb1, ^bb3
      %66 = "exec.failed"(%65) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%66) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb3(%67: !algebra.field<"bls12-381.fr">):  // pred: ^bb1
      %68 = "exec.apply"(%arg28, %63) <{binding = @zkl_binding_10, parameters = [], site = "s5"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%68)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb4(%69: !algebra.field<"bls12-381.fr">):  // pred: ^bb3
      %70 = "exec.returned"(%67, %69) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%70) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s8h73756d636865636b4h73756d73", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087", sym_visibility = "private"}> ({
    ^bb0(%arg24: !runtime.scope, %arg25: !data.field_vector<"bls12-381.fr">, %arg26: ui64, %arg27: ui64):
      %37 = "exec.apply"(%arg24) <{binding = @zkl_binding_0, parameters = [0 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%37)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%38: ui64):  // pred: ^bb0
      %39 = "func.call"(%arg24, %38, %arg26) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s2"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%39)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%40: !exec.stop):  // 10 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12
      %41 = "exec.failed"(%40) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "func.return"(%41) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%42: i1):  // pred: ^bb1
      %43 = "exec.test"(%arg24, %42) <{site = "s3"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%43)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb4(%44: i1):  // pred: ^bb3
      "cf.cond_br"(%44)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %45 = "runtime.enter_scope"(%arg24) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s3"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%45)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %46 = "runtime.enter_scope"(%arg24) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s3"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%46)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // 2 preds: ^bb10, ^bb13
      %47 = "exec.apply"(%arg24, %arg25) <{binding = @zkl_binding_11, parameters = [], site = "s5"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%47)[^bb14, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%48: !runtime.scope):  // pred: ^bb5
      %49 = "func.call"(%48) <{callee = @zkl_control_11}> : (!runtime.scope) -> !exec.outcome<>
      %50 = "runtime.exit_scope"(%48, %49) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%50)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb9(%51: !runtime.transfer<>):  // pred: ^bb8
      %52 = "runtime.accept_transfer"(%arg24, %51) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%52)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb10:  // pred: ^bb9
      "cf.br"()[^bb7] : () -> ()
    ^bb11(%53: !runtime.scope):  // pred: ^bb6
      %54 = "func.call"(%53) <{callee = @zkl_control_12}> : (!runtime.scope) -> !exec.outcome<>
      %55 = "runtime.exit_scope"(%53, %54) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%55)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb12(%56: !runtime.transfer<>):  // pred: ^bb11
      %57 = "runtime.accept_transfer"(%arg24, %56) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%57)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb13:  // pred: ^bb12
      "cf.br"()[^bb7] : () -> ()
    ^bb14(%58: !data.field_vector<"bls12-381.fr">, %59: !data.field_vector<"bls12-381.fr">):  // pred: ^bb7
      %60 = "exec.returned"(%58, %59) : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "func.return"(%60) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561726h68616c766573", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_11", sym_visibility = "private"}> ({
    ^bb0(%arg23: !runtime.scope):
      %36 = "exec.complete"(%arg23) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%36) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_12", sym_visibility = "private"}> ({
    ^bb0(%arg22: !runtime.scope):
      %33 = "exec.reject"(%arg22) <{reason = "reject", site = "s3_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%33)[^bb1] : (!exec.stop) -> ()
    ^bb1(%34: !exec.stop):  // pred: ^bb0
      %35 = "exec.failed"(%34) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%35) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d", sym_visibility = "private"}> ({
    ^bb0(%arg17: !runtime.scope, %arg18: !data.field_vector<"bls12-381.fr">, %arg19: ui64, %arg20: ui64, %arg21: !algebra.field<"bls12-381.fr">):
      %21 = "func.call"(%arg17, %arg18, %arg19, %arg20) <{callee = @zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087}> {runtime.site = "s0"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%21)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%22: !data.field_vector<"bls12-381.fr">, %23: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %24 = "exec.collect"(%arg17, %22, %23, %arg21) <{body = @zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body, domain = @zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_domain, site = "s4"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%24)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%25: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %26 = "exec.failed"(%25) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%26) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb3(%27: !data.field_vector<"bls12-381.fr">):  // pred: ^bb1
      %28 = "exec.apply"(%arg17) <{binding = @zkl_binding_0, parameters = [1 : ui64], site = "s7"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%28)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%29: ui64):  // pred: ^bb3
      %30 = "exec.apply"(%arg17, %arg19, %29) <{binding = @zkl_binding_12, parameters = [], site = "s8"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%30)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%31: ui64):  // pred: ^bb4
      %32 = "exec.returned"(%27, %31, %arg20) : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%32) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561729h6669785f6669727374", []]} : () -> ()
    "data.domain"() <{function_type = (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, sym_name = "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_domain", sym_visibility = "private"}> ({
    ^bb0(%arg15: !data.field_vector<"bls12-381.fr">, %arg16: !data.field_vector<"bls12-381.fr">):
      %18 = "data.domain_elements"(%arg15) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %19 = "data.domain_elements"(%arg16) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %20 = "data.domain_zip"(%18, %19) : (!data.domain<!algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%20) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body", sym_visibility = "private"}> ({
    ^bb0(%arg9: !runtime.scope, %arg10: !algebra.field<"bls12-381.fr">, %arg11: !algebra.field<"bls12-381.fr">, %arg12: !data.field_vector<"bls12-381.fr">, %arg13: !data.field_vector<"bls12-381.fr">, %arg14: !algebra.field<"bls12-381.fr">):
      %13 = "exec.compute"(%arg9, %arg10, %arg11, %arg14) <{callee = @zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5, site = "body"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%13)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%14: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %15 = "exec.returned"(%14) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%15) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%16: !exec.stop):  // pred: ^bb0
      %17 = "exec.failed"(%16) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%17) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5", sym_visibility = "private"}> ({
    ^bb0(%arg6: !algebra.field<"bls12-381.fr">, %arg7: !algebra.field<"bls12-381.fr">, %arg8: !algebra.field<"bls12-381.fr">):
      %10 = "algebra.field_subtract"(%arg7, %arg6) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %11 = "algebra.field_multiply"(%10, %arg8) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %12 = "algebra.field_add"(%arg6, %11) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%12) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", sym_visibility = "private"}> ({
    ^bb0(%arg3: !runtime.scope, %arg4: !data.field_vector<"bls12-381.fr">, %arg5: !algebra.field<"bls12-381.fr">):
      %5 = "exec.apply"(%arg3, %arg4, %arg5) <{binding = @zkl_binding_13, parameters = [], site = "s0"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%5)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%6: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %7 = "exec.returned"(%6) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%7) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%8: !exec.stop):  // pred: ^bb0
      %9 = "exec.failed"(%8) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%9) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6310h7072696d6974697665736h766563746f726h617070656e64", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_c36a2d2c6bd38573735fb9b90d1a3848c562d2c1f688234e2b669408e9c9eea9", sym_visibility = "private"}> ({
    ^bb0(%arg0: !runtime.scope, %arg1: !data.field_vector<"bls12-381.fr">, %arg2: !algebra.field<"bls12-381.fr">):
      %0 = "exec.apply"(%arg0) <{binding = @zkl_binding_8, parameters = [], site = "s0_create_0"}> : (!runtime.scope) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">)>
      "exec.dispatch"(%0)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">)>) -> ()
    ^bb1(%1: !runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">):  // pred: ^bb0
      %2 = "exec.returned"(%1, %arg1, %arg2) : (!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%2) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%4) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s8h73756d636865636b9h61745f707265666978", []]} : () -> ()
    "relation.declare"() <{formula = @zkf_326ab2331715c62ba21cb6a967c927ba6ad7f7f2da5e84eb0e5de0fc610f26ca, key = "zkl_8c866415d5a42d7cb60d6b39dd52568c20001248a901906f13a3d5d9dd8f74ac", kind = "zkc.language.formula/0", purposes = ["parameter", "parameter", "parameter"], revision = "b38e3036898a0350bf7db3a319e518bcd650355abbfc625037f409f6bb2afc48", signature = (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> i1, static_arguments = [], sym_name = "zkl_8c866415d5a42d7cb60d6b39dd52568c20001248a901906f13a3d5d9dd8f74ac"}> : () -> ()
    "relation.declare"() <{formula = @zkf_c51d11bf318ad26bc2fce7b89eec63f85b98f57e91e0e9e6256f84a573b5b6e6, key = "zkl_f03c5af270c09f9d5e832cdb0dc1d71151cebecfaaa08c6cacd997dde03860e9", kind = "zkc.language.formula/0", purposes = ["parameter", "parameter", "parameter", "statement", "statement"], revision = "dd2b2582f72ba257a868259cea188039de19f66f8a3fafa017be603aa980be98", signature = (!data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, static_arguments = [], sym_name = "zkl_f03c5af270c09f9d5e832cdb0dc1d71151cebecfaaa08c6cacd997dde03860e9"}> : () -> ()
  }) : () -> ()
}) : () -> ()

