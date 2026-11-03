"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>, source_declarations = [[[["nominal", "record", "sumcheck::Pending", [["field", "bls12-381.fr"]]], "linear", false, [["point", ["builtin", "vector", [["field", "bls12-381.fr"]]], unit], ["value", ["field", "bls12-381.fr"], unit]], [], "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992"], [["nominal", "record", "zkc::multilinear::Table", [["field", "bls12-381.fr"]]], "ordinary", false, [["entries", ["builtin", "vector", [["field", "bls12-381.fr"]]], unit], ["dimensions", ["index"], unit], ["columns", ["index"], unit]], [], unit]], [["zkl_cf3586ba980b617860654dacf2506dd277a78d1dcf5b84bcc6376225e7fe4f45", [["claim", ["field", "bls12-381.fr"], ["role00000001"], 0 : ui64, 1 : ui64, ["data", ["role00000001"]]], ["rounds", ["index"], ["role00000000", "role00000001"], 1 : ui64, 1 : ui64, ["data", ["role00000000", "role00000001"]]], ["variables", ["index"], ["role00000000"], 2 : ui64, 1 : ui64, ["data", ["role00000000"]]], ["values", ["builtin", "vector", [["field", "bls12-381.fr"]]], ["role00000000"], 3 : ui64, 1 : ui64, ["data", ["role00000000"]]]], [["evaluation", ["nominal", "record", "sumcheck::Pending", [["field", "bls12-381.fr"]]], ["role00000001"], 0 : ui64, 3 : ui64, ["data", ["role00000001"]]], ["residual", ["builtin", "vector", [["field", "bls12-381.fr"]]], ["role00000000"], 3 : ui64, 1 : ui64, ["data", ["role00000000"]]], ["point", ["builtin", "vector", [["field", "bls12-381.fr"]]], ["role00000000"], 4 : ui64, 1 : ui64, ["data", ["role00000000"]]]]], ["zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", [["values", ["nominal", "record", "zkc::multilinear::Table", [["field", "bls12-381.fr"]]], ["role00000000"], 0 : ui64, 3 : ui64, ["data", ["role00000000"]]], ["claim", ["nominal", "record", "sumcheck::Pending", [["field", "bls12-381.fr"]]], ["role00000001"], 3 : ui64, 3 : ui64, ["data", ["role00000001"]]], ["rounds", ["index"], ["role00000000", "role00000001"], 6 : ui64, 1 : ui64, ["data", ["role00000000", "role00000001"]]]], [["point", ["builtin", "vector", [["field", "bls12-381.fr"]]], ["role00000000"], 0 : ui64, 1 : ui64, ["data", ["role00000000"]]], ["residual", ["nominal", "record", "zkc::multilinear::Table", [["field", "bls12-381.fr"]]], ["role00000000"], 1 : ui64, 3 : ui64, ["data", ["role00000000"]]], ["evaluation", ["nominal", "record", "sumcheck::Pending", [["field", "bls12-381.fr"]]], ["role00000001"], 4 : ui64, 3 : ui64, ["data", ["role00000001"]]]]]], [["sumcheck::Pending", "f6d1de752bd5c052f6b7834ce4eb51d7bbd71ffdd0aed5ed0718d84fac2faf3b"], ["zkc::multilinear::Table", "a568766f66b8088201c0c521621df6d49be54fd6e8c10ae1ceb6af4698899482"]]]}> ({
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.append", function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, implementation = "", sym_name = "zkl_binding_13"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.sub", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_12"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.split", function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>, implementation = "", sym_name = "zkl_binding_11"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.sum", function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, implementation = "", sym_name = "zkl_binding_10"}> : () -> ()
    "runtime.binding"() <{arguments = ["zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992"], contract = "resource_unit.consume", function_type = (!runtime.scope, !runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">) -> !exec.outcome<>, implementation = "", sym_name = "zkl_binding_9"}> : () -> ()
    "runtime.binding"() <{arguments = ["zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992"], contract = "resource_unit.create", function_type = (!runtime.scope) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">)>, implementation = "", sym_name = "zkl_binding_8"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.empty", function_type = (!runtime.scope) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, implementation = "", sym_name = "zkl_binding_7"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.mul", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_6"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.less", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>, implementation = "", sym_name = "zkl_binding_5"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.div", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_4"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.equal", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>, implementation = "", sym_name = "zkl_binding_3"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.mod", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_2"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.length", function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_1"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.constant", function_type = (!runtime.scope) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_0"}> : () -> ()
    "protocol.func"() <{contracts = [], function_type = (!algebra.field<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">), input_roles = [["role00000001"], ["role00000000", "role00000001"], ["role00000000"], ["role00000000"], ["role00000001"]], origin = ["sums::Reduction", [["F", ["field", "bls12-381.fr"]], ["Max", ["nat", "4"]]]], output_roles = [["role00000001"], ["role00000001"], ["role00000001"], ["role00000000"], ["role00000000"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_cf3586ba980b617860654dacf2506dd277a78d1dcf5b84bcc6376225e7fe4f45"}> ({
    ^bb0(%arg117: !algebra.field<"bls12-381.fr">, %arg118: ui64, %arg119: ui64, %arg120: !data.field_vector<"bls12-381.fr">, %arg121: !protocol.service_ref<"random.bls12-381.fr/0">):
      %321 = "data.index"() <{value = 1 : ui64}> : () -> ui64
      %322:3 = "protocol.local_call"(%arg120, %arg119, %321) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a, role = "role00000000", site = "s1"}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> (!data.field_vector<"bls12-381.fr">, ui64, ui64)
      %323:3 = "protocol.local_call"(%arg117) <{callee = @zkl_c0a3a2b8b5f989e0e9c138a171631d20dc8bd296769b6ee7636d2d79a8518ba0, role = "role00000001", site = "s3"}> : (!algebra.field<"bls12-381.fr">) -> (!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %324:7 = "protocol.apply"(%322#0, %322#1, %322#2, %323#0, %323#1, %323#2, %arg118, %arg121) <{callee = @zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d, roles = ["role00000000", "role00000001"], site = "s5"}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64, !runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, ui64, !runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %325 = "func.call"(%324#1, %324#2, %324#3) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !data.field_vector<"bls12-381.fr">
      "protocol.return"(%324#4, %324#5, %324#6, %325, %324#0) : (!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", sym_visibility = "private"}> ({
    ^bb0(%arg113: !runtime.scope, %arg114: !data.field_vector<"bls12-381.fr">, %arg115: ui64, %arg116: ui64):
      %302 = "func.call"(%arg113, %arg114, %arg115, %arg116) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655}> {runtime.site = "s0"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%302)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%303: i1):  // pred: ^bb0
      %304 = "exec.test"(%arg113, %303) <{site = "s1"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%304)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%305: !exec.stop):  // 8 preds: ^bb0, ^bb1, ^bb4, ^bb5, ^bb7, ^bb8, ^bb10, ^bb11
      %306 = "exec.failed"(%305) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%306) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb3(%307: i1):  // pred: ^bb1
      "cf.cond_br"(%307)[^bb4, ^bb5] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb4:  // pred: ^bb3
      %308 = "runtime.enter_scope"(%arg113) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%308)[^bb7, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb5:  // pred: ^bb3
      %309 = "runtime.enter_scope"(%arg113) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%309)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // 2 preds: ^bb9, ^bb12
      %310 = "exec.returned"(%arg114, %arg115, %arg116) : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%310) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb7(%311: !runtime.scope):  // pred: ^bb4
      %312 = "func.call"(%311) <{callee = @zkl_control_0}> : (!runtime.scope) -> !exec.outcome<>
      %313 = "runtime.exit_scope"(%311, %312) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%313)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb8(%314: !runtime.transfer<>):  // pred: ^bb7
      %315 = "runtime.accept_transfer"(%arg113, %314) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%315)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb9:  // pred: ^bb8
      "cf.br"()[^bb6] : () -> ()
    ^bb10(%316: !runtime.scope):  // pred: ^bb5
      %317 = "func.call"(%316) <{callee = @zkl_control_1}> : (!runtime.scope) -> !exec.outcome<>
      %318 = "runtime.exit_scope"(%316, %317) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%318)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb11(%319: !runtime.transfer<>):  // pred: ^bb10
      %320 = "runtime.accept_transfer"(%arg113, %319) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%320)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb12:  // pred: ^bb11
      "cf.br"()[^bb6] : () -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561725h7461626c65", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_0", sym_visibility = "private"}> ({
    ^bb0(%arg112: !runtime.scope):
      %301 = "exec.complete"(%arg112) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%301) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_1", sym_visibility = "private"}> ({
    ^bb0(%arg111: !runtime.scope):
      %298 = "exec.reject"(%arg111) <{reason = "reject", site = "s1_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%298)[^bb1] : (!exec.stop) -> ()
    ^bb1(%299: !exec.stop):  // pred: ^bb0
      %300 = "exec.failed"(%299) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%300) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", sym_visibility = "private"}> ({
    ^bb0(%arg107: !runtime.scope, %arg108: !data.field_vector<"bls12-381.fr">, %arg109: ui64, %arg110: ui64):
      %240 = "exec.apply"(%arg107) <{binding = @zkl_binding_0, parameters = [0 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%240)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%241: ui64):  // pred: ^bb0
      %242 = "func.call"(%arg107, %241, %arg110) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s1"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%242)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%243: !exec.stop):  // 23 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12, ^bb15, ^bb16, ^bb17, ^bb18, ^bb19, ^bb21, ^bb22, ^bb25, ^bb26, ^bb28, ^bb29, ^bb31, ^bb32
      %244 = "exec.failed"(%243) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%244) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%245: i1):  // pred: ^bb1
      %246 = "exec.test"(%arg107, %245) <{site = "s3"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%246)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb4(%247: i1):  // pred: ^bb3
      "cf.cond_br"(%247)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %248 = "runtime.enter_scope"(%arg107, %arg109) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "then", site = "s3"}> : (!runtime.scope, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%248)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %249 = "runtime.enter_scope"(%arg107, %arg109) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "else", site = "s3"}> : (!runtime.scope, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%249)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7(%250: i1):  // 2 preds: ^bb10, ^bb13
      %251 = "exec.test"(%arg107, %250) <{site = "s11"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%251)[^bb14, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb8(%252: !runtime.scope):  // pred: ^bb5
      %253 = "func.call"(%252, %arg109) <{callee = @zkl_control_2}> : (!runtime.scope, ui64) -> !exec.outcome<(i1)>
      %254 = "runtime.exit_scope"(%252, %253) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%254)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb9(%255: !runtime.transfer<(i1)>):  // pred: ^bb8
      %256 = "runtime.accept_transfer"(%arg107, %255) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%256)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb10(%257: i1):  // pred: ^bb9
      "cf.br"(%257)[^bb7] : (i1) -> ()
    ^bb11(%258: !runtime.scope):  // pred: ^bb6
      %259 = "func.call"(%258, %arg109) <{callee = @zkl_control_3}> : (!runtime.scope, ui64) -> !exec.outcome<(i1)>
      %260 = "runtime.exit_scope"(%258, %259) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%260)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb12(%261: !runtime.transfer<(i1)>):  // pred: ^bb11
      %262 = "runtime.accept_transfer"(%arg107, %261) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%262)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb13(%263: i1):  // pred: ^bb12
      "cf.br"(%263)[^bb7] : (i1) -> ()
    ^bb14(%264: i1):  // pred: ^bb7
      "cf.cond_br"(%264)[^bb15, ^bb16] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb15:  // pred: ^bb14
      %265 = "runtime.enter_scope"(%arg107, %arg108, %arg110) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "then", site = "s11"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%265)[^bb18, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb16:  // pred: ^bb14
      %266 = "runtime.enter_scope"(%arg107, %arg108, %arg110) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "else", site = "s11"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%266)[^bb21, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb17(%267: i1):  // 2 preds: ^bb20, ^bb23
      %268 = "exec.test"(%arg107, %267) <{site = "s22"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%268)[^bb24, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb18(%269: !runtime.scope):  // pred: ^bb15
      %270 = "func.call"(%269, %arg108, %arg110) <{callee = @zkl_control_4}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>
      %271 = "runtime.exit_scope"(%269, %270) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%271)[^bb19, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb19(%272: !runtime.transfer<(i1)>):  // pred: ^bb18
      %273 = "runtime.accept_transfer"(%arg107, %272) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%273)[^bb20, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb20(%274: i1):  // pred: ^bb19
      "cf.br"(%274)[^bb17] : (i1) -> ()
    ^bb21(%275: !runtime.scope):  // pred: ^bb16
      %276 = "func.call"(%275, %arg108, %arg110) <{callee = @zkl_control_5}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>
      %277 = "runtime.exit_scope"(%275, %276) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%277)[^bb22, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb22(%278: !runtime.transfer<(i1)>):  // pred: ^bb21
      %279 = "runtime.accept_transfer"(%arg107, %278) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%279)[^bb23, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb23(%280: i1):  // pred: ^bb22
      "cf.br"(%280)[^bb17] : (i1) -> ()
    ^bb24(%281: i1):  // pred: ^bb17
      "cf.cond_br"(%281)[^bb25, ^bb26] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb25:  // pred: ^bb24
      %282 = "runtime.enter_scope"(%arg107, %arg108, %arg109, %arg110) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "then", site = "s22"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%282)[^bb28, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb26:  // pred: ^bb24
      %283 = "runtime.enter_scope"(%arg107, %arg108, %arg109, %arg110) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "else", site = "s22"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%283)[^bb31, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb27(%284: i1):  // 2 preds: ^bb30, ^bb33
      %285 = "exec.returned"(%284) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%285) : (!exec.outcome<(i1)>) -> ()
    ^bb28(%286: !runtime.scope):  // pred: ^bb25
      %287 = "func.call"(%286, %arg108, %arg109, %arg110) <{callee = @zkl_control_6}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      %288 = "runtime.exit_scope"(%286, %287) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%288)[^bb29, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb29(%289: !runtime.transfer<(i1)>):  // pred: ^bb28
      %290 = "runtime.accept_transfer"(%arg107, %289) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%290)[^bb30, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb30(%291: i1):  // pred: ^bb29
      "cf.br"(%291)[^bb27] : (i1) -> ()
    ^bb31(%292: !runtime.scope):  // pred: ^bb26
      %293 = "func.call"(%292, %arg108, %arg109, %arg110) <{callee = @zkl_control_7}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      %294 = "runtime.exit_scope"(%292, %293) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%294)[^bb32, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb32(%295: !runtime.transfer<(i1)>):  // pred: ^bb31
      %296 = "runtime.accept_transfer"(%arg107, %295) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%296)[^bb33, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb33(%297: i1):  // pred: ^bb32
      "cf.br"(%297)[^bb27] : (i1) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_2", sym_visibility = "private"}> ({
    ^bb0(%arg105: !runtime.scope, %arg106: ui64):
      %233 = "exec.apply"(%arg105) <{binding = @zkl_binding_0, parameters = [64 : ui64], site = "s4"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%233)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%234: ui64):  // pred: ^bb0
      %235 = "func.call"(%arg105, %arg106, %234) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s5"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%235)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%236: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %237 = "exec.failed"(%236) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%237) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%238: i1):  // pred: ^bb1
      %239 = "exec.complete"(%arg105, %238) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%239) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_3", sym_visibility = "private"}> ({
    ^bb0(%arg103: !runtime.scope, %arg104: ui64):
      %228 = "exec.boolean"(%arg103) <{site = "s7", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%228)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%229: i1):  // pred: ^bb0
      %230 = "exec.complete"(%arg103, %229) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%230) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%231: !exec.stop):  // pred: ^bb0
      %232 = "exec.failed"(%231) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%232) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_4", sym_visibility = "private"}> ({
    ^bb0(%arg100: !runtime.scope, %arg101: !data.field_vector<"bls12-381.fr">, %arg102: ui64):
      %217 = "exec.apply"(%arg100, %arg101) <{binding = @zkl_binding_1, parameters = [], site = "s12"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%217)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%218: ui64):  // pred: ^bb0
      %219 = "exec.apply"(%arg100, %218, %arg102) <{binding = @zkl_binding_2, parameters = [], site = "s13"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%219)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%220: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %221 = "exec.failed"(%220) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%221) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%222: ui64):  // pred: ^bb1
      %223 = "exec.apply"(%arg100) <{binding = @zkl_binding_0, parameters = [0 : ui64], site = "s14"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%223)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%224: ui64):  // pred: ^bb3
      %225 = "exec.apply"(%arg100, %222, %224) <{binding = @zkl_binding_3, parameters = [], site = "s15"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%225)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb5(%226: i1):  // pred: ^bb4
      %227 = "exec.complete"(%arg100, %226) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%227) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_5", sym_visibility = "private"}> ({
    ^bb0(%arg97: !runtime.scope, %arg98: !data.field_vector<"bls12-381.fr">, %arg99: ui64):
      %212 = "exec.boolean"(%arg97) <{site = "s17", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%212)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%213: i1):  // pred: ^bb0
      %214 = "exec.complete"(%arg97, %213) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%214) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%215: !exec.stop):  // pred: ^bb0
      %216 = "exec.failed"(%215) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%216) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_6", sym_visibility = "private"}> ({
    ^bb0(%arg93: !runtime.scope, %arg94: !data.field_vector<"bls12-381.fr">, %arg95: ui64, %arg96: ui64):
      %201 = "exec.apply"(%arg93, %arg94) <{binding = @zkl_binding_1, parameters = [], site = "s23"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%201)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%202: ui64):  // pred: ^bb0
      %203 = "exec.apply"(%arg93, %202, %arg96) <{binding = @zkl_binding_4, parameters = [], site = "s24"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%203)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%204: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %205 = "exec.failed"(%204) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%205) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%206: ui64):  // pred: ^bb1
      %207 = "func.call"(%arg93, %arg95) <{callee = @s3h7a6b6311h6d756c74696c696e6561724h726f7773}> {runtime.site = "s25"} : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%207)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%208: ui64):  // pred: ^bb3
      %209 = "exec.apply"(%arg93, %206, %208) <{binding = @zkl_binding_3, parameters = [], site = "s26"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%209)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb5(%210: i1):  // pred: ^bb4
      %211 = "exec.complete"(%arg93, %210) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%211) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_7", sym_visibility = "private"}> ({
    ^bb0(%arg89: !runtime.scope, %arg90: !data.field_vector<"bls12-381.fr">, %arg91: ui64, %arg92: ui64):
      %196 = "exec.boolean"(%arg89) <{site = "s28", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%196)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%197: i1):  // pred: ^bb0
      %198 = "exec.complete"(%arg89, %197) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%198) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%199: !exec.stop):  // pred: ^bb0
      %200 = "exec.failed"(%199) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%200) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "s3h7a6b637h696e64696365734h6c657373", sym_visibility = "private"}> ({
    ^bb0(%arg86: !runtime.scope, %arg87: ui64, %arg88: ui64):
      %191 = "exec.apply"(%arg86, %arg87, %arg88) <{binding = @zkl_binding_5, parameters = [], site = "s0"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%191)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%192: i1):  // pred: ^bb0
      %193 = "exec.returned"(%192) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%193) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%194: !exec.stop):  // pred: ^bb0
      %195 = "exec.failed"(%194) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%195) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.origin = ["s3h7a6b637h696e64696365734h6c657373", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "s3h7a6b6311h6d756c74696c696e6561724h726f7773", sym_visibility = "private"}> ({
    ^bb0(%arg84: !runtime.scope, %arg85: ui64):
      %144 = "exec.apply"(%arg84) <{binding = @zkl_binding_0, parameters = [64 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%144)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%145: ui64):  // pred: ^bb0
      %146 = "func.call"(%arg84, %arg85, %145) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s1"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%146)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%147: !exec.stop):  // 14 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12, ^bb14, ^bb15, ^bb19, ^bb21
      %148 = "exec.failed"(%147) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%148) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%149: i1):  // pred: ^bb1
      %150 = "exec.test"(%arg84, %149) <{site = "s2"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%150)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb4(%151: i1):  // pred: ^bb3
      "cf.cond_br"(%151)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %152 = "runtime.enter_scope"(%arg84) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s2"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%152)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %153 = "runtime.enter_scope"(%arg84) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s2"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%153)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // 2 preds: ^bb10, ^bb13
      %154 = "exec.apply"(%arg84) <{binding = @zkl_binding_0, parameters = [1 : ui64], site = "s3"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%154)[^bb14, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb8(%155: !runtime.scope):  // pred: ^bb5
      %156 = "func.call"(%155) <{callee = @zkl_control_8}> : (!runtime.scope) -> !exec.outcome<>
      %157 = "runtime.exit_scope"(%155, %156) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%157)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb9(%158: !runtime.transfer<>):  // pred: ^bb8
      %159 = "runtime.accept_transfer"(%arg84, %158) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%159)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb10:  // pred: ^bb9
      "cf.br"()[^bb7] : () -> ()
    ^bb11(%160: !runtime.scope):  // pred: ^bb6
      %161 = "func.call"(%160) <{callee = @zkl_control_9}> : (!runtime.scope) -> !exec.outcome<>
      %162 = "runtime.exit_scope"(%160, %161) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%162)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb12(%163: !runtime.transfer<>):  // pred: ^bb11
      %164 = "runtime.accept_transfer"(%arg84, %163) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%164)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb13:  // pred: ^bb12
      "cf.br"()[^bb7] : () -> ()
    ^bb14(%165: ui64):  // pred: ^bb7
      %166 = "exec.apply"(%arg84) <{binding = @zkl_binding_0, parameters = [0 : ui64], site = "s5"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%166)[^bb15, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb15(%167: ui64):  // pred: ^bb14
      %168 = "exec.range"(%arg84, %167, %arg85) <{site = "s6"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%168)[^bb16, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i64, i64)>) -> ()
    ^bb16(%169: i64, %170: i64):  // pred: ^bb15
      %171 = "runtime.borrow_transfer"(%arg84, %165) : (!runtime.scope, ui64) -> !runtime.transfer<(ui64)>
      "cf.br"(%169, %171)[^bb17] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb17(%172: i64, %173: !runtime.transfer<(ui64)>):  // 2 preds: ^bb16, ^bb20
      %174 = "arith.cmpi"(%172, %170) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%174, %173)[^bb18, ^bb19] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(ui64)>) -> ()
    ^bb18:  // pred: ^bb17
      %175 = "runtime.iteration"(%arg84, %172) <{site = "s6"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%175)[^bb22, ^bb21] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb19(%176: !runtime.transfer<(ui64)>):  // pred: ^bb17
      %177 = "runtime.accept_transfer"(%arg84, %176) : (!runtime.scope, !runtime.transfer<(ui64)>) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%177)[^bb25, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb20(%178: !runtime.transfer<(ui64)>):  // pred: ^bb24
      %179 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %180 = "arith.addi"(%172, %179) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%180, %178)[^bb17] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb21(%181: !exec.stop):  // 3 preds: ^bb18, ^bb22, ^bb23
      "runtime.release_transfer"(%173) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%181)[^bb2] : (!exec.stop) -> ()
    ^bb22(%182: ui64):  // pred: ^bb18
      %183 = "runtime.transfer_values"(%173) : (!runtime.transfer<(ui64)>) -> ui64
      %184 = "runtime.enter_scope"(%arg84, %172, %182, %183) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 2>, site = "s6"}> : (!runtime.scope, i64, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%184)[^bb23, ^bb21] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb23(%185: !runtime.scope):  // pred: ^bb22
      %186 = "func.call"(%185, %182, %183) <{callee = @zkl_control_10}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      %187 = "runtime.exit_scope"(%185, %186) : (!runtime.scope, !exec.outcome<(ui64)>) -> !exec.outcome<(!runtime.transfer<(ui64)>)>
      "exec.dispatch"(%187)[^bb24, ^bb21] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(ui64)>)>) -> ()
    ^bb24(%188: !runtime.transfer<(ui64)>):  // pred: ^bb23
      "runtime.release_transfer"(%173) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%188)[^bb20] : (!runtime.transfer<(ui64)>) -> ()
    ^bb25(%189: ui64):  // pred: ^bb19
      %190 = "exec.returned"(%189) : (ui64) -> !exec.outcome<(ui64)>
      "func.return"(%190) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561724h726f7773", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_8", sym_visibility = "private"}> ({
    ^bb0(%arg83: !runtime.scope):
      %143 = "exec.complete"(%arg83) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%143) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_9", sym_visibility = "private"}> ({
    ^bb0(%arg82: !runtime.scope):
      %140 = "exec.reject"(%arg82) <{reason = "reject", site = "s2_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%140)[^bb1] : (!exec.stop) -> ()
    ^bb1(%141: !exec.stop):  // pred: ^bb0
      %142 = "exec.failed"(%141) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%142) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "zkl_control_10", sym_visibility = "private"}> ({
    ^bb0(%arg79: !runtime.scope, %arg80: ui64, %arg81: ui64):
      %133 = "exec.apply"(%arg79) <{binding = @zkl_binding_0, parameters = [2 : ui64], site = "s7"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%133)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%134: ui64):  // pred: ^bb0
      %135 = "exec.apply"(%arg79, %arg81, %134) <{binding = @zkl_binding_6, parameters = [], site = "s8"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%135)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%136: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %137 = "exec.failed"(%136) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%137) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%138: ui64):  // pred: ^bb1
      %139 = "exec.complete"(%arg79, %138) : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "func.return"(%139) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_c0a3a2b8b5f989e0e9c138a171631d20dc8bd296769b6ee7636d2d79a8518ba0", sym_visibility = "private"}> ({
    ^bb0(%arg77: !runtime.scope, %arg78: !algebra.field<"bls12-381.fr">):
      %126 = "exec.apply"(%arg77) <{binding = @zkl_binding_7, parameters = [], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%126)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%127: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %128 = "exec.apply"(%arg77) <{binding = @zkl_binding_8, parameters = [], site = "s1_create_0"}> : (!runtime.scope) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">)>
      "exec.dispatch"(%128)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">)>) -> ()
    ^bb2(%129: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %130 = "exec.failed"(%129) : (!exec.stop) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%130) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb3(%131: !runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">):  // pred: ^bb1
      %132 = "exec.returned"(%131, %127, %arg78) : (!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%132) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s8h73756d636865636b7h70656e64696e67", []]} : () -> ()
    "protocol.func"() <{contracts = [["input", "shape", [@zkl_8c866415d5a42d7cb60d6b39dd52568c20001248a901906f13a3d5d9dd8f74ac, [["input", 0, "role00000000"], ["input", 1, "role00000000"], ["input", 2, "role00000000"]]], unit, unit], ["continuation", "initial_sum", [@zkl_f03c5af270c09f9d5e832cdb0dc1d71151cebecfaaa08c6cacd997dde03860e9, [["input", 0, "role00000000"], ["input", 1, "role00000000"], ["input", 2, "role00000000"], ["input", 4, "role00000001"], ["input", 5, "role00000001"]]], [@zkl_f03c5af270c09f9d5e832cdb0dc1d71151cebecfaaa08c6cacd997dde03860e9, [["input", 0, "role00000000"], ["input", 1, "role00000000"], ["input", 2, "role00000000"], ["output", 5, "role00000001"], ["output", 6, "role00000001"]]], unit]], function_type = (!data.field_vector<"bls12-381.fr">, ui64, ui64, !runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, ui64, !runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), input_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"], ["role00000001"], ["role00000000", "role00000001"], ["role00000001"]], origin = ["sumcheck::Reduce", [["F", ["field", "bls12-381.fr"]], ["Max", ["nat", "4"]]]], output_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"], ["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d"}> ({
    ^bb0(%arg61: !data.field_vector<"bls12-381.fr">, %arg62: ui64, %arg63: ui64, %arg64: !runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, %arg65: !data.field_vector<"bls12-381.fr">, %arg66: !algebra.field<"bls12-381.fr">, %arg67: ui64, %arg68: !protocol.service_ref<"random.bls12-381.fr/0">):
      %97 = "func.call"(%arg61, %arg62, %arg63) <{callee = @zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %98 = "data.index"() <{value = 1 : ui64}> : () -> ui64
      %99 = "data.index_equal"(%97, %98) : (ui64, ui64) -> i1
      "protocol.guard"(%99) <{owner = "role00000000", site = "s3"}> : (i1) -> ()
      %100 = "func.call"(%arg61, %arg62, %arg63) <{callee = @zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %101 = "protocol.local_call"(%100, %arg67) <{callee = @s3h7a6b637h696e64696365734h6c657373, role = "role00000000", site = "s5"}> : (ui64, ui64) -> i1
      %102 = "arith.constant"() <{value = false}> : () -> i1
      %103 = "arith.cmpi"(%101, %102) <{predicate = 0 : i64}> : (i1, i1) -> i1
      "protocol.guard"(%103) <{owner = "role00000000", site = "s8"}> : (i1) -> ()
      %104 = "protocol.local_call"() <{callee = @zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f, role = "role00000000", site = "s10"}> : () -> !data.field_vector<"bls12-381.fr">
      %105:2 = "protocol.local_call"(%arg64, %arg65, %arg66) <{callee = @zkl_e8df957aab384c1d5416600c13a571512206e97abfbf6e0e9cddac5c84860d07, role = "role00000001", site = "s12"}> : (!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %106:6 = "protocol.repeat"(%arg67, %arg61, %arg62, %arg63, %104, %105#0, %105#1, %arg68) <{carried = 6 : i64, carried_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"]], maximum = 4 : i64, roles = ["role00000000", "role00000001"], site = "s18"}> ({
      ^bb0(%arg69: ui64, %arg70: !data.field_vector<"bls12-381.fr">, %arg71: ui64, %arg72: ui64, %arg73: !data.field_vector<"bls12-381.fr">, %arg74: !data.field_vector<"bls12-381.fr">, %arg75: !algebra.field<"bls12-381.fr">, %arg76: !protocol.service_ref<"random.bls12-381.fr/0">):
        %108:2 = "protocol.local_call"(%arg70, %arg71, %arg72) <{callee = @zkl_532a609cf36a935835501ca51308940142121e647ca360843a880bf231f04aa6, role = "role00000000", site = "s19"}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %109 = "protocol.exchange"(%108#0) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %110 = "protocol.restrict_roles"(%109) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %111 = "protocol.exchange"(%108#1) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_1"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %112 = "protocol.restrict_roles"(%111) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %113 = "algebra.field_add"(%110, %112) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %114 = "algebra.field_equal"(%arg75, %113) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
        "protocol.guard"(%114) <{owner = "role00000001", site = "s27"}> : (i1) -> ()
        %115 = "protocol.query"(%arg76) <{method = "draw", owner = "role00000001", site = "label_6368616c6c656e6765"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
        %116 = "protocol.exchange"(%115) <{receiver = "role00000000", sender = "role00000001", site = "label_64656c6976657279_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %117 = "protocol.restrict_roles"(%116) <{roles = ["role00000000"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %118:3 = "protocol.local_call"(%arg70, %arg71, %arg72, %117) <{callee = @zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d, role = "role00000000", site = "s32"}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> (!data.field_vector<"bls12-381.fr">, ui64, ui64)
        %119 = "protocol.local_call"(%arg73, %117) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000000", site = "s34"}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !data.field_vector<"bls12-381.fr">
        %120 = "protocol.local_call"(%arg74, %115) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000001", site = "s36"}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !data.field_vector<"bls12-381.fr">
        %121 = "algebra.constant"() <{value = #algebra.literal<<"bls12-381.fr">, 1 : ui255> : !algebra.field<"bls12-381.fr">}> : () -> !algebra.field<"bls12-381.fr">
        %122 = "algebra.field_subtract"(%121, %115) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %123 = "algebra.field_multiply"(%122, %110) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %124 = "algebra.field_multiply"(%115, %112) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %125 = "algebra.field_add"(%123, %124) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        "protocol.yield"(%118#0, %118#1, %118#2, %119, %120, %125) : (!data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
      }) : (ui64, !data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %107:3 = "protocol.local_call"(%106#4, %106#5) <{callee = @zkl_c36a2d2c6bd38573735fb9b90d1a3848c562d2c1f688234e2b669408e9c9eea9, role = "role00000001", site = "s48"}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      "protocol.return"(%106#3, %106#0, %106#1, %106#2, %107#0, %107#1, %107#2) : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, ui64, !runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> i1, sym_name = "zkf_326ab2331715c62ba21cb6a967c927ba6ad7f7f2da5e84eb0e5de0fc610f26ca", sym_visibility = "private"}> ({
    ^bb0(%arg58: !data.field_vector<"bls12-381.fr">, %arg59: ui64, %arg60: ui64):
      %89 = "func.call"(%arg58, %arg59, %arg60) <{callee = @zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %90 = "data.index"() <{value = 1 : ui64}> : () -> ui64
      %91 = "data.index_equal"(%89, %90) : (ui64, ui64) -> i1
      %92 = "func.call"(%arg58, %arg59, %arg60) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !data.field_vector<"bls12-381.fr">
      %93 = "data.dim"(%92) <{axis = 0 : i64}> : (!data.field_vector<"bls12-381.fr">) -> ui64
      %94 = "func.call"(%arg58, %arg59, %arg60) <{callee = @zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %95 = "data.index_power_of_two"(%93, %94) : (ui64, ui64) -> i1
      %96 = "arith.andi"(%91, %95) : (i1, i1) -> i1
      "func.return"(%96) : (i1) -> ()
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
    "func.func"() <{function_type = (!runtime.scope, !runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_e8df957aab384c1d5416600c13a571512206e97abfbf6e0e9cddac5c84860d07", sym_visibility = "private"}> ({
    ^bb0(%arg32: !runtime.scope, %arg33: !runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, %arg34: !data.field_vector<"bls12-381.fr">, %arg35: !algebra.field<"bls12-381.fr">):
      %71 = "exec.apply"(%arg32, %arg33) <{binding = @zkl_binding_9, parameters = [], site = "s0_unpack_0"}> : (!runtime.scope, !runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">) -> !exec.outcome<>
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
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_c36a2d2c6bd38573735fb9b90d1a3848c562d2c1f688234e2b669408e9c9eea9", sym_visibility = "private"}> ({
    ^bb0(%arg0: !runtime.scope, %arg1: !data.field_vector<"bls12-381.fr">, %arg2: !algebra.field<"bls12-381.fr">):
      %0 = "exec.apply"(%arg0) <{binding = @zkl_binding_8, parameters = [], site = "s0_create_0"}> : (!runtime.scope) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">)>
      "exec.dispatch"(%0)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">)>) -> ()
    ^bb1(%1: !runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">):  // pred: ^bb0
      %2 = "exec.returned"(%1, %arg1, %arg2) : (!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%2) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%4) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s8h73756d636865636b9h61745f707265666978", []]} : () -> ()
    "relation.declare"() <{formula = @zkf_326ab2331715c62ba21cb6a967c927ba6ad7f7f2da5e84eb0e5de0fc610f26ca, key = "zkl_8c866415d5a42d7cb60d6b39dd52568c20001248a901906f13a3d5d9dd8f74ac", kind = "zkc.language.formula/0", purposes = ["parameter", "parameter", "parameter"], revision = "38b907e02d60bf6870a7d7cd7dfb2c81fa0a4e067cdcc1138f99aed00da6eaed", signature = (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> i1, static_arguments = [], sym_name = "zkl_8c866415d5a42d7cb60d6b39dd52568c20001248a901906f13a3d5d9dd8f74ac"}> : () -> ()
    "relation.declare"() <{formula = @zkf_c51d11bf318ad26bc2fce7b89eec63f85b98f57e91e0e9e6256f84a573b5b6e6, key = "zkl_f03c5af270c09f9d5e832cdb0dc1d71151cebecfaaa08c6cacd997dde03860e9", kind = "zkc.language.formula/0", purposes = ["parameter", "parameter", "parameter", "statement", "statement"], revision = "569415ff287b072bbe1e4e48bfd0f722b01ceaa00a0c97dae52619ecafe372ae", signature = (!data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, static_arguments = [], sym_name = "zkl_f03c5af270c09f9d5e832cdb0dc1d71151cebecfaaa08c6cacd997dde03860e9"}> : () -> ()
  }) : () -> ()
}) : () -> ()

