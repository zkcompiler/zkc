"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>, source_declarations = [[[["nominal", "record", "zkc::multilinear::Table", [["field", "bls12-381.fr"]]], "ordinary", false, [["entries", ["builtin", "vector", [["field", "bls12-381.fr"]]], unit], ["dimensions", ["index"], unit], ["columns", ["index"], unit]], [], unit], [["nominal", "record", "sumcheck::Pending", [["field", "bls12-381.fr"]]], "linear", false, [["point", ["builtin", "vector", [["field", "bls12-381.fr"]]], unit], ["value", ["field", "bls12-381.fr"], unit]], [], "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992"]], [["zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", [["values", ["builtin", "vector", [["field", "bls12-381.fr"]]], ["role00000000", "role00000001"], 0 : ui64, 1 : ui64, ["data", ["role00000000", "role00000001"]]], ["claim", ["field", "bls12-381.fr"], ["role00000001"], 1 : ui64, 1 : ui64, ["data", ["role00000001"]]], ["rounds", ["index"], ["role00000000", "role00000001"], 2 : ui64, 1 : ui64, ["data", ["role00000000", "role00000001"]]]], [["accepted", ["bool"], ["role00000001"], 0 : ui64, 1 : ui64, ["data", ["role00000001"]]]]], ["zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", [["values", ["nominal", "record", "zkc::multilinear::Table", [["field", "bls12-381.fr"]]], ["role00000000"], 0 : ui64, 3 : ui64, ["data", ["role00000000"]]], ["claim", ["nominal", "record", "sumcheck::Pending", [["field", "bls12-381.fr"]]], ["role00000001"], 3 : ui64, 3 : ui64, ["data", ["role00000001"]]], ["rounds", ["index"], ["role00000000", "role00000001"], 6 : ui64, 1 : ui64, ["data", ["role00000000", "role00000001"]]]], [["point", ["builtin", "vector", [["field", "bls12-381.fr"]]], ["role00000000"], 0 : ui64, 1 : ui64, ["data", ["role00000000"]]], ["residual", ["nominal", "record", "zkc::multilinear::Table", [["field", "bls12-381.fr"]]], ["role00000000"], 1 : ui64, 3 : ui64, ["data", ["role00000000"]]], ["evaluation", ["nominal", "record", "sumcheck::Pending", [["field", "bls12-381.fr"]]], ["role00000001"], 4 : ui64, 3 : ui64, ["data", ["role00000001"]]]]]], [["sumcheck::Pending", "f6d1de752bd5c052f6b7834ce4eb51d7bbd71ffdd0aed5ed0718d84fac2faf3b"], ["zkc::multilinear::Table", "a568766f66b8088201c0c521621df6d49be54fd6e8c10ae1ceb6af4698899482"]]]}> ({
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "field.equal", function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>, implementation = "", sym_name = "zkl_binding_14"}> : () -> ()
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
    "protocol.func"() <{contracts = [["input", "shape", [@zkl_733a9984be750c90a7e40f8fc81c10a284cb9ecaf745c62024f07f1a3806a10c, [["input", 0, "role00000001"], ["input", 2, "role00000001"]]], unit, unit], ["target", "public_sum", [@zkl_1c2e12f894c2f4b39d38adc87f1dedbaf7856eb6985dba89eb2261c88030aef2, [["input", 0, "role00000001"], ["input", 1, "role00000001"]]], unit, ["output", 0, "role00000001"]]], function_type = (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> i1, input_roles = [["role00000000", "role00000001"], ["role00000001"], ["role00000000", "role00000001"], ["role00000001"]], origin = ["sumcheck::Sumcheck", [["F", ["field", "bls12-381.fr"]], ["Max", ["nat", "2"]]]], output_roles = [["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071"}> ({
    ^bb0(%arg160: !data.field_vector<"bls12-381.fr">, %arg161: !algebra.field<"bls12-381.fr">, %arg162: ui64, %arg163: !protocol.service_ref<"random.bls12-381.fr/0">):
      %417 = "data.index"() <{value = 1 : ui64}> : () -> ui64
      %418:3 = "protocol.local_call"(%arg160, %arg162, %417) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a, role = "role00000000", site = "s1"}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> (!data.field_vector<"bls12-381.fr">, ui64, ui64)
      %419:3 = "protocol.local_call"(%arg161) <{callee = @zkl_c0a3a2b8b5f989e0e9c138a171631d20dc8bd296769b6ee7636d2d79a8518ba0, role = "role00000001", site = "s3"}> : (!algebra.field<"bls12-381.fr">) -> (!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %420:7 = "protocol.apply"(%418#0, %418#1, %418#2, %419#0, %419#1, %419#2, %arg162, %arg163) <{callee = @zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5, roles = ["role00000000", "role00000001"], site = "label_726564756365"}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64, !runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, ui64, !runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %421 = "protocol.local_call"(%arg160, %420#4, %420#5, %420#6) <{callee = @zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc, role = "role00000001", site = "s9"}> : (!data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "protocol.return"(%421) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!data.field_vector<"bls12-381.fr">, ui64) -> i1, sym_name = "zkf_9ca6c98faa0d00ed80eb608a89db1544ad71443a8944af6ac99e6fd78cb3660b", sym_visibility = "private"}> ({
    ^bb0(%arg158: !data.field_vector<"bls12-381.fr">, %arg159: ui64):
      %410 = "data.dim"(%arg158) <{axis = 0 : i64}> : (!data.field_vector<"bls12-381.fr">) -> ui64
      %411 = "data.index_power_of_two"(%410, %arg159) : (ui64, ui64) -> i1
      %412 = "data.index"() <{value = 2 : ui64}> : () -> ui64
      %413 = "data.index_less"(%412, %arg159) : (ui64, ui64) -> i1
      %414 = "arith.constant"() <{value = false}> : () -> i1
      %415 = "arith.cmpi"(%413, %414) <{predicate = 0 : i64}> : (i1, i1) -> i1
      %416 = "arith.andi"(%411, %415) : (i1, i1) -> i1
      "func.return"(%416) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "zkf_116f3285742dd1275b8149c69b78a6713cd6256a8af715be7c346da1c793a766", sym_visibility = "private"}> ({
    ^bb0(%arg156: !data.field_vector<"bls12-381.fr">, %arg157: !algebra.field<"bls12-381.fr">):
      %408 = "func.call"(%arg156) <{callee = @zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e}> : (!data.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %409 = "algebra.field_equal"(%arg157, %408) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "func.return"(%409) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!data.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e", sym_visibility = "private"}> ({
    ^bb0(%arg155: !data.field_vector<"bls12-381.fr">):
      %406 = "algebra.constant"() <{value = #algebra.literal<<"bls12-381.fr">, 0 : ui255> : !algebra.field<"bls12-381.fr">}> : () -> !algebra.field<"bls12-381.fr">
      %407 = "data.finite_fold"(%arg155, %406) <{domain = @finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_domain, step = @finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_body}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%407) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "data.domain"() <{function_type = (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_domain", sym_visibility = "private"}> ({
    ^bb0(%arg154: !data.field_vector<"bls12-381.fr">):
      %405 = "data.domain_elements"(%arg154) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%405) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_body", sym_visibility = "private"}> ({
    ^bb0(%arg151: !algebra.field<"bls12-381.fr">, %arg152: !algebra.field<"bls12-381.fr">, %arg153: !data.field_vector<"bls12-381.fr">):
      %404 = "func.call"(%arg151, %arg152) <{callee = @zkl_3fc17a64a5bb6e75192d0a1362e9954f0d434a10d0f93e319db6b516835a1005}> : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%404) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_3fc17a64a5bb6e75192d0a1362e9954f0d434a10d0f93e319db6b516835a1005", sym_visibility = "private"}> ({
    ^bb0(%arg149: !algebra.field<"bls12-381.fr">, %arg150: !algebra.field<"bls12-381.fr">):
      %403 = "algebra.field_add"(%arg149, %arg150) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%403) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", sym_visibility = "private"}> ({
    ^bb0(%arg145: !runtime.scope, %arg146: !data.field_vector<"bls12-381.fr">, %arg147: ui64, %arg148: ui64):
      %384 = "func.call"(%arg145, %arg146, %arg147, %arg148) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655}> {runtime.site = "s0"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%384)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%385: i1):  // pred: ^bb0
      %386 = "exec.test"(%arg145, %385) <{site = "s1"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%386)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%387: !exec.stop):  // 8 preds: ^bb0, ^bb1, ^bb4, ^bb5, ^bb7, ^bb8, ^bb10, ^bb11
      %388 = "exec.failed"(%387) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%388) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb3(%389: i1):  // pred: ^bb1
      "cf.cond_br"(%389)[^bb4, ^bb5] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb4:  // pred: ^bb3
      %390 = "runtime.enter_scope"(%arg145) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%390)[^bb7, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb5:  // pred: ^bb3
      %391 = "runtime.enter_scope"(%arg145) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%391)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // 2 preds: ^bb9, ^bb12
      %392 = "exec.returned"(%arg146, %arg147, %arg148) : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%392) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb7(%393: !runtime.scope):  // pred: ^bb4
      %394 = "func.call"(%393) <{callee = @zkl_control_0}> : (!runtime.scope) -> !exec.outcome<>
      %395 = "runtime.exit_scope"(%393, %394) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%395)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb8(%396: !runtime.transfer<>):  // pred: ^bb7
      %397 = "runtime.accept_transfer"(%arg145, %396) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%397)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb9:  // pred: ^bb8
      "cf.br"()[^bb6] : () -> ()
    ^bb10(%398: !runtime.scope):  // pred: ^bb5
      %399 = "func.call"(%398) <{callee = @zkl_control_1}> : (!runtime.scope) -> !exec.outcome<>
      %400 = "runtime.exit_scope"(%398, %399) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%400)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb11(%401: !runtime.transfer<>):  // pred: ^bb10
      %402 = "runtime.accept_transfer"(%arg145, %401) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%402)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb12:  // pred: ^bb11
      "cf.br"()[^bb6] : () -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561725h7461626c65", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_0", sym_visibility = "private"}> ({
    ^bb0(%arg144: !runtime.scope):
      %383 = "exec.complete"(%arg144) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%383) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_1", sym_visibility = "private"}> ({
    ^bb0(%arg143: !runtime.scope):
      %380 = "exec.reject"(%arg143) <{reason = "reject", site = "s1_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%380)[^bb1] : (!exec.stop) -> ()
    ^bb1(%381: !exec.stop):  // pred: ^bb0
      %382 = "exec.failed"(%381) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%382) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", sym_visibility = "private"}> ({
    ^bb0(%arg139: !runtime.scope, %arg140: !data.field_vector<"bls12-381.fr">, %arg141: ui64, %arg142: ui64):
      %322 = "exec.apply"(%arg139) <{binding = @zkl_binding_0, parameters = [0 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%322)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%323: ui64):  // pred: ^bb0
      %324 = "func.call"(%arg139, %323, %arg142) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s1"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%324)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%325: !exec.stop):  // 23 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12, ^bb15, ^bb16, ^bb17, ^bb18, ^bb19, ^bb21, ^bb22, ^bb25, ^bb26, ^bb28, ^bb29, ^bb31, ^bb32
      %326 = "exec.failed"(%325) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%326) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%327: i1):  // pred: ^bb1
      %328 = "exec.test"(%arg139, %327) <{site = "s3"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%328)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb4(%329: i1):  // pred: ^bb3
      "cf.cond_br"(%329)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %330 = "runtime.enter_scope"(%arg139, %arg141) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "then", site = "s3"}> : (!runtime.scope, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%330)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %331 = "runtime.enter_scope"(%arg139, %arg141) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "else", site = "s3"}> : (!runtime.scope, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%331)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7(%332: i1):  // 2 preds: ^bb10, ^bb13
      %333 = "exec.test"(%arg139, %332) <{site = "s11"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%333)[^bb14, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb8(%334: !runtime.scope):  // pred: ^bb5
      %335 = "func.call"(%334, %arg141) <{callee = @zkl_control_2}> : (!runtime.scope, ui64) -> !exec.outcome<(i1)>
      %336 = "runtime.exit_scope"(%334, %335) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%336)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb9(%337: !runtime.transfer<(i1)>):  // pred: ^bb8
      %338 = "runtime.accept_transfer"(%arg139, %337) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%338)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb10(%339: i1):  // pred: ^bb9
      "cf.br"(%339)[^bb7] : (i1) -> ()
    ^bb11(%340: !runtime.scope):  // pred: ^bb6
      %341 = "func.call"(%340, %arg141) <{callee = @zkl_control_3}> : (!runtime.scope, ui64) -> !exec.outcome<(i1)>
      %342 = "runtime.exit_scope"(%340, %341) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%342)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb12(%343: !runtime.transfer<(i1)>):  // pred: ^bb11
      %344 = "runtime.accept_transfer"(%arg139, %343) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%344)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb13(%345: i1):  // pred: ^bb12
      "cf.br"(%345)[^bb7] : (i1) -> ()
    ^bb14(%346: i1):  // pred: ^bb7
      "cf.cond_br"(%346)[^bb15, ^bb16] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb15:  // pred: ^bb14
      %347 = "runtime.enter_scope"(%arg139, %arg140, %arg142) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "then", site = "s11"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%347)[^bb18, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb16:  // pred: ^bb14
      %348 = "runtime.enter_scope"(%arg139, %arg140, %arg142) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "else", site = "s11"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%348)[^bb21, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb17(%349: i1):  // 2 preds: ^bb20, ^bb23
      %350 = "exec.test"(%arg139, %349) <{site = "s22"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%350)[^bb24, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb18(%351: !runtime.scope):  // pred: ^bb15
      %352 = "func.call"(%351, %arg140, %arg142) <{callee = @zkl_control_4}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>
      %353 = "runtime.exit_scope"(%351, %352) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%353)[^bb19, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb19(%354: !runtime.transfer<(i1)>):  // pred: ^bb18
      %355 = "runtime.accept_transfer"(%arg139, %354) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%355)[^bb20, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb20(%356: i1):  // pred: ^bb19
      "cf.br"(%356)[^bb17] : (i1) -> ()
    ^bb21(%357: !runtime.scope):  // pred: ^bb16
      %358 = "func.call"(%357, %arg140, %arg142) <{callee = @zkl_control_5}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>
      %359 = "runtime.exit_scope"(%357, %358) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%359)[^bb22, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb22(%360: !runtime.transfer<(i1)>):  // pred: ^bb21
      %361 = "runtime.accept_transfer"(%arg139, %360) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%361)[^bb23, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb23(%362: i1):  // pred: ^bb22
      "cf.br"(%362)[^bb17] : (i1) -> ()
    ^bb24(%363: i1):  // pred: ^bb17
      "cf.cond_br"(%363)[^bb25, ^bb26] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb25:  // pred: ^bb24
      %364 = "runtime.enter_scope"(%arg139, %arg140, %arg141, %arg142) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "then", site = "s22"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%364)[^bb28, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb26:  // pred: ^bb24
      %365 = "runtime.enter_scope"(%arg139, %arg140, %arg141, %arg142) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "else", site = "s22"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%365)[^bb31, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb27(%366: i1):  // 2 preds: ^bb30, ^bb33
      %367 = "exec.returned"(%366) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%367) : (!exec.outcome<(i1)>) -> ()
    ^bb28(%368: !runtime.scope):  // pred: ^bb25
      %369 = "func.call"(%368, %arg140, %arg141, %arg142) <{callee = @zkl_control_6}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      %370 = "runtime.exit_scope"(%368, %369) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%370)[^bb29, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb29(%371: !runtime.transfer<(i1)>):  // pred: ^bb28
      %372 = "runtime.accept_transfer"(%arg139, %371) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%372)[^bb30, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb30(%373: i1):  // pred: ^bb29
      "cf.br"(%373)[^bb27] : (i1) -> ()
    ^bb31(%374: !runtime.scope):  // pred: ^bb26
      %375 = "func.call"(%374, %arg140, %arg141, %arg142) <{callee = @zkl_control_7}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      %376 = "runtime.exit_scope"(%374, %375) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%376)[^bb32, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb32(%377: !runtime.transfer<(i1)>):  // pred: ^bb31
      %378 = "runtime.accept_transfer"(%arg139, %377) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%378)[^bb33, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb33(%379: i1):  // pred: ^bb32
      "cf.br"(%379)[^bb27] : (i1) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_2", sym_visibility = "private"}> ({
    ^bb0(%arg137: !runtime.scope, %arg138: ui64):
      %315 = "exec.apply"(%arg137) <{binding = @zkl_binding_0, parameters = [64 : ui64], site = "s4"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%315)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%316: ui64):  // pred: ^bb0
      %317 = "func.call"(%arg137, %arg138, %316) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s5"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%317)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%318: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %319 = "exec.failed"(%318) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%319) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%320: i1):  // pred: ^bb1
      %321 = "exec.complete"(%arg137, %320) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%321) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_3", sym_visibility = "private"}> ({
    ^bb0(%arg135: !runtime.scope, %arg136: ui64):
      %310 = "exec.boolean"(%arg135) <{site = "s7", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%310)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%311: i1):  // pred: ^bb0
      %312 = "exec.complete"(%arg135, %311) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%312) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%313: !exec.stop):  // pred: ^bb0
      %314 = "exec.failed"(%313) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%314) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_4", sym_visibility = "private"}> ({
    ^bb0(%arg132: !runtime.scope, %arg133: !data.field_vector<"bls12-381.fr">, %arg134: ui64):
      %299 = "exec.apply"(%arg132, %arg133) <{binding = @zkl_binding_1, parameters = [], site = "s12"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%299)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%300: ui64):  // pred: ^bb0
      %301 = "exec.apply"(%arg132, %300, %arg134) <{binding = @zkl_binding_2, parameters = [], site = "s13"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%301)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%302: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %303 = "exec.failed"(%302) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%303) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%304: ui64):  // pred: ^bb1
      %305 = "exec.apply"(%arg132) <{binding = @zkl_binding_0, parameters = [0 : ui64], site = "s14"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%305)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%306: ui64):  // pred: ^bb3
      %307 = "exec.apply"(%arg132, %304, %306) <{binding = @zkl_binding_3, parameters = [], site = "s15"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%307)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb5(%308: i1):  // pred: ^bb4
      %309 = "exec.complete"(%arg132, %308) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%309) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_5", sym_visibility = "private"}> ({
    ^bb0(%arg129: !runtime.scope, %arg130: !data.field_vector<"bls12-381.fr">, %arg131: ui64):
      %294 = "exec.boolean"(%arg129) <{site = "s17", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%294)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%295: i1):  // pred: ^bb0
      %296 = "exec.complete"(%arg129, %295) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%296) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%297: !exec.stop):  // pred: ^bb0
      %298 = "exec.failed"(%297) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%298) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_6", sym_visibility = "private"}> ({
    ^bb0(%arg125: !runtime.scope, %arg126: !data.field_vector<"bls12-381.fr">, %arg127: ui64, %arg128: ui64):
      %283 = "exec.apply"(%arg125, %arg126) <{binding = @zkl_binding_1, parameters = [], site = "s23"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%283)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%284: ui64):  // pred: ^bb0
      %285 = "exec.apply"(%arg125, %284, %arg128) <{binding = @zkl_binding_4, parameters = [], site = "s24"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%285)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%286: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %287 = "exec.failed"(%286) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%287) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%288: ui64):  // pred: ^bb1
      %289 = "func.call"(%arg125, %arg127) <{callee = @s3h7a6b6311h6d756c74696c696e6561724h726f7773}> {runtime.site = "s25"} : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%289)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%290: ui64):  // pred: ^bb3
      %291 = "exec.apply"(%arg125, %288, %290) <{binding = @zkl_binding_3, parameters = [], site = "s26"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%291)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb5(%292: i1):  // pred: ^bb4
      %293 = "exec.complete"(%arg125, %292) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%293) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_7", sym_visibility = "private"}> ({
    ^bb0(%arg121: !runtime.scope, %arg122: !data.field_vector<"bls12-381.fr">, %arg123: ui64, %arg124: ui64):
      %278 = "exec.boolean"(%arg121) <{site = "s28", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%278)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%279: i1):  // pred: ^bb0
      %280 = "exec.complete"(%arg121, %279) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%280) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%281: !exec.stop):  // pred: ^bb0
      %282 = "exec.failed"(%281) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%282) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "s3h7a6b637h696e64696365734h6c657373", sym_visibility = "private"}> ({
    ^bb0(%arg118: !runtime.scope, %arg119: ui64, %arg120: ui64):
      %273 = "exec.apply"(%arg118, %arg119, %arg120) <{binding = @zkl_binding_5, parameters = [], site = "s0"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%273)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%274: i1):  // pred: ^bb0
      %275 = "exec.returned"(%274) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%275) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%276: !exec.stop):  // pred: ^bb0
      %277 = "exec.failed"(%276) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%277) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.origin = ["s3h7a6b637h696e64696365734h6c657373", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "s3h7a6b6311h6d756c74696c696e6561724h726f7773", sym_visibility = "private"}> ({
    ^bb0(%arg116: !runtime.scope, %arg117: ui64):
      %226 = "exec.apply"(%arg116) <{binding = @zkl_binding_0, parameters = [64 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%226)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%227: ui64):  // pred: ^bb0
      %228 = "func.call"(%arg116, %arg117, %227) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s1"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%228)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%229: !exec.stop):  // 14 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12, ^bb14, ^bb15, ^bb19, ^bb21
      %230 = "exec.failed"(%229) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%230) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%231: i1):  // pred: ^bb1
      %232 = "exec.test"(%arg116, %231) <{site = "s2"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%232)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb4(%233: i1):  // pred: ^bb3
      "cf.cond_br"(%233)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %234 = "runtime.enter_scope"(%arg116) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s2"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%234)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %235 = "runtime.enter_scope"(%arg116) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s2"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%235)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // 2 preds: ^bb10, ^bb13
      %236 = "exec.apply"(%arg116) <{binding = @zkl_binding_0, parameters = [1 : ui64], site = "s3"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%236)[^bb14, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb8(%237: !runtime.scope):  // pred: ^bb5
      %238 = "func.call"(%237) <{callee = @zkl_control_8}> : (!runtime.scope) -> !exec.outcome<>
      %239 = "runtime.exit_scope"(%237, %238) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%239)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb9(%240: !runtime.transfer<>):  // pred: ^bb8
      %241 = "runtime.accept_transfer"(%arg116, %240) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%241)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb10:  // pred: ^bb9
      "cf.br"()[^bb7] : () -> ()
    ^bb11(%242: !runtime.scope):  // pred: ^bb6
      %243 = "func.call"(%242) <{callee = @zkl_control_9}> : (!runtime.scope) -> !exec.outcome<>
      %244 = "runtime.exit_scope"(%242, %243) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%244)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb12(%245: !runtime.transfer<>):  // pred: ^bb11
      %246 = "runtime.accept_transfer"(%arg116, %245) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%246)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb13:  // pred: ^bb12
      "cf.br"()[^bb7] : () -> ()
    ^bb14(%247: ui64):  // pred: ^bb7
      %248 = "exec.apply"(%arg116) <{binding = @zkl_binding_0, parameters = [0 : ui64], site = "s5"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%248)[^bb15, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb15(%249: ui64):  // pred: ^bb14
      %250 = "exec.range"(%arg116, %249, %arg117) <{site = "s6"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%250)[^bb16, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i64, i64)>) -> ()
    ^bb16(%251: i64, %252: i64):  // pred: ^bb15
      %253 = "runtime.borrow_transfer"(%arg116, %247) : (!runtime.scope, ui64) -> !runtime.transfer<(ui64)>
      "cf.br"(%251, %253)[^bb17] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb17(%254: i64, %255: !runtime.transfer<(ui64)>):  // 2 preds: ^bb16, ^bb20
      %256 = "arith.cmpi"(%254, %252) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%256, %255)[^bb18, ^bb19] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(ui64)>) -> ()
    ^bb18:  // pred: ^bb17
      %257 = "runtime.iteration"(%arg116, %254) <{site = "s6"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%257)[^bb22, ^bb21] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb19(%258: !runtime.transfer<(ui64)>):  // pred: ^bb17
      %259 = "runtime.accept_transfer"(%arg116, %258) : (!runtime.scope, !runtime.transfer<(ui64)>) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%259)[^bb25, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb20(%260: !runtime.transfer<(ui64)>):  // pred: ^bb24
      %261 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %262 = "arith.addi"(%254, %261) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%262, %260)[^bb17] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb21(%263: !exec.stop):  // 3 preds: ^bb18, ^bb22, ^bb23
      "runtime.release_transfer"(%255) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%263)[^bb2] : (!exec.stop) -> ()
    ^bb22(%264: ui64):  // pred: ^bb18
      %265 = "runtime.transfer_values"(%255) : (!runtime.transfer<(ui64)>) -> ui64
      %266 = "runtime.enter_scope"(%arg116, %254, %264, %265) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 2>, site = "s6"}> : (!runtime.scope, i64, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%266)[^bb23, ^bb21] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb23(%267: !runtime.scope):  // pred: ^bb22
      %268 = "func.call"(%267, %264, %265) <{callee = @zkl_control_10}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      %269 = "runtime.exit_scope"(%267, %268) : (!runtime.scope, !exec.outcome<(ui64)>) -> !exec.outcome<(!runtime.transfer<(ui64)>)>
      "exec.dispatch"(%269)[^bb24, ^bb21] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(ui64)>)>) -> ()
    ^bb24(%270: !runtime.transfer<(ui64)>):  // pred: ^bb23
      "runtime.release_transfer"(%255) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%270)[^bb20] : (!runtime.transfer<(ui64)>) -> ()
    ^bb25(%271: ui64):  // pred: ^bb19
      %272 = "exec.returned"(%271) : (ui64) -> !exec.outcome<(ui64)>
      "func.return"(%272) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561724h726f7773", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_8", sym_visibility = "private"}> ({
    ^bb0(%arg115: !runtime.scope):
      %225 = "exec.complete"(%arg115) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%225) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_9", sym_visibility = "private"}> ({
    ^bb0(%arg114: !runtime.scope):
      %222 = "exec.reject"(%arg114) <{reason = "reject", site = "s2_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%222)[^bb1] : (!exec.stop) -> ()
    ^bb1(%223: !exec.stop):  // pred: ^bb0
      %224 = "exec.failed"(%223) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%224) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "zkl_control_10", sym_visibility = "private"}> ({
    ^bb0(%arg111: !runtime.scope, %arg112: ui64, %arg113: ui64):
      %215 = "exec.apply"(%arg111) <{binding = @zkl_binding_0, parameters = [2 : ui64], site = "s7"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%215)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%216: ui64):  // pred: ^bb0
      %217 = "exec.apply"(%arg111, %arg113, %216) <{binding = @zkl_binding_6, parameters = [], site = "s8"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%217)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%218: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %219 = "exec.failed"(%218) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%219) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%220: ui64):  // pred: ^bb1
      %221 = "exec.complete"(%arg111, %220) : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "func.return"(%221) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_c0a3a2b8b5f989e0e9c138a171631d20dc8bd296769b6ee7636d2d79a8518ba0", sym_visibility = "private"}> ({
    ^bb0(%arg109: !runtime.scope, %arg110: !algebra.field<"bls12-381.fr">):
      %208 = "exec.apply"(%arg109) <{binding = @zkl_binding_7, parameters = [], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%208)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%209: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %210 = "exec.apply"(%arg109) <{binding = @zkl_binding_8, parameters = [], site = "s1_create_0"}> : (!runtime.scope) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">)>
      "exec.dispatch"(%210)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">)>) -> ()
    ^bb2(%211: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %212 = "exec.failed"(%211) : (!exec.stop) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%212) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb3(%213: !runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">):  // pred: ^bb1
      %214 = "exec.returned"(%213, %209, %arg110) : (!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%214) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s8h73756d636865636b7h70656e64696e67", []]} : () -> ()
    "protocol.func"() <{contracts = [["input", "shape", [@zkl_8c866415d5a42d7cb60d6b39dd52568c20001248a901906f13a3d5d9dd8f74ac, [["input", 0, "role00000000"], ["input", 1, "role00000000"], ["input", 2, "role00000000"]]], unit, unit], ["continuation", "initial_sum", [@zkl_f03c5af270c09f9d5e832cdb0dc1d71151cebecfaaa08c6cacd997dde03860e9, [["input", 0, "role00000000"], ["input", 1, "role00000000"], ["input", 2, "role00000000"], ["input", 4, "role00000001"], ["input", 5, "role00000001"]]], [@zkl_f03c5af270c09f9d5e832cdb0dc1d71151cebecfaaa08c6cacd997dde03860e9, [["input", 0, "role00000000"], ["input", 1, "role00000000"], ["input", 2, "role00000000"], ["output", 5, "role00000001"], ["output", 6, "role00000001"]]], unit]], function_type = (!data.field_vector<"bls12-381.fr">, ui64, ui64, !runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, ui64, !runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), input_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"], ["role00000001"], ["role00000000", "role00000001"], ["role00000001"]], origin = ["sumcheck::Reduce", [["F", ["field", "bls12-381.fr"]], ["Max", ["nat", "2"]]]], output_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"], ["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5"}> ({
    ^bb0(%arg93: !data.field_vector<"bls12-381.fr">, %arg94: ui64, %arg95: ui64, %arg96: !runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, %arg97: !data.field_vector<"bls12-381.fr">, %arg98: !algebra.field<"bls12-381.fr">, %arg99: ui64, %arg100: !protocol.service_ref<"random.bls12-381.fr/0">):
      %179 = "func.call"(%arg93, %arg94, %arg95) <{callee = @zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %180 = "data.index"() <{value = 1 : ui64}> : () -> ui64
      %181 = "data.index_equal"(%179, %180) : (ui64, ui64) -> i1
      "protocol.guard"(%181) <{owner = "role00000000", site = "s3"}> : (i1) -> ()
      %182 = "func.call"(%arg93, %arg94, %arg95) <{callee = @zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %183 = "protocol.local_call"(%182, %arg99) <{callee = @s3h7a6b637h696e64696365734h6c657373, role = "role00000000", site = "s5"}> : (ui64, ui64) -> i1
      %184 = "arith.constant"() <{value = false}> : () -> i1
      %185 = "arith.cmpi"(%183, %184) <{predicate = 0 : i64}> : (i1, i1) -> i1
      "protocol.guard"(%185) <{owner = "role00000000", site = "s8"}> : (i1) -> ()
      %186 = "protocol.local_call"() <{callee = @zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f, role = "role00000000", site = "s10"}> : () -> !data.field_vector<"bls12-381.fr">
      %187:2 = "protocol.local_call"(%arg96, %arg97, %arg98) <{callee = @zkl_e8df957aab384c1d5416600c13a571512206e97abfbf6e0e9cddac5c84860d07, role = "role00000001", site = "s12"}> : (!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %188:6 = "protocol.repeat"(%arg99, %arg93, %arg94, %arg95, %186, %187#0, %187#1, %arg100) <{carried = 6 : i64, carried_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"]], maximum = 2 : i64, roles = ["role00000000", "role00000001"], site = "s18"}> ({
      ^bb0(%arg101: ui64, %arg102: !data.field_vector<"bls12-381.fr">, %arg103: ui64, %arg104: ui64, %arg105: !data.field_vector<"bls12-381.fr">, %arg106: !data.field_vector<"bls12-381.fr">, %arg107: !algebra.field<"bls12-381.fr">, %arg108: !protocol.service_ref<"random.bls12-381.fr/0">):
        %190:2 = "protocol.local_call"(%arg102, %arg103, %arg104) <{callee = @zkl_532a609cf36a935835501ca51308940142121e647ca360843a880bf231f04aa6, role = "role00000000", site = "s19"}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %191 = "protocol.exchange"(%190#0) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %192 = "protocol.restrict_roles"(%191) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %193 = "protocol.exchange"(%190#1) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_1"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %194 = "protocol.restrict_roles"(%193) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %195 = "algebra.field_add"(%192, %194) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %196 = "algebra.field_equal"(%arg107, %195) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
        "protocol.guard"(%196) <{owner = "role00000001", site = "s27"}> : (i1) -> ()
        %197 = "protocol.query"(%arg108) <{method = "draw", owner = "role00000001", site = "label_6368616c6c656e6765"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
        %198 = "protocol.exchange"(%197) <{receiver = "role00000000", sender = "role00000001", site = "label_64656c6976657279_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %199 = "protocol.restrict_roles"(%198) <{roles = ["role00000000"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %200:3 = "protocol.local_call"(%arg102, %arg103, %arg104, %199) <{callee = @zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d, role = "role00000000", site = "s32"}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> (!data.field_vector<"bls12-381.fr">, ui64, ui64)
        %201 = "protocol.local_call"(%arg105, %199) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000000", site = "s34"}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !data.field_vector<"bls12-381.fr">
        %202 = "protocol.local_call"(%arg106, %197) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000001", site = "s36"}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !data.field_vector<"bls12-381.fr">
        %203 = "algebra.constant"() <{value = #algebra.literal<<"bls12-381.fr">, 1 : ui255> : !algebra.field<"bls12-381.fr">}> : () -> !algebra.field<"bls12-381.fr">
        %204 = "algebra.field_subtract"(%203, %197) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %205 = "algebra.field_multiply"(%204, %192) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %206 = "algebra.field_multiply"(%197, %194) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %207 = "algebra.field_add"(%205, %206) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        "protocol.yield"(%200#0, %200#1, %200#2, %201, %202, %207) : (!data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
      }) : (ui64, !data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %189:3 = "protocol.local_call"(%188#4, %188#5) <{callee = @zkl_c36a2d2c6bd38573735fb9b90d1a3848c562d2c1f688234e2b669408e9c9eea9, role = "role00000001", site = "s48"}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      "protocol.return"(%188#3, %188#0, %188#1, %188#2, %189#0, %189#1, %189#2) : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, ui64, !runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> i1, sym_name = "zkf_326ab2331715c62ba21cb6a967c927ba6ad7f7f2da5e84eb0e5de0fc610f26ca", sym_visibility = "private"}> ({
    ^bb0(%arg90: !data.field_vector<"bls12-381.fr">, %arg91: ui64, %arg92: ui64):
      %171 = "func.call"(%arg90, %arg91, %arg92) <{callee = @zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %172 = "data.index"() <{value = 1 : ui64}> : () -> ui64
      %173 = "data.index_equal"(%171, %172) : (ui64, ui64) -> i1
      %174 = "func.call"(%arg90, %arg91, %arg92) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !data.field_vector<"bls12-381.fr">
      %175 = "data.dim"(%174) <{axis = 0 : i64}> : (!data.field_vector<"bls12-381.fr">) -> ui64
      %176 = "func.call"(%arg90, %arg91, %arg92) <{callee = @zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %177 = "data.index_power_of_two"(%175, %176) : (ui64, ui64) -> i1
      %178 = "arith.andi"(%173, %177) : (i1, i1) -> i1
      "func.return"(%178) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64, sym_name = "zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275", sym_visibility = "private"}> ({
    ^bb0(%arg87: !data.field_vector<"bls12-381.fr">, %arg88: ui64, %arg89: ui64):
      "func.return"(%arg89) : (ui64) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !data.field_vector<"bls12-381.fr">, sym_name = "zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", sym_visibility = "private"}> ({
    ^bb0(%arg84: !data.field_vector<"bls12-381.fr">, %arg85: ui64, %arg86: ui64):
      "func.return"(%arg84) : (!data.field_vector<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64, sym_name = "zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94", sym_visibility = "private"}> ({
    ^bb0(%arg81: !data.field_vector<"bls12-381.fr">, %arg82: ui64, %arg83: ui64):
      "func.return"(%arg82) : (ui64) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "zkf_c51d11bf318ad26bc2fce7b89eec63f85b98f57e91e0e9e6256f84a573b5b6e6", sym_visibility = "private"}> ({
    ^bb0(%arg76: !data.field_vector<"bls12-381.fr">, %arg77: ui64, %arg78: ui64, %arg79: !data.field_vector<"bls12-381.fr">, %arg80: !algebra.field<"bls12-381.fr">):
      %167 = "func.call"(%arg76, %arg77, %arg78) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !data.field_vector<"bls12-381.fr">
      %168 = "algebra.multilinear_restrict_prefix"(%167, %arg79) : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !data.field_vector<"bls12-381.fr">
      %169 = "func.call"(%168) <{callee = @zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e}> : (!data.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %170 = "algebra.field_equal"(%arg80, %169) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "func.return"(%170) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", sym_visibility = "private"}> ({
    ^bb0(%arg75: !runtime.scope):
      %162 = "exec.apply"(%arg75) <{binding = @zkl_binding_7, parameters = [], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%162)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%163: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %164 = "exec.returned"(%163) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%164) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%165: !exec.stop):  // pred: ^bb0
      %166 = "exec.failed"(%165) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%166) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6310h7072696d6974697665736h766563746f725h656d707479", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_e8df957aab384c1d5416600c13a571512206e97abfbf6e0e9cddac5c84860d07", sym_visibility = "private"}> ({
    ^bb0(%arg71: !runtime.scope, %arg72: !runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, %arg73: !data.field_vector<"bls12-381.fr">, %arg74: !algebra.field<"bls12-381.fr">):
      %158 = "exec.apply"(%arg71, %arg72) <{binding = @zkl_binding_9, parameters = [], site = "s0_unpack_0"}> : (!runtime.scope, !runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">) -> !exec.outcome<>
      "exec.dispatch"(%158)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb1:  // pred: ^bb0
      %159 = "exec.returned"(%arg73, %arg74) : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%159) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%160: !exec.stop):  // pred: ^bb0
      %161 = "exec.failed"(%160) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%161) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s8h73756d636865636b10h6f70656e5f636c61696d", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_532a609cf36a935835501ca51308940142121e647ca360843a880bf231f04aa6", sym_visibility = "private"}> ({
    ^bb0(%arg67: !runtime.scope, %arg68: !data.field_vector<"bls12-381.fr">, %arg69: ui64, %arg70: ui64):
      %148 = "func.call"(%arg67, %arg68, %arg69, %arg70) <{callee = @zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087}> {runtime.site = "s0"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%148)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%149: !data.field_vector<"bls12-381.fr">, %150: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %151 = "exec.apply"(%arg67, %149) <{binding = @zkl_binding_10, parameters = [], site = "s3"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%151)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%152: !exec.stop):  // 3 preds: ^bb0, ^bb1, ^bb3
      %153 = "exec.failed"(%152) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%153) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb3(%154: !algebra.field<"bls12-381.fr">):  // pred: ^bb1
      %155 = "exec.apply"(%arg67, %150) <{binding = @zkl_binding_10, parameters = [], site = "s5"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%155)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb4(%156: !algebra.field<"bls12-381.fr">):  // pred: ^bb3
      %157 = "exec.returned"(%154, %156) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%157) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s8h73756d636865636b4h73756d73", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087", sym_visibility = "private"}> ({
    ^bb0(%arg63: !runtime.scope, %arg64: !data.field_vector<"bls12-381.fr">, %arg65: ui64, %arg66: ui64):
      %124 = "exec.apply"(%arg63) <{binding = @zkl_binding_0, parameters = [0 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%124)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%125: ui64):  // pred: ^bb0
      %126 = "func.call"(%arg63, %125, %arg65) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s2"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%126)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%127: !exec.stop):  // 10 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12
      %128 = "exec.failed"(%127) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "func.return"(%128) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%129: i1):  // pred: ^bb1
      %130 = "exec.test"(%arg63, %129) <{site = "s3"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%130)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb4(%131: i1):  // pred: ^bb3
      "cf.cond_br"(%131)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %132 = "runtime.enter_scope"(%arg63) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s3"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%132)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %133 = "runtime.enter_scope"(%arg63) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s3"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%133)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // 2 preds: ^bb10, ^bb13
      %134 = "exec.apply"(%arg63, %arg64) <{binding = @zkl_binding_11, parameters = [], site = "s5"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%134)[^bb14, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%135: !runtime.scope):  // pred: ^bb5
      %136 = "func.call"(%135) <{callee = @zkl_control_11}> : (!runtime.scope) -> !exec.outcome<>
      %137 = "runtime.exit_scope"(%135, %136) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%137)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb9(%138: !runtime.transfer<>):  // pred: ^bb8
      %139 = "runtime.accept_transfer"(%arg63, %138) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%139)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb10:  // pred: ^bb9
      "cf.br"()[^bb7] : () -> ()
    ^bb11(%140: !runtime.scope):  // pred: ^bb6
      %141 = "func.call"(%140) <{callee = @zkl_control_12}> : (!runtime.scope) -> !exec.outcome<>
      %142 = "runtime.exit_scope"(%140, %141) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%142)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb12(%143: !runtime.transfer<>):  // pred: ^bb11
      %144 = "runtime.accept_transfer"(%arg63, %143) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%144)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb13:  // pred: ^bb12
      "cf.br"()[^bb7] : () -> ()
    ^bb14(%145: !data.field_vector<"bls12-381.fr">, %146: !data.field_vector<"bls12-381.fr">):  // pred: ^bb7
      %147 = "exec.returned"(%145, %146) : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "func.return"(%147) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561726h68616c766573", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_11", sym_visibility = "private"}> ({
    ^bb0(%arg62: !runtime.scope):
      %123 = "exec.complete"(%arg62) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%123) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_12", sym_visibility = "private"}> ({
    ^bb0(%arg61: !runtime.scope):
      %120 = "exec.reject"(%arg61) <{reason = "reject", site = "s3_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%120)[^bb1] : (!exec.stop) -> ()
    ^bb1(%121: !exec.stop):  // pred: ^bb0
      %122 = "exec.failed"(%121) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%122) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d", sym_visibility = "private"}> ({
    ^bb0(%arg56: !runtime.scope, %arg57: !data.field_vector<"bls12-381.fr">, %arg58: ui64, %arg59: ui64, %arg60: !algebra.field<"bls12-381.fr">):
      %108 = "func.call"(%arg56, %arg57, %arg58, %arg59) <{callee = @zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087}> {runtime.site = "s0"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%108)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%109: !data.field_vector<"bls12-381.fr">, %110: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %111 = "exec.collect"(%arg56, %109, %110, %arg60) <{body = @zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body, domain = @zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_domain, site = "s4"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%111)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%112: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %113 = "exec.failed"(%112) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%113) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb3(%114: !data.field_vector<"bls12-381.fr">):  // pred: ^bb1
      %115 = "exec.apply"(%arg56) <{binding = @zkl_binding_0, parameters = [1 : ui64], site = "s7"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%115)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%116: ui64):  // pred: ^bb3
      %117 = "exec.apply"(%arg56, %arg58, %116) <{binding = @zkl_binding_12, parameters = [], site = "s8"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%117)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%118: ui64):  // pred: ^bb4
      %119 = "exec.returned"(%114, %118, %arg59) : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%119) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561729h6669785f6669727374", []]} : () -> ()
    "data.domain"() <{function_type = (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, sym_name = "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_domain", sym_visibility = "private"}> ({
    ^bb0(%arg54: !data.field_vector<"bls12-381.fr">, %arg55: !data.field_vector<"bls12-381.fr">):
      %105 = "data.domain_elements"(%arg54) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %106 = "data.domain_elements"(%arg55) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %107 = "data.domain_zip"(%105, %106) : (!data.domain<!algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%107) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body", sym_visibility = "private"}> ({
    ^bb0(%arg48: !runtime.scope, %arg49: !algebra.field<"bls12-381.fr">, %arg50: !algebra.field<"bls12-381.fr">, %arg51: !data.field_vector<"bls12-381.fr">, %arg52: !data.field_vector<"bls12-381.fr">, %arg53: !algebra.field<"bls12-381.fr">):
      %100 = "exec.compute"(%arg48, %arg49, %arg50, %arg53) <{callee = @zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5, site = "body"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%100)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%101: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %102 = "exec.returned"(%101) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%102) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%103: !exec.stop):  // pred: ^bb0
      %104 = "exec.failed"(%103) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%104) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5", sym_visibility = "private"}> ({
    ^bb0(%arg45: !algebra.field<"bls12-381.fr">, %arg46: !algebra.field<"bls12-381.fr">, %arg47: !algebra.field<"bls12-381.fr">):
      %97 = "algebra.field_subtract"(%arg46, %arg45) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %98 = "algebra.field_multiply"(%97, %arg47) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %99 = "algebra.field_add"(%arg45, %98) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%99) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", sym_visibility = "private"}> ({
    ^bb0(%arg42: !runtime.scope, %arg43: !data.field_vector<"bls12-381.fr">, %arg44: !algebra.field<"bls12-381.fr">):
      %92 = "exec.apply"(%arg42, %arg43, %arg44) <{binding = @zkl_binding_13, parameters = [], site = "s0"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%92)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%93: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %94 = "exec.returned"(%93) : (!data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%94) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%95: !exec.stop):  // pred: ^bb0
      %96 = "exec.failed"(%95) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "func.return"(%96) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6310h7072696d6974697665736h766563746f726h617070656e64", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_c36a2d2c6bd38573735fb9b90d1a3848c562d2c1f688234e2b669408e9c9eea9", sym_visibility = "private"}> ({
    ^bb0(%arg39: !runtime.scope, %arg40: !data.field_vector<"bls12-381.fr">, %arg41: !algebra.field<"bls12-381.fr">):
      %87 = "exec.apply"(%arg39) <{binding = @zkl_binding_8, parameters = [], site = "s0_create_0"}> : (!runtime.scope) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">)>
      "exec.dispatch"(%87)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">)>) -> ()
    ^bb1(%88: !runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">):  // pred: ^bb0
      %89 = "exec.returned"(%88, %arg40, %arg41) : (!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%89) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%90: !exec.stop):  // pred: ^bb0
      %91 = "exec.failed"(%90) : (!exec.stop) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%91) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s8h73756d636865636b9h61745f707265666978", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc", sym_visibility = "private"}> ({
    ^bb0(%arg34: !runtime.scope, %arg35: !data.field_vector<"bls12-381.fr">, %arg36: !runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">, %arg37: !data.field_vector<"bls12-381.fr">, %arg38: !algebra.field<"bls12-381.fr">):
      %60 = "exec.apply"(%arg34, %arg36) <{binding = @zkl_binding_9, parameters = [], site = "s0_unpack_0"}> : (!runtime.scope, !runtime.capability<resource_unit, "zkl_resource_924693d979af232703fc6e9fd8f77bb89ef5ead67a2d4c10d4a54c14b3839992">) -> !exec.outcome<>
      "exec.dispatch"(%60)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb1:  // pred: ^bb0
      %61 = "exec.apply"(%arg34, %arg37) <{binding = @zkl_binding_1, parameters = [], site = "s3"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%61)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%62: !exec.stop):  // 11 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb7, ^bb8, ^bb10, ^bb11, ^bb13, ^bb14
      %63 = "exec.failed"(%62) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%63) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%64: ui64):  // pred: ^bb1
      %65 = "exec.apply"(%arg34) <{binding = @zkl_binding_0, parameters = [1 : ui64], site = "s4"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%65)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%66: ui64):  // pred: ^bb3
      %67 = "func.call"(%arg34, %arg35, %64, %66) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655}> {runtime.site = "s5"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%67)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb5(%68: i1):  // pred: ^bb4
      %69 = "exec.test"(%arg34, %68) <{site = "s9"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%69)[^bb6, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb6(%70: i1):  // pred: ^bb5
      "cf.cond_br"(%70)[^bb7, ^bb8] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb7:  // pred: ^bb6
      %71 = "runtime.enter_scope"(%arg34, %arg35, %arg37, %arg38) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "then", site = "s9"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%71)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb8:  // pred: ^bb6
      %72 = "runtime.enter_scope"(%arg34, %arg35, %arg37, %arg38) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "else", site = "s9"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%72)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb9(%73: i1):  // 2 preds: ^bb12, ^bb15
      %74 = "exec.returned"(%73) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%74) : (!exec.outcome<(i1)>) -> ()
    ^bb10(%75: !runtime.scope):  // pred: ^bb7
      %76 = "func.call"(%75, %arg35, %arg37, %arg38) <{callee = @zkl_control_13}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>
      %77 = "runtime.exit_scope"(%75, %76) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%77)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb11(%78: !runtime.transfer<(i1)>):  // pred: ^bb10
      %79 = "runtime.accept_transfer"(%arg34, %78) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%79)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb12(%80: i1):  // pred: ^bb11
      "cf.br"(%80)[^bb9] : (i1) -> ()
    ^bb13(%81: !runtime.scope):  // pred: ^bb8
      %82 = "func.call"(%81, %arg35, %arg37, %arg38) <{callee = @zkl_control_14}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>
      %83 = "runtime.exit_scope"(%81, %82) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%83)[^bb14, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb14(%84: !runtime.transfer<(i1)>):  // pred: ^bb13
      %85 = "runtime.accept_transfer"(%arg34, %84) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%85)[^bb15, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb15(%86: i1):  // pred: ^bb14
      "cf.br"(%86)[^bb9] : (i1) -> ()
    }) {runtime.origin = ["s8h73756d636865636b5h636865636b", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_13", sym_visibility = "private"}> ({
    ^bb0(%arg30: !runtime.scope, %arg31: !data.field_vector<"bls12-381.fr">, %arg32: !data.field_vector<"bls12-381.fr">, %arg33: !algebra.field<"bls12-381.fr">):
      %55 = "func.call"(%arg30, %arg31, %arg32, %arg33) <{callee = @zkl_967e003dd39c9e1730d1e9e543081e08e351228ff07f85fb14e1e88dbded8a99}> {runtime.site = "s12"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>
      "exec.dispatch"(%55)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%56: i1):  // pred: ^bb0
      %57 = "exec.complete"(%arg30, %56) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%57) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%58: !exec.stop):  // pred: ^bb0
      %59 = "exec.failed"(%58) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%59) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_14", sym_visibility = "private"}> ({
    ^bb0(%arg26: !runtime.scope, %arg27: !data.field_vector<"bls12-381.fr">, %arg28: !data.field_vector<"bls12-381.fr">, %arg29: !algebra.field<"bls12-381.fr">):
      %50 = "exec.boolean"(%arg26) <{site = "s14", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%50)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%51: i1):  // pred: ^bb0
      %52 = "exec.complete"(%arg26, %51) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%52) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%53: !exec.stop):  // pred: ^bb0
      %54 = "exec.failed"(%53) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%54) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_967e003dd39c9e1730d1e9e543081e08e351228ff07f85fb14e1e88dbded8a99", sym_visibility = "private"}> ({
    ^bb0(%arg22: !runtime.scope, %arg23: !data.field_vector<"bls12-381.fr">, %arg24: !data.field_vector<"bls12-381.fr">, %arg25: !algebra.field<"bls12-381.fr">):
      %29 = "exec.apply"(%arg22, %arg24) <{binding = @zkl_binding_1, parameters = [], site = "s0"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%29)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%30: ui64):  // pred: ^bb0
      %31 = "exec.apply"(%arg22) <{binding = @zkl_binding_0, parameters = [1 : ui64], site = "s1"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%31)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%32: !exec.stop):  // 7 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7
      %33 = "exec.failed"(%32) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%33) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%34: ui64):  // pred: ^bb1
      %35 = "func.call"(%arg22, %arg23, %30, %34) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a}> {runtime.site = "s2"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%35)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb4(%36: !data.field_vector<"bls12-381.fr">, %37: ui64, %38: ui64):  // pred: ^bb3
      %39 = "func.call"(%arg22, %36, %37, %38, %arg24) <{callee = @zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be}> {runtime.site = "s4"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%39)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb5(%40: !data.field_vector<"bls12-381.fr">, %41: ui64, %42: ui64):  // pred: ^bb4
      %43 = "exec.compute"(%arg22, %40, %41, %42) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33, site = "s6"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%43)[^bb6, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb6(%44: !data.field_vector<"bls12-381.fr">):  // pred: ^bb5
      %45 = "exec.apply"(%arg22, %44) <{binding = @zkl_binding_10, parameters = [], site = "s7"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%45)[^bb7, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb7(%46: !algebra.field<"bls12-381.fr">):  // pred: ^bb6
      %47 = "exec.apply"(%arg22, %46, %arg25) <{binding = @zkl_binding_14, parameters = [], site = "s8"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>
      "exec.dispatch"(%47)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb8(%48: i1):  // pred: ^bb7
      %49 = "exec.returned"(%48) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%49) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.origin = ["s8h73756d636865636b11h636865636b5f7461626c65", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be", sym_visibility = "private"}> ({
    ^bb0(%arg17: !runtime.scope, %arg18: !data.field_vector<"bls12-381.fr">, %arg19: ui64, %arg20: ui64, %arg21: !data.field_vector<"bls12-381.fr">):
      %22 = "func.call"(%arg17, %arg18, %arg19, %arg20, %arg21) <{callee = @zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2}> {runtime.site = "s0"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%22)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb1(%23: !data.field_vector<"bls12-381.fr">, %24: ui64, %25: ui64):  // pred: ^bb0
      %26 = "exec.returned"(%23, %24, %25) : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%26) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb2(%27: !exec.stop):  // pred: ^bb0
      %28 = "exec.failed"(%27) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%28) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e65617210h6669785f707265666978", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_195a79478f48dffc2a6917273d8317df0fabae786920a46fa2ac6b2737144299", sym_visibility = "private"}> ({
    ^bb0(%arg12: !runtime.scope, %arg13: !data.field_vector<"bls12-381.fr">, %arg14: ui64, %arg15: ui64, %arg16: !algebra.field<"bls12-381.fr">):
      %15 = "func.call"(%arg12, %arg13, %arg14, %arg15, %arg16) <{callee = @zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d}> {runtime.site = "s2"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%15)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb1(%16: !data.field_vector<"bls12-381.fr">, %17: ui64, %18: ui64):  // pred: ^bb0
      %19 = "exec.returned"(%16, %17, %18) : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%19) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb2(%20: !exec.stop):  // pred: ^bb0
      %21 = "exec.failed"(%20) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%21) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["zks_50b2228592370f9a2bce2e71277fbb9bf36d691d6ece4416923708e3a0c063ae", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2", sym_visibility = "private"}> ({
    ^bb0(%arg7: !runtime.scope, %arg8: !data.field_vector<"bls12-381.fr">, %arg9: ui64, %arg10: ui64, %arg11: !data.field_vector<"bls12-381.fr">):
      %8 = "exec.fold"(%arg7, %arg11, %arg8, %arg9, %arg10) <{domain = @finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_domain, site = "s0", step = @finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%8)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb1(%9: !data.field_vector<"bls12-381.fr">, %10: ui64, %11: ui64):  // pred: ^bb0
      %12 = "exec.returned"(%9, %10, %11) : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%12) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb2(%13: !exec.stop):  // pred: ^bb0
      %14 = "exec.failed"(%13) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%14) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg6: !data.field_vector<"bls12-381.fr">):
      %7 = "data.domain_elements"(%arg6) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%7) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg0: !runtime.scope, %arg1: !data.field_vector<"bls12-381.fr">, %arg2: ui64, %arg3: ui64, %arg4: !algebra.field<"bls12-381.fr">, %arg5: !data.field_vector<"bls12-381.fr">):
      %0 = "func.call"(%arg0, %arg1, %arg2, %arg3, %arg4) <{callee = @zkl_195a79478f48dffc2a6917273d8317df0fabae786920a46fa2ac6b2737144299}> {runtime.site = "body"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb1(%1: !data.field_vector<"bls12-381.fr">, %2: ui64, %3: ui64):  // pred: ^bb0
      %4 = "exec.returned"(%1, %2, %3) : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%4) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb2(%5: !exec.stop):  // pred: ^bb0
      %6 = "exec.failed"(%5) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%6) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body", []]} : () -> ()
    "relation.declare"() <{formula = @zkf_9ca6c98faa0d00ed80eb608a89db1544ad71443a8944af6ac99e6fd78cb3660b, key = "zkl_733a9984be750c90a7e40f8fc81c10a284cb9ecaf745c62024f07f1a3806a10c", kind = "zkc.language.formula/0", purposes = ["parameter", "parameter"], revision = "d94f5d42db69c800d9b707fca6571d5aa62c317acd9eb209e8b27d117a5285da", signature = (!data.field_vector<"bls12-381.fr">, ui64) -> i1, static_arguments = [], sym_name = "zkl_733a9984be750c90a7e40f8fc81c10a284cb9ecaf745c62024f07f1a3806a10c"}> : () -> ()
    "relation.declare"() <{formula = @zkf_116f3285742dd1275b8149c69b78a6713cd6256a8af715be7c346da1c793a766, key = "zkl_1c2e12f894c2f4b39d38adc87f1dedbaf7856eb6985dba89eb2261c88030aef2", kind = "zkc.language.formula/0", purposes = ["parameter", "statement"], revision = "57d17255e158ced9416cb3888c3f005f4e17bae102e66f5a117b3a000b9306da", signature = (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, static_arguments = [], sym_name = "zkl_1c2e12f894c2f4b39d38adc87f1dedbaf7856eb6985dba89eb2261c88030aef2"}> : () -> ()
    "relation.declare"() <{formula = @zkf_326ab2331715c62ba21cb6a967c927ba6ad7f7f2da5e84eb0e5de0fc610f26ca, key = "zkl_8c866415d5a42d7cb60d6b39dd52568c20001248a901906f13a3d5d9dd8f74ac", kind = "zkc.language.formula/0", purposes = ["parameter", "parameter", "parameter"], revision = "38b907e02d60bf6870a7d7cd7dfb2c81fa0a4e067cdcc1138f99aed00da6eaed", signature = (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> i1, static_arguments = [], sym_name = "zkl_8c866415d5a42d7cb60d6b39dd52568c20001248a901906f13a3d5d9dd8f74ac"}> : () -> ()
    "relation.declare"() <{formula = @zkf_c51d11bf318ad26bc2fce7b89eec63f85b98f57e91e0e9e6256f84a573b5b6e6, key = "zkl_f03c5af270c09f9d5e832cdb0dc1d71151cebecfaaa08c6cacd997dde03860e9", kind = "zkc.language.formula/0", purposes = ["parameter", "parameter", "parameter", "statement", "statement"], revision = "569415ff287b072bbe1e4e48bfd0f722b01ceaa00a0c97dae52619ecafe372ae", signature = (!data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, static_arguments = [], sym_name = "zkl_f03c5af270c09f9d5e832cdb0dc1d71151cebecfaaa08c6cacd997dde03860e9"}> : () -> ()
  }) : () -> ()
}) : () -> ()

