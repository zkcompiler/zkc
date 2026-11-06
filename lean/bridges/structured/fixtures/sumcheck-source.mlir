"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>, source_declarations = [[[["nominal", "record", "zkc::multilinear::Table", [["field", "bls12-381.fr"]]], "ordinary", false, [["entries", ["builtin", "vector", [["field", "bls12-381.fr"]]], unit], ["dimensions", ["index"], unit], ["columns", ["index"], unit]], [], unit], [["nominal", "record", "sumcheck::Pending", [["field", "bls12-381.fr"]]], "linear", false, [["point", ["builtin", "vector", [["field", "bls12-381.fr"]]], unit], ["value", ["field", "bls12-381.fr"], unit]], [], "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6"]], [["zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", [["values", ["builtin", "vector", [["field", "bls12-381.fr"]]], ["role00000000", "role00000001"], 0 : ui64, 1 : ui64, ["data", ["role00000000", "role00000001"]]], ["claim", ["field", "bls12-381.fr"], ["role00000001"], 1 : ui64, 1 : ui64, ["data", ["role00000001"]]], ["rounds", ["index"], ["role00000000", "role00000001"], 2 : ui64, 1 : ui64, ["data", ["role00000000", "role00000001"]]]], [["accepted", ["bool"], ["role00000001"], 0 : ui64, 1 : ui64, ["data", ["role00000001"]]]]], ["zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", [["values", ["nominal", "record", "zkc::multilinear::Table", [["field", "bls12-381.fr"]]], ["role00000000"], 0 : ui64, 3 : ui64, ["data", ["role00000000"]]], ["claim", ["nominal", "record", "sumcheck::Pending", [["field", "bls12-381.fr"]]], ["role00000001"], 3 : ui64, 3 : ui64, ["data", ["role00000001"]]], ["rounds", ["index"], ["role00000000", "role00000001"], 6 : ui64, 1 : ui64, ["data", ["role00000000", "role00000001"]]]], [["point", ["builtin", "vector", [["field", "bls12-381.fr"]]], ["role00000000"], 0 : ui64, 1 : ui64, ["data", ["role00000000"]]], ["residual", ["nominal", "record", "zkc::multilinear::Table", [["field", "bls12-381.fr"]]], ["role00000000"], 1 : ui64, 3 : ui64, ["data", ["role00000000"]]], ["evaluation", ["nominal", "record", "sumcheck::Pending", [["field", "bls12-381.fr"]]], ["role00000001"], 4 : ui64, 3 : ui64, ["data", ["role00000001"]]]]]], [["sumcheck::Pending", "7755041130d6ceb96e647d78ac25f7e67d45df1d27871cb103399d282c063f61"], ["zkc::multilinear::Table", "8aa28c4604470c28369b6893e2527323f693924f66cd54f1701edee86bd6bf62"]]]}> ({
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "field.equal", function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>, implementation = "", sym_name = "zkl_binding_14"}> : () -> ()
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
    "protocol.func"() <{contracts = [["input", "shape", [@zkl_733a9984be750c90a7e40f8fc81c10a284cb9ecaf745c62024f07f1a3806a10c, [["input", 0, "role00000001"], ["input", 2, "role00000001"]]], unit, unit], ["target", "public_sum", [@zkl_1c2e12f894c2f4b39d38adc87f1dedbaf7856eb6985dba89eb2261c88030aef2, [["input", 0, "role00000001"], ["input", 1, "role00000001"]]], unit, ["output", 0, "role00000001"]]], function_type = (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> i1, input_roles = [["role00000000", "role00000001"], ["role00000001"], ["role00000000", "role00000001"], ["role00000001"]], origin = ["sumcheck::Sumcheck", [["F", ["field", "bls12-381.fr"]], ["Max", ["nat", "2"]]]], output_roles = [["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071"}> ({
    ^bb0(%arg168: !data.field_vector<"bls12-381.fr">, %arg169: !algebra.field<"bls12-381.fr">, %arg170: ui64, %arg171: !protocol.service_ref<"random.bls12-381.fr/0">):
      %419 = "data.index"() <{value = 1 : ui64}> : () -> ui64
      %420:3 = "protocol.local_call"(%arg168, %arg170, %419) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a, role = "role00000000", site = "s1"}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> (!data.field_vector<"bls12-381.fr">, ui64, ui64)
      %421:3 = "protocol.local_call"(%arg169) <{callee = @zkl_c0a3a2b8b5f989e0e9c138a171631d20dc8bd296769b6ee7636d2d79a8518ba0, role = "role00000001", site = "s3"}> : (!algebra.field<"bls12-381.fr">) -> (!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %422:7 = "protocol.apply"(%420#0, %420#1, %420#2, %421#0, %421#1, %421#2, %arg170, %arg171) <{callee = @zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5, roles = ["role00000000", "role00000001"], site = "label_726564756365"}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64, !runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, ui64, !runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %423 = "protocol.local_call"(%arg168, %422#4, %422#5, %422#6) <{callee = @zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc, role = "role00000001", site = "s9"}> : (!data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "protocol.return"(%423) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!data.field_vector<"bls12-381.fr">, ui64) -> i1, sym_name = "zkf_9ca6c98faa0d00ed80eb608a89db1544ad71443a8944af6ac99e6fd78cb3660b", sym_visibility = "private"}> ({
    ^bb0(%arg164: !data.field_vector<"bls12-381.fr">, %arg165: ui64):
      %411 = "data.dim"(%arg164) <{axis = 0 : i64}> : (!data.field_vector<"bls12-381.fr">) -> ui64
      %412 = "data.index_power_of_two"(%411, %arg165) : (ui64, ui64) -> i1
      %413 = "data.branch"(%412, %arg165) <{alternatives = ["then", "else"]}> ({
      ^bb0(%arg167: ui64):
        %415 = "data.index"() <{value = 2 : ui64}> : () -> ui64
        %416 = "data.index_less"(%415, %arg167) : (ui64, ui64) -> i1
        %417 = "arith.constant"() <{value = false}> : () -> i1
        %418 = "arith.cmpi"(%416, %417) <{predicate = 0 : i64}> : (i1, i1) -> i1
        "data.yield"(%418) : (i1) -> ()
      }, {
      ^bb0(%arg166: ui64):
        %414 = "arith.constant"() <{value = false}> : () -> i1
        "data.yield"(%414) : (i1) -> ()
      }) : (i1, ui64) -> i1
      "func.return"(%413) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "zkf_116f3285742dd1275b8149c69b78a6713cd6256a8af715be7c346da1c793a766", sym_visibility = "private"}> ({
    ^bb0(%arg162: !data.field_vector<"bls12-381.fr">, %arg163: !algebra.field<"bls12-381.fr">):
      %409 = "func.call"(%arg162) <{callee = @zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e}> : (!data.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %410 = "algebra.field_equal"(%arg163, %409) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "func.return"(%410) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!data.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e", sym_visibility = "private"}> ({
    ^bb0(%arg161: !data.field_vector<"bls12-381.fr">):
      %407 = "algebra.constant"() <{value = #algebra.literal<<"bls12-381.fr">, 0 : ui255> : !algebra.field<"bls12-381.fr">}> : () -> !algebra.field<"bls12-381.fr">
      %408 = "data.finite_fold"(%arg161, %407) <{domain = @finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_domain, step = @finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_body}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%408) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "data.domain"() <{function_type = (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_domain", sym_visibility = "private"}> ({
    ^bb0(%arg160: !data.field_vector<"bls12-381.fr">):
      %406 = "data.domain_elements"(%arg160) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%406) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_body", sym_visibility = "private"}> ({
    ^bb0(%arg157: !algebra.field<"bls12-381.fr">, %arg158: !algebra.field<"bls12-381.fr">, %arg159: !data.field_vector<"bls12-381.fr">):
      %405 = "func.call"(%arg157, %arg158) <{callee = @zkl_3fc17a64a5bb6e75192d0a1362e9954f0d434a10d0f93e319db6b516835a1005}> : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%405) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_3fc17a64a5bb6e75192d0a1362e9954f0d434a10d0f93e319db6b516835a1005", sym_visibility = "private"}> ({
    ^bb0(%arg155: !algebra.field<"bls12-381.fr">, %arg156: !algebra.field<"bls12-381.fr">):
      %404 = "algebra.field_add"(%arg155, %arg156) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%404) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", sym_visibility = "private"}> ({
    ^bb0(%arg151: !runtime.scope, %arg152: !data.field_vector<"bls12-381.fr">, %arg153: ui64, %arg154: ui64):
      %385 = "func.call"(%arg151, %arg152, %arg153, %arg154) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655}> {runtime.site = "s0"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%385)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%386: i1):  // pred: ^bb0
      %387 = "exec.test"(%arg151, %386) <{site = "s1"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%387)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%388: !exec.stop):  // 8 preds: ^bb0, ^bb1, ^bb4, ^bb5, ^bb7, ^bb8, ^bb10, ^bb11
      %389 = "exec.failed"(%388) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%389) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb3(%390: i1):  // pred: ^bb1
      "cf.cond_br"(%390)[^bb4, ^bb5] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb4:  // pred: ^bb3
      %391 = "runtime.enter_scope"(%arg151) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%391)[^bb7, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb5:  // pred: ^bb3
      %392 = "runtime.enter_scope"(%arg151) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%392)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // 2 preds: ^bb9, ^bb12
      %393 = "exec.returned"(%arg152, %arg153, %arg154) : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%393) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb7(%394: !runtime.scope):  // pred: ^bb4
      %395 = "func.call"(%394) <{callee = @zkl_control_0}> : (!runtime.scope) -> !exec.outcome<>
      %396 = "runtime.exit_scope"(%394, %395) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%396)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb8(%397: !runtime.transfer<>):  // pred: ^bb7
      %398 = "runtime.accept_transfer"(%arg151, %397) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%398)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb9:  // pred: ^bb8
      "cf.br"()[^bb6] : () -> ()
    ^bb10(%399: !runtime.scope):  // pred: ^bb5
      %400 = "func.call"(%399) <{callee = @zkl_control_1}> : (!runtime.scope) -> !exec.outcome<>
      %401 = "runtime.exit_scope"(%399, %400) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%401)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb11(%402: !runtime.transfer<>):  // pred: ^bb10
      %403 = "runtime.accept_transfer"(%arg151, %402) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%403)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb12:  // pred: ^bb11
      "cf.br"()[^bb6] : () -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561725h7461626c65", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_0", sym_visibility = "private"}> ({
    ^bb0(%arg150: !runtime.scope):
      %384 = "exec.complete"(%arg150) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%384) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_1", sym_visibility = "private"}> ({
    ^bb0(%arg149: !runtime.scope):
      %381 = "exec.reject"(%arg149) <{reason = "reject", site = "s1_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%381)[^bb1] : (!exec.stop) -> ()
    ^bb1(%382: !exec.stop):  // pred: ^bb0
      %383 = "exec.failed"(%382) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%383) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", sym_visibility = "private"}> ({
    ^bb0(%arg145: !runtime.scope, %arg146: !data.field_vector<"bls12-381.fr">, %arg147: ui64, %arg148: ui64):
      %323 = "exec.apply"(%arg145) <{binding = @zkl_binding_0, parameters = [0 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%323)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%324: ui64):  // pred: ^bb0
      %325 = "func.call"(%arg145, %324, %arg148) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s1"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%325)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%326: !exec.stop):  // 23 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12, ^bb15, ^bb16, ^bb17, ^bb18, ^bb19, ^bb21, ^bb22, ^bb25, ^bb26, ^bb28, ^bb29, ^bb31, ^bb32
      %327 = "exec.failed"(%326) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%327) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%328: i1):  // pred: ^bb1
      %329 = "exec.test"(%arg145, %328) <{site = "s3"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%329)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb4(%330: i1):  // pred: ^bb3
      "cf.cond_br"(%330)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %331 = "runtime.enter_scope"(%arg145, %arg147) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "then", site = "s3"}> : (!runtime.scope, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%331)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %332 = "runtime.enter_scope"(%arg145, %arg147) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "else", site = "s3"}> : (!runtime.scope, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%332)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7(%333: i1):  // 2 preds: ^bb10, ^bb13
      %334 = "exec.test"(%arg145, %333) <{site = "s11"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%334)[^bb14, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb8(%335: !runtime.scope):  // pred: ^bb5
      %336 = "func.call"(%335, %arg147) <{callee = @zkl_control_2}> : (!runtime.scope, ui64) -> !exec.outcome<(i1)>
      %337 = "runtime.exit_scope"(%335, %336) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%337)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb9(%338: !runtime.transfer<(i1)>):  // pred: ^bb8
      %339 = "runtime.accept_transfer"(%arg145, %338) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%339)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb10(%340: i1):  // pred: ^bb9
      "cf.br"(%340)[^bb7] : (i1) -> ()
    ^bb11(%341: !runtime.scope):  // pred: ^bb6
      %342 = "func.call"(%341, %arg147) <{callee = @zkl_control_3}> : (!runtime.scope, ui64) -> !exec.outcome<(i1)>
      %343 = "runtime.exit_scope"(%341, %342) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%343)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb12(%344: !runtime.transfer<(i1)>):  // pred: ^bb11
      %345 = "runtime.accept_transfer"(%arg145, %344) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%345)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb13(%346: i1):  // pred: ^bb12
      "cf.br"(%346)[^bb7] : (i1) -> ()
    ^bb14(%347: i1):  // pred: ^bb7
      "cf.cond_br"(%347)[^bb15, ^bb16] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb15:  // pred: ^bb14
      %348 = "runtime.enter_scope"(%arg145, %arg146, %arg148) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "then", site = "s11"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%348)[^bb18, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb16:  // pred: ^bb14
      %349 = "runtime.enter_scope"(%arg145, %arg146, %arg148) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "else", site = "s11"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%349)[^bb21, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb17(%350: i1):  // 2 preds: ^bb20, ^bb23
      %351 = "exec.test"(%arg145, %350) <{site = "s22"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%351)[^bb24, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb18(%352: !runtime.scope):  // pred: ^bb15
      %353 = "func.call"(%352, %arg146, %arg148) <{callee = @zkl_control_4}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>
      %354 = "runtime.exit_scope"(%352, %353) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%354)[^bb19, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb19(%355: !runtime.transfer<(i1)>):  // pred: ^bb18
      %356 = "runtime.accept_transfer"(%arg145, %355) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%356)[^bb20, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb20(%357: i1):  // pred: ^bb19
      "cf.br"(%357)[^bb17] : (i1) -> ()
    ^bb21(%358: !runtime.scope):  // pred: ^bb16
      %359 = "func.call"(%358, %arg146, %arg148) <{callee = @zkl_control_5}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>
      %360 = "runtime.exit_scope"(%358, %359) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%360)[^bb22, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb22(%361: !runtime.transfer<(i1)>):  // pred: ^bb21
      %362 = "runtime.accept_transfer"(%arg145, %361) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%362)[^bb23, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb23(%363: i1):  // pred: ^bb22
      "cf.br"(%363)[^bb17] : (i1) -> ()
    ^bb24(%364: i1):  // pred: ^bb17
      "cf.cond_br"(%364)[^bb25, ^bb26] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb25:  // pred: ^bb24
      %365 = "runtime.enter_scope"(%arg145, %arg146, %arg147, %arg148) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "then", site = "s22"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%365)[^bb28, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb26:  // pred: ^bb24
      %366 = "runtime.enter_scope"(%arg145, %arg146, %arg147, %arg148) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "else", site = "s22"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%366)[^bb31, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb27(%367: i1):  // 2 preds: ^bb30, ^bb33
      %368 = "exec.returned"(%367) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%368) : (!exec.outcome<(i1)>) -> ()
    ^bb28(%369: !runtime.scope):  // pred: ^bb25
      %370 = "func.call"(%369, %arg146, %arg147, %arg148) <{callee = @zkl_control_6}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      %371 = "runtime.exit_scope"(%369, %370) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%371)[^bb29, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb29(%372: !runtime.transfer<(i1)>):  // pred: ^bb28
      %373 = "runtime.accept_transfer"(%arg145, %372) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%373)[^bb30, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb30(%374: i1):  // pred: ^bb29
      "cf.br"(%374)[^bb27] : (i1) -> ()
    ^bb31(%375: !runtime.scope):  // pred: ^bb26
      %376 = "func.call"(%375, %arg146, %arg147, %arg148) <{callee = @zkl_control_7}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      %377 = "runtime.exit_scope"(%375, %376) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%377)[^bb32, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb32(%378: !runtime.transfer<(i1)>):  // pred: ^bb31
      %379 = "runtime.accept_transfer"(%arg145, %378) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%379)[^bb33, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb33(%380: i1):  // pred: ^bb32
      "cf.br"(%380)[^bb27] : (i1) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_2", sym_visibility = "private"}> ({
    ^bb0(%arg143: !runtime.scope, %arg144: ui64):
      %316 = "exec.apply"(%arg143) <{binding = @zkl_binding_0, parameters = [64 : ui64], site = "s4"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%316)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%317: ui64):  // pred: ^bb0
      %318 = "func.call"(%arg143, %arg144, %317) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s5"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%318)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%319: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %320 = "exec.failed"(%319) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%320) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%321: i1):  // pred: ^bb1
      %322 = "exec.complete"(%arg143, %321) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%322) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_3", sym_visibility = "private"}> ({
    ^bb0(%arg141: !runtime.scope, %arg142: ui64):
      %311 = "exec.boolean"(%arg141) <{site = "s7", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%311)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%312: i1):  // pred: ^bb0
      %313 = "exec.complete"(%arg141, %312) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%313) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%314: !exec.stop):  // pred: ^bb0
      %315 = "exec.failed"(%314) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%315) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_4", sym_visibility = "private"}> ({
    ^bb0(%arg138: !runtime.scope, %arg139: !data.field_vector<"bls12-381.fr">, %arg140: ui64):
      %300 = "exec.apply"(%arg138, %arg139) <{binding = @zkl_binding_1, parameters = [], site = "s12"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%300)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%301: ui64):  // pred: ^bb0
      %302 = "exec.apply"(%arg138, %301, %arg140) <{binding = @zkl_binding_2, parameters = [], site = "s13"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%302)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%303: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %304 = "exec.failed"(%303) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%304) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%305: ui64):  // pred: ^bb1
      %306 = "exec.apply"(%arg138) <{binding = @zkl_binding_0, parameters = [0 : ui64], site = "s14"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%306)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%307: ui64):  // pred: ^bb3
      %308 = "exec.apply"(%arg138, %305, %307) <{binding = @zkl_binding_3, parameters = [], site = "s15"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%308)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb5(%309: i1):  // pred: ^bb4
      %310 = "exec.complete"(%arg138, %309) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%310) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_5", sym_visibility = "private"}> ({
    ^bb0(%arg135: !runtime.scope, %arg136: !data.field_vector<"bls12-381.fr">, %arg137: ui64):
      %295 = "exec.boolean"(%arg135) <{site = "s17", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%295)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%296: i1):  // pred: ^bb0
      %297 = "exec.complete"(%arg135, %296) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%297) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%298: !exec.stop):  // pred: ^bb0
      %299 = "exec.failed"(%298) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%299) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_6", sym_visibility = "private"}> ({
    ^bb0(%arg131: !runtime.scope, %arg132: !data.field_vector<"bls12-381.fr">, %arg133: ui64, %arg134: ui64):
      %284 = "exec.apply"(%arg131, %arg132) <{binding = @zkl_binding_1, parameters = [], site = "s23"}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%284)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%285: ui64):  // pred: ^bb0
      %286 = "exec.apply"(%arg131, %285, %arg134) <{binding = @zkl_binding_4, parameters = [], site = "s24"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%286)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%287: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %288 = "exec.failed"(%287) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%288) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%289: ui64):  // pred: ^bb1
      %290 = "func.call"(%arg131, %arg133) <{callee = @s3h7a6b6311h6d756c74696c696e6561724h726f7773}> {runtime.site = "s25"} : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%290)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%291: ui64):  // pred: ^bb3
      %292 = "exec.apply"(%arg131, %289, %291) <{binding = @zkl_binding_3, parameters = [], site = "s26"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%292)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb5(%293: i1):  // pred: ^bb4
      %294 = "exec.complete"(%arg131, %293) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%294) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_7", sym_visibility = "private"}> ({
    ^bb0(%arg127: !runtime.scope, %arg128: !data.field_vector<"bls12-381.fr">, %arg129: ui64, %arg130: ui64):
      %279 = "exec.boolean"(%arg127) <{site = "s28", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%279)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%280: i1):  // pred: ^bb0
      %281 = "exec.complete"(%arg127, %280) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%281) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%282: !exec.stop):  // pred: ^bb0
      %283 = "exec.failed"(%282) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%283) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "s3h7a6b637h696e64696365734h6c657373", sym_visibility = "private"}> ({
    ^bb0(%arg124: !runtime.scope, %arg125: ui64, %arg126: ui64):
      %274 = "exec.apply"(%arg124, %arg125, %arg126) <{binding = @zkl_binding_5, parameters = [], site = "s0"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%274)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%275: i1):  // pred: ^bb0
      %276 = "exec.returned"(%275) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%276) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%277: !exec.stop):  // pred: ^bb0
      %278 = "exec.failed"(%277) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%278) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.origin = ["s3h7a6b637h696e64696365734h6c657373", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "s3h7a6b6311h6d756c74696c696e6561724h726f7773", sym_visibility = "private"}> ({
    ^bb0(%arg122: !runtime.scope, %arg123: ui64):
      %227 = "exec.apply"(%arg122) <{binding = @zkl_binding_0, parameters = [64 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%227)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%228: ui64):  // pred: ^bb0
      %229 = "func.call"(%arg122, %arg123, %228) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s1"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%229)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%230: !exec.stop):  // 14 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12, ^bb14, ^bb15, ^bb19, ^bb21
      %231 = "exec.failed"(%230) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%231) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%232: i1):  // pred: ^bb1
      %233 = "exec.test"(%arg122, %232) <{site = "s2"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%233)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb4(%234: i1):  // pred: ^bb3
      "cf.cond_br"(%234)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %235 = "runtime.enter_scope"(%arg122) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s2"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%235)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %236 = "runtime.enter_scope"(%arg122) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s2"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%236)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // 2 preds: ^bb10, ^bb13
      %237 = "exec.apply"(%arg122) <{binding = @zkl_binding_0, parameters = [1 : ui64], site = "s3"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%237)[^bb14, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb8(%238: !runtime.scope):  // pred: ^bb5
      %239 = "func.call"(%238) <{callee = @zkl_control_8}> : (!runtime.scope) -> !exec.outcome<>
      %240 = "runtime.exit_scope"(%238, %239) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%240)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb9(%241: !runtime.transfer<>):  // pred: ^bb8
      %242 = "runtime.accept_transfer"(%arg122, %241) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%242)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb10:  // pred: ^bb9
      "cf.br"()[^bb7] : () -> ()
    ^bb11(%243: !runtime.scope):  // pred: ^bb6
      %244 = "func.call"(%243) <{callee = @zkl_control_9}> : (!runtime.scope) -> !exec.outcome<>
      %245 = "runtime.exit_scope"(%243, %244) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%245)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb12(%246: !runtime.transfer<>):  // pred: ^bb11
      %247 = "runtime.accept_transfer"(%arg122, %246) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%247)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb13:  // pred: ^bb12
      "cf.br"()[^bb7] : () -> ()
    ^bb14(%248: ui64):  // pred: ^bb7
      %249 = "exec.apply"(%arg122) <{binding = @zkl_binding_0, parameters = [0 : ui64], site = "s5"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%249)[^bb15, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb15(%250: ui64):  // pred: ^bb14
      %251 = "exec.range"(%arg122, %250, %arg123) <{site = "s6"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%251)[^bb16, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i64, i64)>) -> ()
    ^bb16(%252: i64, %253: i64):  // pred: ^bb15
      %254 = "runtime.borrow_transfer"(%arg122, %248) : (!runtime.scope, ui64) -> !runtime.transfer<(ui64)>
      "cf.br"(%252, %254)[^bb17] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb17(%255: i64, %256: !runtime.transfer<(ui64)>):  // 2 preds: ^bb16, ^bb20
      %257 = "arith.cmpi"(%255, %253) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%257, %256)[^bb18, ^bb19] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(ui64)>) -> ()
    ^bb18:  // pred: ^bb17
      %258 = "runtime.iteration"(%arg122, %255) <{site = "s6"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%258)[^bb22, ^bb21] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb19(%259: !runtime.transfer<(ui64)>):  // pred: ^bb17
      %260 = "runtime.accept_transfer"(%arg122, %259) : (!runtime.scope, !runtime.transfer<(ui64)>) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%260)[^bb25, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb20(%261: !runtime.transfer<(ui64)>):  // pred: ^bb24
      %262 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %263 = "arith.addi"(%255, %262) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%263, %261)[^bb17] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb21(%264: !exec.stop):  // 3 preds: ^bb18, ^bb22, ^bb23
      "runtime.release_transfer"(%256) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%264)[^bb2] : (!exec.stop) -> ()
    ^bb22(%265: ui64):  // pred: ^bb18
      %266 = "runtime.transfer_values"(%256) : (!runtime.transfer<(ui64)>) -> ui64
      %267 = "runtime.enter_scope"(%arg122, %255, %265, %266) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 2>, site = "s6"}> : (!runtime.scope, i64, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%267)[^bb23, ^bb21] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb23(%268: !runtime.scope):  // pred: ^bb22
      %269 = "func.call"(%268, %265, %266) <{callee = @zkl_control_10}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      %270 = "runtime.exit_scope"(%268, %269) : (!runtime.scope, !exec.outcome<(ui64)>) -> !exec.outcome<(!runtime.transfer<(ui64)>)>
      "exec.dispatch"(%270)[^bb24, ^bb21] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(ui64)>)>) -> ()
    ^bb24(%271: !runtime.transfer<(ui64)>):  // pred: ^bb23
      "runtime.release_transfer"(%256) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%271)[^bb20] : (!runtime.transfer<(ui64)>) -> ()
    ^bb25(%272: ui64):  // pred: ^bb19
      %273 = "exec.returned"(%272) : (ui64) -> !exec.outcome<(ui64)>
      "func.return"(%273) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561724h726f7773", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_8", sym_visibility = "private"}> ({
    ^bb0(%arg121: !runtime.scope):
      %226 = "exec.complete"(%arg121) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%226) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_9", sym_visibility = "private"}> ({
    ^bb0(%arg120: !runtime.scope):
      %223 = "exec.reject"(%arg120) <{reason = "reject", site = "s2_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%223)[^bb1] : (!exec.stop) -> ()
    ^bb1(%224: !exec.stop):  // pred: ^bb0
      %225 = "exec.failed"(%224) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%225) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "zkl_control_10", sym_visibility = "private"}> ({
    ^bb0(%arg117: !runtime.scope, %arg118: ui64, %arg119: ui64):
      %216 = "exec.apply"(%arg117) <{binding = @zkl_binding_0, parameters = [2 : ui64], site = "s7"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%216)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%217: ui64):  // pred: ^bb0
      %218 = "exec.apply"(%arg117, %arg119, %217) <{binding = @zkl_binding_6, parameters = [], site = "s8"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%218)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%219: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %220 = "exec.failed"(%219) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%220) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%221: ui64):  // pred: ^bb1
      %222 = "exec.complete"(%arg117, %221) : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "func.return"(%222) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_c0a3a2b8b5f989e0e9c138a171631d20dc8bd296769b6ee7636d2d79a8518ba0", sym_visibility = "private"}> ({
    ^bb0(%arg115: !runtime.scope, %arg116: !algebra.field<"bls12-381.fr">):
      %209 = "exec.apply"(%arg115) <{binding = @zkl_binding_7, parameters = [], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%209)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%210: !data.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %211 = "exec.apply"(%arg115) <{binding = @zkl_binding_8, parameters = [], site = "s1_create_0"}> : (!runtime.scope) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">)>
      "exec.dispatch"(%211)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">)>) -> ()
    ^bb2(%212: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %213 = "exec.failed"(%212) : (!exec.stop) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%213) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb3(%214: !runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">):  // pred: ^bb1
      %215 = "exec.returned"(%214, %210, %arg116) : (!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%215) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s8h73756d636865636b7h70656e64696e67", []]} : () -> ()
    "protocol.func"() <{contracts = [["input", "shape", [@zkl_8c866415d5a42d7cb60d6b39dd52568c20001248a901906f13a3d5d9dd8f74ac, [["input", 0, "role00000000"], ["input", 1, "role00000000"], ["input", 2, "role00000000"]]], unit, unit], ["continuation", "initial_sum", [@zkl_f03c5af270c09f9d5e832cdb0dc1d71151cebecfaaa08c6cacd997dde03860e9, [["input", 0, "role00000000"], ["input", 1, "role00000000"], ["input", 2, "role00000000"], ["input", 4, "role00000001"], ["input", 5, "role00000001"]]], [@zkl_f03c5af270c09f9d5e832cdb0dc1d71151cebecfaaa08c6cacd997dde03860e9, [["input", 0, "role00000000"], ["input", 1, "role00000000"], ["input", 2, "role00000000"], ["output", 5, "role00000001"], ["output", 6, "role00000001"]]], unit]], function_type = (!data.field_vector<"bls12-381.fr">, ui64, ui64, !runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, ui64, !runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), input_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"], ["role00000001"], ["role00000000", "role00000001"], ["role00000001"]], origin = ["sumcheck::Reduce", [["F", ["field", "bls12-381.fr"]], ["Max", ["nat", "2"]]]], output_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"], ["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5"}> ({
    ^bb0(%arg99: !data.field_vector<"bls12-381.fr">, %arg100: ui64, %arg101: ui64, %arg102: !runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, %arg103: !data.field_vector<"bls12-381.fr">, %arg104: !algebra.field<"bls12-381.fr">, %arg105: ui64, %arg106: !protocol.service_ref<"random.bls12-381.fr/0">):
      %180 = "func.call"(%arg99, %arg100, %arg101) <{callee = @zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %181 = "data.index"() <{value = 1 : ui64}> : () -> ui64
      %182 = "data.index_equal"(%180, %181) : (ui64, ui64) -> i1
      "protocol.guard"(%182) <{owner = "role00000000", site = "s3"}> : (i1) -> ()
      %183 = "func.call"(%arg99, %arg100, %arg101) <{callee = @zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %184 = "protocol.local_call"(%183, %arg105) <{callee = @s3h7a6b637h696e64696365734h6c657373, role = "role00000000", site = "s5"}> : (ui64, ui64) -> i1
      %185 = "arith.constant"() <{value = false}> : () -> i1
      %186 = "arith.cmpi"(%184, %185) <{predicate = 0 : i64}> : (i1, i1) -> i1
      "protocol.guard"(%186) <{owner = "role00000000", site = "s8"}> : (i1) -> ()
      %187 = "protocol.local_call"() <{callee = @zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f, role = "role00000000", site = "s10"}> : () -> !data.field_vector<"bls12-381.fr">
      %188:2 = "protocol.local_call"(%arg102, %arg103, %arg104) <{callee = @zkl_e8df957aab384c1d5416600c13a571512206e97abfbf6e0e9cddac5c84860d07, role = "role00000001", site = "s12"}> : (!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %189:6 = "protocol.repeat"(%arg105, %arg99, %arg100, %arg101, %187, %188#0, %188#1, %arg106) <{carried = 6 : i64, carried_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"]], maximum = 2 : i64, roles = ["role00000000", "role00000001"], site = "s18"}> ({
      ^bb0(%arg107: ui64, %arg108: !data.field_vector<"bls12-381.fr">, %arg109: ui64, %arg110: ui64, %arg111: !data.field_vector<"bls12-381.fr">, %arg112: !data.field_vector<"bls12-381.fr">, %arg113: !algebra.field<"bls12-381.fr">, %arg114: !protocol.service_ref<"random.bls12-381.fr/0">):
        %191:2 = "protocol.local_call"(%arg108, %arg109, %arg110) <{callee = @zkl_532a609cf36a935835501ca51308940142121e647ca360843a880bf231f04aa6, role = "role00000000", site = "s19"}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %192 = "protocol.exchange"(%191#0) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %193 = "protocol.restrict_roles"(%192) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %194 = "protocol.exchange"(%191#1) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_1"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %195 = "protocol.restrict_roles"(%194) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %196 = "algebra.field_add"(%193, %195) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %197 = "algebra.field_equal"(%arg113, %196) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
        "protocol.guard"(%197) <{owner = "role00000001", site = "s27"}> : (i1) -> ()
        %198 = "protocol.query"(%arg114) <{method = "draw", owner = "role00000001", site = "label_6368616c6c656e6765"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
        %199 = "protocol.exchange"(%198) <{receiver = "role00000000", sender = "role00000001", site = "label_64656c6976657279_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %200 = "protocol.restrict_roles"(%199) <{roles = ["role00000000"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %201:3 = "protocol.local_call"(%arg108, %arg109, %arg110, %200) <{callee = @zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d, role = "role00000000", site = "s32"}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> (!data.field_vector<"bls12-381.fr">, ui64, ui64)
        %202 = "protocol.local_call"(%arg111, %200) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000000", site = "s34"}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !data.field_vector<"bls12-381.fr">
        %203 = "protocol.local_call"(%arg112, %198) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000001", site = "s36"}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !data.field_vector<"bls12-381.fr">
        %204 = "algebra.constant"() <{value = #algebra.literal<<"bls12-381.fr">, 1 : ui255> : !algebra.field<"bls12-381.fr">}> : () -> !algebra.field<"bls12-381.fr">
        %205 = "algebra.field_subtract"(%204, %198) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %206 = "algebra.field_multiply"(%205, %193) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %207 = "algebra.field_multiply"(%198, %195) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %208 = "algebra.field_add"(%206, %207) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        "protocol.yield"(%201#0, %201#1, %201#2, %202, %203, %208) : (!data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
      }) : (ui64, !data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %190:3 = "protocol.local_call"(%189#4, %189#5) <{callee = @zkl_c36a2d2c6bd38573735fb9b90d1a3848c562d2c1f688234e2b669408e9c9eea9, role = "role00000001", site = "s48"}> : (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      "protocol.return"(%189#3, %189#0, %189#1, %189#2, %190#0, %190#1, %190#2) : (!data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, ui64, !runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> i1, sym_name = "zkf_326ab2331715c62ba21cb6a967c927ba6ad7f7f2da5e84eb0e5de0fc610f26ca", sym_visibility = "private"}> ({
    ^bb0(%arg90: !data.field_vector<"bls12-381.fr">, %arg91: ui64, %arg92: ui64):
      %171 = "func.call"(%arg90, %arg91, %arg92) <{callee = @zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %172 = "data.index"() <{value = 1 : ui64}> : () -> ui64
      %173 = "data.index_equal"(%171, %172) : (ui64, ui64) -> i1
      %174 = "data.branch"(%173, %arg90, %arg91, %arg92) <{alternatives = ["then", "else"]}> ({
      ^bb0(%arg96: !data.field_vector<"bls12-381.fr">, %arg97: ui64, %arg98: ui64):
        %176 = "func.call"(%arg96, %arg97, %arg98) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !data.field_vector<"bls12-381.fr">
        %177 = "data.dim"(%176) <{axis = 0 : i64}> : (!data.field_vector<"bls12-381.fr">) -> ui64
        %178 = "func.call"(%arg96, %arg97, %arg98) <{callee = @zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94}> : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
        %179 = "data.index_power_of_two"(%177, %178) : (ui64, ui64) -> i1
        "data.yield"(%179) : (i1) -> ()
      }, {
      ^bb0(%arg93: !data.field_vector<"bls12-381.fr">, %arg94: ui64, %arg95: ui64):
        %175 = "arith.constant"() <{value = false}> : () -> i1
        "data.yield"(%175) : (i1) -> ()
      }) : (i1, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> i1
      "func.return"(%174) : (i1) -> ()
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
    "func.func"() <{function_type = (!runtime.scope, !runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_e8df957aab384c1d5416600c13a571512206e97abfbf6e0e9cddac5c84860d07", sym_visibility = "private"}> ({
    ^bb0(%arg71: !runtime.scope, %arg72: !runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, %arg73: !data.field_vector<"bls12-381.fr">, %arg74: !algebra.field<"bls12-381.fr">):
      %158 = "exec.apply"(%arg71, %arg72) <{binding = @zkl_binding_9, parameters = [], site = "s0_unpack_0"}> : (!runtime.scope, !runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">) -> !exec.outcome<>
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
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_c36a2d2c6bd38573735fb9b90d1a3848c562d2c1f688234e2b669408e9c9eea9", sym_visibility = "private"}> ({
    ^bb0(%arg39: !runtime.scope, %arg40: !data.field_vector<"bls12-381.fr">, %arg41: !algebra.field<"bls12-381.fr">):
      %87 = "exec.apply"(%arg39) <{binding = @zkl_binding_8, parameters = [], site = "s0_create_0"}> : (!runtime.scope) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">)>
      "exec.dispatch"(%87)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">)>) -> ()
    ^bb1(%88: !runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">):  // pred: ^bb0
      %89 = "exec.returned"(%88, %arg40, %arg41) : (!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%89) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%90: !exec.stop):  // pred: ^bb0
      %91 = "exec.failed"(%90) : (!exec.stop) -> !exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%91) : (!exec.outcome<(!runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s8h73756d636865636b9h61745f707265666978", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, !runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc", sym_visibility = "private"}> ({
    ^bb0(%arg34: !runtime.scope, %arg35: !data.field_vector<"bls12-381.fr">, %arg36: !runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">, %arg37: !data.field_vector<"bls12-381.fr">, %arg38: !algebra.field<"bls12-381.fr">):
      %60 = "exec.apply"(%arg34, %arg36) <{binding = @zkl_binding_9, parameters = [], site = "s0_unpack_0"}> : (!runtime.scope, !runtime.capability<resource_unit, "zkl_resource_e879b580f7fdcf4d6debf9c9777de579b7015ecbc447abeffa5e14af217ae4e6">) -> !exec.outcome<>
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
      %22 = "func.call"(%arg17, %arg18, %arg19, %arg20, %arg21) <{callee = @zkl_c22ca043f56e31ae33fc04b669755c76f6f9db03b95b1cc7733fde9f3c08b402}> {runtime.site = "s0"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
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
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_c22ca043f56e31ae33fc04b669755c76f6f9db03b95b1cc7733fde9f3c08b402", sym_visibility = "private"}> ({
    ^bb0(%arg7: !runtime.scope, %arg8: !data.field_vector<"bls12-381.fr">, %arg9: ui64, %arg10: ui64, %arg11: !data.field_vector<"bls12-381.fr">):
      %8 = "exec.fold"(%arg7, %arg11, %arg8, %arg9, %arg10) <{domain = @finite_zkl_c22ca043f56e31ae33fc04b669755c76f6f9db03b95b1cc7733fde9f3c08b402_s0_domain, site = "s0", step = @finite_zkl_c22ca043f56e31ae33fc04b669755c76f6f9db03b95b1cc7733fde9f3c08b402_s0_body}> : (!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%8)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb1(%9: !data.field_vector<"bls12-381.fr">, %10: ui64, %11: ui64):  // pred: ^bb0
      %12 = "exec.returned"(%9, %10, %11) : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%12) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb2(%13: !exec.stop):  // pred: ^bb0
      %14 = "exec.failed"(%13) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%14) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_c22ca043f56e31ae33fc04b669755c76f6f9db03b95b1cc7733fde9f3c08b402_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg6: !data.field_vector<"bls12-381.fr">):
      %7 = "data.domain_elements"(%arg6) : (!data.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%7) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "finite_zkl_c22ca043f56e31ae33fc04b669755c76f6f9db03b95b1cc7733fde9f3c08b402_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg0: !runtime.scope, %arg1: !data.field_vector<"bls12-381.fr">, %arg2: ui64, %arg3: ui64, %arg4: !algebra.field<"bls12-381.fr">, %arg5: !data.field_vector<"bls12-381.fr">):
      %0 = "func.call"(%arg0, %arg1, %arg2, %arg3, %arg4) <{callee = @zkl_195a79478f48dffc2a6917273d8317df0fabae786920a46fa2ac6b2737144299}> {runtime.site = "body"} : (!runtime.scope, !data.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb1(%1: !data.field_vector<"bls12-381.fr">, %2: ui64, %3: ui64):  // pred: ^bb0
      %4 = "exec.returned"(%1, %2, %3) : (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%4) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb2(%5: !exec.stop):  // pred: ^bb0
      %6 = "exec.failed"(%5) : (!exec.stop) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%6) : (!exec.outcome<(!data.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["finite_zkl_c22ca043f56e31ae33fc04b669755c76f6f9db03b95b1cc7733fde9f3c08b402_s0_body", []]} : () -> ()
    "relation.declare"() <{formula = @zkf_9ca6c98faa0d00ed80eb608a89db1544ad71443a8944af6ac99e6fd78cb3660b, key = "zkl_733a9984be750c90a7e40f8fc81c10a284cb9ecaf745c62024f07f1a3806a10c", kind = "zkc.language.formula/0", purposes = ["parameter", "parameter"], revision = "09463457777001ce6c09c9f8993c1bd0b601c89f93d22f6b2eef8d32347ecbf1", signature = (!data.field_vector<"bls12-381.fr">, ui64) -> i1, static_arguments = [], sym_name = "zkl_733a9984be750c90a7e40f8fc81c10a284cb9ecaf745c62024f07f1a3806a10c"}> : () -> ()
    "relation.declare"() <{formula = @zkf_116f3285742dd1275b8149c69b78a6713cd6256a8af715be7c346da1c793a766, key = "zkl_1c2e12f894c2f4b39d38adc87f1dedbaf7856eb6985dba89eb2261c88030aef2", kind = "zkc.language.formula/0", purposes = ["parameter", "statement"], revision = "57d17255e158ced9416cb3888c3f005f4e17bae102e66f5a117b3a000b9306da", signature = (!data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, static_arguments = [], sym_name = "zkl_1c2e12f894c2f4b39d38adc87f1dedbaf7856eb6985dba89eb2261c88030aef2"}> : () -> ()
    "relation.declare"() <{formula = @zkf_326ab2331715c62ba21cb6a967c927ba6ad7f7f2da5e84eb0e5de0fc610f26ca, key = "zkl_8c866415d5a42d7cb60d6b39dd52568c20001248a901906f13a3d5d9dd8f74ac", kind = "zkc.language.formula/0", purposes = ["parameter", "parameter", "parameter"], revision = "b38e3036898a0350bf7db3a319e518bcd650355abbfc625037f409f6bb2afc48", signature = (!data.field_vector<"bls12-381.fr">, ui64, ui64) -> i1, static_arguments = [], sym_name = "zkl_8c866415d5a42d7cb60d6b39dd52568c20001248a901906f13a3d5d9dd8f74ac"}> : () -> ()
    "relation.declare"() <{formula = @zkf_c51d11bf318ad26bc2fce7b89eec63f85b98f57e91e0e9e6256f84a573b5b6e6, key = "zkl_f03c5af270c09f9d5e832cdb0dc1d71151cebecfaaa08c6cacd997dde03860e9", kind = "zkc.language.formula/0", purposes = ["parameter", "parameter", "parameter", "statement", "statement"], revision = "dd2b2582f72ba257a868259cea188039de19f66f8a3fafa017be603aa980be98", signature = (!data.field_vector<"bls12-381.fr">, ui64, ui64, !data.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, static_arguments = [], sym_name = "zkl_f03c5af270c09f9d5e832cdb0dc1d71151cebecfaaa08c6cacd997dde03860e9"}> : () -> ()
  }) : () -> ()
}) : () -> ()

