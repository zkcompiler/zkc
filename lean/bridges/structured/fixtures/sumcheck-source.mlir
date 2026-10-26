"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "field.equal", implementation = "", sym_name = "zkl_binding_12"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.append", implementation = "", sym_name = "zkl_binding_11"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.sub", implementation = "", sym_name = "zkl_binding_10"}> : () -> ()
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
    "protocol.func"() <{contracts = [["input", "shape", [@zkl_733a9984be750c90a7e40f8fc81c10a284cb9ecaf745c62024f07f1a3806a10c, [["input", 0, "role00000001"], ["input", 2, "role00000001"]]], unit, unit], ["target", "public_sum", [@zkl_1c2e12f894c2f4b39d38adc87f1dedbaf7856eb6985dba89eb2261c88030aef2, [["input", 0, "role00000001"], ["input", 1, "role00000001"]]], unit, ["output", 0, "role00000001"]]], function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> i1, input_roles = [["role00000000", "role00000001"], ["role00000001"], ["role00000000", "role00000001"], ["role00000001"]], origin = ["sumcheck::Sumcheck", [["F", ["field", "bls12-381.fr"]], ["Max", ["nat", "2"]]]], output_roles = [["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071"}> ({
    ^bb0(%arg144: !algebra.field_vector<"bls12-381.fr">, %arg145: !algebra.field<"bls12-381.fr">, %arg146: ui64, %arg147: !protocol.service_ref<"random.bls12-381.fr/0">):
      %390 = "data.index"() <{value = "1"}> : () -> ui64
      %391:3 = "protocol.local_call"(%arg144, %arg146, %390) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a, role = "role00000000", site = "s1"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      %392:6 = "protocol.apply"(%391#0, %391#1, %391#2, %arg145, %arg146, %arg147) <{callee = @zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5, roles = ["role00000000", "role00000001"], site = "label_726564756365"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %393 = "protocol.local_call"(%arg144, %392#4, %392#5) <{callee = @zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc, role = "role00000001", site = "s7"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "protocol.return"(%393) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64) -> i1, sym_name = "zkf_9ca6c98faa0d00ed80eb608a89db1544ad71443a8944af6ac99e6fd78cb3660b", sym_visibility = "private"}> ({
    ^bb0(%arg142: !algebra.field_vector<"bls12-381.fr">, %arg143: ui64):
      %383 = "data.dim"(%arg142) <{axis = 0 : i64}> : (!algebra.field_vector<"bls12-381.fr">) -> ui64
      %384 = "data.index_power_of_two"(%383, %arg143) : (ui64, ui64) -> i1
      %385 = "data.index"() <{value = "2"}> : () -> ui64
      %386 = "data.index_less"(%385, %arg143) : (ui64, ui64) -> i1
      %387 = "arith.constant"() <{value = false}> : () -> i1
      %388 = "arith.cmpi"(%386, %387) <{predicate = 0 : i64}> : (i1, i1) -> i1
      %389 = "arith.andi"(%384, %388) : (i1, i1) -> i1
      "func.return"(%389) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "zkf_116f3285742dd1275b8149c69b78a6713cd6256a8af715be7c346da1c793a766", sym_visibility = "private"}> ({
    ^bb0(%arg140: !algebra.field_vector<"bls12-381.fr">, %arg141: !algebra.field<"bls12-381.fr">):
      %381 = "func.call"(%arg140) <{callee = @zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e}> : (!algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %382 = "algebra.field_equal"(%arg141, %381) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "func.return"(%382) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e", sym_visibility = "private"}> ({
    ^bb0(%arg139: !algebra.field_vector<"bls12-381.fr">):
      %379 = "algebra.constant"() <{value = "0"}> : () -> !algebra.field<"bls12-381.fr">
      %380 = "algebra.finite_fold"(%arg139, %379) <{domain = @finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_domain, step = @finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_body}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%380) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_domain", sym_visibility = "private"}> ({
    ^bb0(%arg138: !algebra.field_vector<"bls12-381.fr">):
      %378 = "data.domain_elements"(%arg138) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%378) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_body", sym_visibility = "private"}> ({
    ^bb0(%arg135: !algebra.field<"bls12-381.fr">, %arg136: !algebra.field<"bls12-381.fr">, %arg137: !algebra.field_vector<"bls12-381.fr">):
      %377 = "func.call"(%arg135, %arg136) <{callee = @zkl_3fc17a64a5bb6e75192d0a1362e9954f0d434a10d0f93e319db6b516835a1005}> : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%377) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_3fc17a64a5bb6e75192d0a1362e9954f0d434a10d0f93e319db6b516835a1005", sym_visibility = "private"}> ({
    ^bb0(%arg133: !algebra.field<"bls12-381.fr">, %arg134: !algebra.field<"bls12-381.fr">):
      %376 = "algebra.field_add"(%arg133, %arg134) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%376) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", sym_visibility = "private"}> ({
    ^bb0(%arg129: !runtime.scope, %arg130: !algebra.field_vector<"bls12-381.fr">, %arg131: ui64, %arg132: ui64):
      %357 = "func.call"(%arg129, %arg130, %arg131, %arg132) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655}> {runtime.site = "s0"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%357)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%358: i1):  // pred: ^bb0
      %359 = "exec.test"(%arg129, %358) <{site = "s1"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%359)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%360: !exec.stop):  // 8 preds: ^bb0, ^bb1, ^bb4, ^bb5, ^bb7, ^bb8, ^bb10, ^bb11
      %361 = "exec.failed"(%360) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%361) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb3(%362: i1):  // pred: ^bb1
      "cf.cond_br"(%362)[^bb4, ^bb5] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb4:  // pred: ^bb3
      %363 = "runtime.enter_scope"(%arg129) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%363)[^bb7, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb5:  // pred: ^bb3
      %364 = "runtime.enter_scope"(%arg129) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%364)[^bb10, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // 2 preds: ^bb9, ^bb12
      %365 = "exec.returned"(%arg130, %arg131, %arg132) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%365) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb7(%366: !runtime.scope):  // pred: ^bb4
      %367 = "func.call"(%366) <{callee = @zkl_control_0}> : (!runtime.scope) -> !exec.outcome<>
      %368 = "runtime.exit_scope"(%366, %367) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%368)[^bb8, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb8(%369: !runtime.transfer<>):  // pred: ^bb7
      %370 = "runtime.accept_transfer"(%arg129, %369) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%370)[^bb9, ^bb2] : (!exec.outcome<>) -> ()
    ^bb9:  // pred: ^bb8
      "cf.br"()[^bb6] : () -> ()
    ^bb10(%371: !runtime.scope):  // pred: ^bb5
      %372 = "func.call"(%371) <{callee = @zkl_control_1}> : (!runtime.scope) -> !exec.outcome<>
      %373 = "runtime.exit_scope"(%371, %372) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%373)[^bb11, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb11(%374: !runtime.transfer<>):  // pred: ^bb10
      %375 = "runtime.accept_transfer"(%arg129, %374) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%375)[^bb12, ^bb2] : (!exec.outcome<>) -> ()
    ^bb12:  // pred: ^bb11
      "cf.br"()[^bb6] : () -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561725h7461626c65", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_0", sym_visibility = "private"}> ({
    ^bb0(%arg128: !runtime.scope):
      %356 = "exec.complete"(%arg128) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%356) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_1", sym_visibility = "private"}> ({
    ^bb0(%arg127: !runtime.scope):
      %353 = "exec.reject"(%arg127) <{reason = "reject", site = "s1_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%353)[^bb1] : (!exec.stop) -> ()
    ^bb1(%354: !exec.stop):  // pred: ^bb0
      %355 = "exec.failed"(%354) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%355) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", sym_visibility = "private"}> ({
    ^bb0(%arg123: !runtime.scope, %arg124: !algebra.field_vector<"bls12-381.fr">, %arg125: ui64, %arg126: ui64):
      %295 = "exec.apply"(%arg123) <{binding = @zkl_binding_0, parameters = ["0"], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%295)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%296: ui64):  // pred: ^bb0
      %297 = "func.call"(%arg123, %296, %arg126) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s1"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%297)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%298: !exec.stop):  // 23 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12, ^bb15, ^bb16, ^bb17, ^bb18, ^bb19, ^bb21, ^bb22, ^bb25, ^bb26, ^bb28, ^bb29, ^bb31, ^bb32
      %299 = "exec.failed"(%298) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%299) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%300: i1):  // pred: ^bb1
      %301 = "exec.test"(%arg123, %300) <{site = "s3"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%301)[^bb4, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb4(%302: i1):  // pred: ^bb3
      "cf.cond_br"(%302)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %303 = "runtime.enter_scope"(%arg123, %arg125) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "then", site = "s3"}> : (!runtime.scope, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%303)[^bb8, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %304 = "runtime.enter_scope"(%arg123, %arg125) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "else", site = "s3"}> : (!runtime.scope, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%304)[^bb11, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7(%305: i1):  // 2 preds: ^bb10, ^bb13
      %306 = "exec.test"(%arg123, %305) <{site = "s11"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%306)[^bb14, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb8(%307: !runtime.scope):  // pred: ^bb5
      %308 = "func.call"(%307, %arg125) <{callee = @zkl_control_2}> : (!runtime.scope, ui64) -> !exec.outcome<(i1)>
      %309 = "runtime.exit_scope"(%307, %308) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%309)[^bb9, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb9(%310: !runtime.transfer<(i1)>):  // pred: ^bb8
      %311 = "runtime.accept_transfer"(%arg123, %310) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%311)[^bb10, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb10(%312: i1):  // pred: ^bb9
      "cf.br"(%312)[^bb7] : (i1) -> ()
    ^bb11(%313: !runtime.scope):  // pred: ^bb6
      %314 = "func.call"(%313, %arg125) <{callee = @zkl_control_3}> : (!runtime.scope, ui64) -> !exec.outcome<(i1)>
      %315 = "runtime.exit_scope"(%313, %314) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%315)[^bb12, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb12(%316: !runtime.transfer<(i1)>):  // pred: ^bb11
      %317 = "runtime.accept_transfer"(%arg123, %316) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%317)[^bb13, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb13(%318: i1):  // pred: ^bb12
      "cf.br"(%318)[^bb7] : (i1) -> ()
    ^bb14(%319: i1):  // pred: ^bb7
      "cf.cond_br"(%319)[^bb15, ^bb16] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb15:  // pred: ^bb14
      %320 = "runtime.enter_scope"(%arg123, %arg124, %arg126) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "then", site = "s11"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%320)[^bb18, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb16:  // pred: ^bb14
      %321 = "runtime.enter_scope"(%arg123, %arg124, %arg126) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "else", site = "s11"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%321)[^bb21, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb17(%322: i1):  // 2 preds: ^bb20, ^bb23
      %323 = "exec.test"(%arg123, %322) <{site = "s22"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%323)[^bb24, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb18(%324: !runtime.scope):  // pred: ^bb15
      %325 = "func.call"(%324, %arg124, %arg126) <{callee = @zkl_control_4}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>
      %326 = "runtime.exit_scope"(%324, %325) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%326)[^bb19, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb19(%327: !runtime.transfer<(i1)>):  // pred: ^bb18
      %328 = "runtime.accept_transfer"(%arg123, %327) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%328)[^bb20, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb20(%329: i1):  // pred: ^bb19
      "cf.br"(%329)[^bb17] : (i1) -> ()
    ^bb21(%330: !runtime.scope):  // pred: ^bb16
      %331 = "func.call"(%330, %arg124, %arg126) <{callee = @zkl_control_5}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>
      %332 = "runtime.exit_scope"(%330, %331) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%332)[^bb22, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb22(%333: !runtime.transfer<(i1)>):  // pred: ^bb21
      %334 = "runtime.accept_transfer"(%arg123, %333) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%334)[^bb23, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb23(%335: i1):  // pred: ^bb22
      "cf.br"(%335)[^bb17] : (i1) -> ()
    ^bb24(%336: i1):  // pred: ^bb17
      "cf.cond_br"(%336)[^bb25, ^bb26] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb25:  // pred: ^bb24
      %337 = "runtime.enter_scope"(%arg123, %arg124, %arg125, %arg126) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "then", site = "s22"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%337)[^bb28, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb26:  // pred: ^bb24
      %338 = "runtime.enter_scope"(%arg123, %arg124, %arg125, %arg126) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "else", site = "s22"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%338)[^bb31, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb27(%339: i1):  // 2 preds: ^bb30, ^bb33
      %340 = "exec.returned"(%339) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%340) : (!exec.outcome<(i1)>) -> ()
    ^bb28(%341: !runtime.scope):  // pred: ^bb25
      %342 = "func.call"(%341, %arg124, %arg125, %arg126) <{callee = @zkl_control_6}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      %343 = "runtime.exit_scope"(%341, %342) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%343)[^bb29, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb29(%344: !runtime.transfer<(i1)>):  // pred: ^bb28
      %345 = "runtime.accept_transfer"(%arg123, %344) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%345)[^bb30, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb30(%346: i1):  // pred: ^bb29
      "cf.br"(%346)[^bb27] : (i1) -> ()
    ^bb31(%347: !runtime.scope):  // pred: ^bb26
      %348 = "func.call"(%347, %arg124, %arg125, %arg126) <{callee = @zkl_control_7}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      %349 = "runtime.exit_scope"(%347, %348) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%349)[^bb32, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb32(%350: !runtime.transfer<(i1)>):  // pred: ^bb31
      %351 = "runtime.accept_transfer"(%arg123, %350) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%351)[^bb33, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb33(%352: i1):  // pred: ^bb32
      "cf.br"(%352)[^bb27] : (i1) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_2", sym_visibility = "private"}> ({
    ^bb0(%arg121: !runtime.scope, %arg122: ui64):
      %288 = "exec.apply"(%arg121) <{binding = @zkl_binding_0, parameters = ["64"], site = "s4"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%288)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%289: ui64):  // pred: ^bb0
      %290 = "func.call"(%arg121, %arg122, %289) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s5"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%290)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%291: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %292 = "exec.failed"(%291) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%292) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%293: i1):  // pred: ^bb1
      %294 = "exec.complete"(%arg121, %293) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%294) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_3", sym_visibility = "private"}> ({
    ^bb0(%arg119: !runtime.scope, %arg120: ui64):
      %283 = "exec.boolean"(%arg119) <{site = "s7", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%283)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%284: i1):  // pred: ^bb0
      %285 = "exec.complete"(%arg119, %284) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%285) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%286: !exec.stop):  // pred: ^bb0
      %287 = "exec.failed"(%286) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%287) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_4", sym_visibility = "private"}> ({
    ^bb0(%arg116: !runtime.scope, %arg117: !algebra.field_vector<"bls12-381.fr">, %arg118: ui64):
      %272 = "exec.apply"(%arg116, %arg117) <{binding = @zkl_binding_1, parameters = [], site = "s12"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%272)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%273: ui64):  // pred: ^bb0
      %274 = "exec.apply"(%arg116, %273, %arg118) <{binding = @zkl_binding_2, parameters = [], site = "s13"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%274)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%275: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %276 = "exec.failed"(%275) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%276) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%277: ui64):  // pred: ^bb1
      %278 = "exec.apply"(%arg116) <{binding = @zkl_binding_0, parameters = ["0"], site = "s14"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%278)[^bb4, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%279: ui64):  // pred: ^bb3
      %280 = "exec.apply"(%arg116, %277, %279) <{binding = @zkl_binding_3, parameters = [], site = "s15"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%280)[^bb5, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb5(%281: i1):  // pred: ^bb4
      %282 = "exec.complete"(%arg116, %281) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%282) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_5", sym_visibility = "private"}> ({
    ^bb0(%arg113: !runtime.scope, %arg114: !algebra.field_vector<"bls12-381.fr">, %arg115: ui64):
      %267 = "exec.boolean"(%arg113) <{site = "s17", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%267)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%268: i1):  // pred: ^bb0
      %269 = "exec.complete"(%arg113, %268) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%269) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%270: !exec.stop):  // pred: ^bb0
      %271 = "exec.failed"(%270) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%271) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_6", sym_visibility = "private"}> ({
    ^bb0(%arg109: !runtime.scope, %arg110: !algebra.field_vector<"bls12-381.fr">, %arg111: ui64, %arg112: ui64):
      %256 = "exec.apply"(%arg109, %arg110) <{binding = @zkl_binding_1, parameters = [], site = "s23"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%256)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%257: ui64):  // pred: ^bb0
      %258 = "exec.apply"(%arg109, %257, %arg112) <{binding = @zkl_binding_4, parameters = [], site = "s24"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%258)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%259: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %260 = "exec.failed"(%259) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%260) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%261: ui64):  // pred: ^bb1
      %262 = "func.call"(%arg109, %arg111) <{callee = @s3h7a6b6311h6d756c74696c696e6561724h726f7773}> {runtime.site = "s25"} : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%262)[^bb4, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%263: ui64):  // pred: ^bb3
      %264 = "exec.apply"(%arg109, %261, %263) <{binding = @zkl_binding_3, parameters = [], site = "s26"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%264)[^bb5, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb5(%265: i1):  // pred: ^bb4
      %266 = "exec.complete"(%arg109, %265) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%266) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_7", sym_visibility = "private"}> ({
    ^bb0(%arg105: !runtime.scope, %arg106: !algebra.field_vector<"bls12-381.fr">, %arg107: ui64, %arg108: ui64):
      %251 = "exec.boolean"(%arg105) <{site = "s28", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%251)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%252: i1):  // pred: ^bb0
      %253 = "exec.complete"(%arg105, %252) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%253) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%254: !exec.stop):  // pred: ^bb0
      %255 = "exec.failed"(%254) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%255) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "s3h7a6b637h696e64696365734h6c657373", sym_visibility = "private"}> ({
    ^bb0(%arg102: !runtime.scope, %arg103: ui64, %arg104: ui64):
      %246 = "exec.apply"(%arg102, %arg103, %arg104) <{binding = @zkl_binding_5, parameters = [], site = "s0"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%246)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%247: i1):  // pred: ^bb0
      %248 = "exec.returned"(%247) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%248) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%249: !exec.stop):  // pred: ^bb0
      %250 = "exec.failed"(%249) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%250) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.origin = ["s3h7a6b637h696e64696365734h6c657373", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "s3h7a6b6311h6d756c74696c696e6561724h726f7773", sym_visibility = "private"}> ({
    ^bb0(%arg100: !runtime.scope, %arg101: ui64):
      %199 = "exec.apply"(%arg100) <{binding = @zkl_binding_0, parameters = ["64"], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%199)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%200: ui64):  // pred: ^bb0
      %201 = "func.call"(%arg100, %arg101, %200) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s1"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%201)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%202: !exec.stop):  // 14 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12, ^bb14, ^bb15, ^bb19, ^bb21
      %203 = "exec.failed"(%202) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%203) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%204: i1):  // pred: ^bb1
      %205 = "exec.test"(%arg100, %204) <{site = "s2"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%205)[^bb4, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb4(%206: i1):  // pred: ^bb3
      "cf.cond_br"(%206)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %207 = "runtime.enter_scope"(%arg100) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s2"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%207)[^bb8, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %208 = "runtime.enter_scope"(%arg100) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s2"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%208)[^bb11, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // 2 preds: ^bb10, ^bb13
      %209 = "exec.apply"(%arg100) <{binding = @zkl_binding_0, parameters = ["1"], site = "s3"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%209)[^bb14, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb8(%210: !runtime.scope):  // pred: ^bb5
      %211 = "func.call"(%210) <{callee = @zkl_control_8}> : (!runtime.scope) -> !exec.outcome<>
      %212 = "runtime.exit_scope"(%210, %211) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%212)[^bb9, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb9(%213: !runtime.transfer<>):  // pred: ^bb8
      %214 = "runtime.accept_transfer"(%arg100, %213) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%214)[^bb10, ^bb2] : (!exec.outcome<>) -> ()
    ^bb10:  // pred: ^bb9
      "cf.br"()[^bb7] : () -> ()
    ^bb11(%215: !runtime.scope):  // pred: ^bb6
      %216 = "func.call"(%215) <{callee = @zkl_control_9}> : (!runtime.scope) -> !exec.outcome<>
      %217 = "runtime.exit_scope"(%215, %216) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%217)[^bb12, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb12(%218: !runtime.transfer<>):  // pred: ^bb11
      %219 = "runtime.accept_transfer"(%arg100, %218) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%219)[^bb13, ^bb2] : (!exec.outcome<>) -> ()
    ^bb13:  // pred: ^bb12
      "cf.br"()[^bb7] : () -> ()
    ^bb14(%220: ui64):  // pred: ^bb7
      %221 = "exec.apply"(%arg100) <{binding = @zkl_binding_0, parameters = ["0"], site = "s5"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%221)[^bb15, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb15(%222: ui64):  // pred: ^bb14
      %223 = "exec.range"(%arg100, %222, %arg101) <{site = "s6"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%223)[^bb16, ^bb2] : (!exec.outcome<(i64, i64)>) -> ()
    ^bb16(%224: i64, %225: i64):  // pred: ^bb15
      %226 = "runtime.borrow_transfer"(%arg100, %220) : (!runtime.scope, ui64) -> !runtime.transfer<(ui64)>
      "cf.br"(%224, %226)[^bb17] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb17(%227: i64, %228: !runtime.transfer<(ui64)>):  // 2 preds: ^bb16, ^bb20
      %229 = "arith.cmpi"(%227, %225) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%229, %228)[^bb18, ^bb19] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(ui64)>) -> ()
    ^bb18:  // pred: ^bb17
      %230 = "runtime.iteration"(%arg100, %227) <{site = "s6"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%230)[^bb22, ^bb21] : (!exec.outcome<(ui64)>) -> ()
    ^bb19(%231: !runtime.transfer<(ui64)>):  // pred: ^bb17
      %232 = "runtime.accept_transfer"(%arg100, %231) : (!runtime.scope, !runtime.transfer<(ui64)>) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%232)[^bb25, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb20(%233: !runtime.transfer<(ui64)>):  // pred: ^bb24
      %234 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %235 = "arith.addi"(%227, %234) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%235, %233)[^bb17] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb21(%236: !exec.stop):  // 3 preds: ^bb18, ^bb22, ^bb23
      "runtime.release_transfer"(%228) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%236)[^bb2] : (!exec.stop) -> ()
    ^bb22(%237: ui64):  // pred: ^bb18
      %238 = "runtime.transfer_values"(%228) : (!runtime.transfer<(ui64)>) -> ui64
      %239 = "runtime.enter_scope"(%arg100, %227, %237, %238) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 2>, site = "s6"}> : (!runtime.scope, i64, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%239)[^bb23, ^bb21] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb23(%240: !runtime.scope):  // pred: ^bb22
      %241 = "func.call"(%240, %237, %238) <{callee = @zkl_control_10}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      %242 = "runtime.exit_scope"(%240, %241) : (!runtime.scope, !exec.outcome<(ui64)>) -> !exec.outcome<(!runtime.transfer<(ui64)>)>
      "exec.dispatch"(%242)[^bb24, ^bb21] : (!exec.outcome<(!runtime.transfer<(ui64)>)>) -> ()
    ^bb24(%243: !runtime.transfer<(ui64)>):  // pred: ^bb23
      "runtime.release_transfer"(%228) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%243)[^bb20] : (!runtime.transfer<(ui64)>) -> ()
    ^bb25(%244: ui64):  // pred: ^bb19
      %245 = "exec.returned"(%244) : (ui64) -> !exec.outcome<(ui64)>
      "func.return"(%245) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561724h726f7773", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_8", sym_visibility = "private"}> ({
    ^bb0(%arg99: !runtime.scope):
      %198 = "exec.complete"(%arg99) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%198) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_9", sym_visibility = "private"}> ({
    ^bb0(%arg98: !runtime.scope):
      %195 = "exec.reject"(%arg98) <{reason = "reject", site = "s2_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%195)[^bb1] : (!exec.stop) -> ()
    ^bb1(%196: !exec.stop):  // pred: ^bb0
      %197 = "exec.failed"(%196) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%197) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "zkl_control_10", sym_visibility = "private"}> ({
    ^bb0(%arg95: !runtime.scope, %arg96: ui64, %arg97: ui64):
      %188 = "exec.apply"(%arg95) <{binding = @zkl_binding_0, parameters = ["2"], site = "s7"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%188)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%189: ui64):  // pred: ^bb0
      %190 = "exec.apply"(%arg95, %arg97, %189) <{binding = @zkl_binding_6, parameters = [], site = "s8"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%190)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%191: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %192 = "exec.failed"(%191) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%192) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%193: ui64):  // pred: ^bb1
      %194 = "exec.complete"(%arg95, %193) : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "func.return"(%194) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.region} : () -> ()
    "protocol.func"() <{contracts = [["input", "initial_sum", [@zkl_11c80248216cbe579879aabc5c6f64d5f465a4db68261d6da29eab7c94d7679c, [["input", 0, "role00000000"], ["input", 1, "role00000000"], ["input", 2, "role00000000"], ["input", 3, "role00000001"]]], unit, unit]], function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), input_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000000", "role00000001"], ["role00000001"]], origin = ["sumcheck::Reduce", [["F", ["field", "bls12-381.fr"]], ["Max", ["nat", "2"]]]], output_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5"}> ({
    ^bb0(%arg81: !algebra.field_vector<"bls12-381.fr">, %arg82: ui64, %arg83: ui64, %arg84: !algebra.field<"bls12-381.fr">, %arg85: ui64, %arg86: !protocol.service_ref<"random.bls12-381.fr/0">):
      %160 = "func.call"(%arg81, %arg82, %arg83) <{callee = @zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %161 = "data.index"() <{value = "1"}> : () -> ui64
      %162 = "data.index_equal"(%160, %161) : (ui64, ui64) -> i1
      "protocol.guard"(%162) <{owner = "role00000000", site = "s3"}> : (i1) -> ()
      %163 = "func.call"(%arg81, %arg82, %arg83) <{callee = @zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %164 = "protocol.local_call"(%163, %arg85) <{callee = @s3h7a6b637h696e64696365734h6c657373, role = "role00000000", site = "s5"}> : (ui64, ui64) -> i1
      %165 = "arith.constant"() <{value = false}> : () -> i1
      %166 = "arith.cmpi"(%164, %165) <{predicate = 0 : i64}> : (i1, i1) -> i1
      "protocol.guard"(%166) <{owner = "role00000000", site = "s8"}> : (i1) -> ()
      %167 = "protocol.local_call"() <{callee = @zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f, role = "role00000000", site = "s10"}> : () -> !algebra.field_vector<"bls12-381.fr">
      %168 = "protocol.local_call"() <{callee = @zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f, role = "role00000001", site = "s12"}> : () -> !algebra.field_vector<"bls12-381.fr">
      %169:6 = "protocol.repeat"(%arg85, %arg81, %arg82, %arg83, %167, %168, %arg84, %arg86) <{carried = 6 : i64, carried_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"]], maximum = 2 : i64, roles = ["role00000000", "role00000001"], site = "s15"}> ({
      ^bb0(%arg87: ui64, %arg88: !algebra.field_vector<"bls12-381.fr">, %arg89: ui64, %arg90: ui64, %arg91: !algebra.field_vector<"bls12-381.fr">, %arg92: !algebra.field_vector<"bls12-381.fr">, %arg93: !algebra.field<"bls12-381.fr">, %arg94: !protocol.service_ref<"random.bls12-381.fr/0">):
        %170:2 = "protocol.local_call"(%arg88, %arg89, %arg90) <{callee = @zkl_532a609cf36a935835501ca51308940142121e647ca360843a880bf231f04aa6, role = "role00000000", site = "s16"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %171 = "protocol.exchange"(%170#0) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %172 = "protocol.restrict_roles"(%171) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %173 = "protocol.exchange"(%170#1) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_1"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %174 = "protocol.restrict_roles"(%173) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %175 = "algebra.field_add"(%172, %174) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %176 = "algebra.field_equal"(%arg93, %175) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
        "protocol.guard"(%176) <{owner = "role00000001", site = "s24"}> : (i1) -> ()
        %177 = "protocol.query"(%arg94) <{method = "draw", owner = "role00000001", site = "label_6368616c6c656e6765"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
        %178 = "protocol.exchange"(%177) <{receiver = "role00000000", sender = "role00000001", site = "label_64656c6976657279_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %179 = "protocol.restrict_roles"(%178) <{roles = ["role00000000"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %180:3 = "protocol.local_call"(%arg88, %arg89, %arg90, %179) <{callee = @zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d, role = "role00000000", site = "s29"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
        %181 = "protocol.local_call"(%arg91, %179) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000000", site = "s31"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
        %182 = "protocol.local_call"(%arg92, %177) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000001", site = "s33"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
        %183 = "algebra.constant"() <{value = "1"}> : () -> !algebra.field<"bls12-381.fr">
        %184 = "algebra.field_subtract"(%183, %177) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %185 = "algebra.field_multiply"(%184, %172) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %186 = "algebra.field_multiply"(%177, %174) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %187 = "algebra.field_add"(%185, %186) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        "protocol.yield"(%180#0, %180#1, %180#2, %181, %182, %187) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
      }) : (ui64, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      "protocol.return"(%169#3, %169#0, %169#1, %169#2, %169#4, %169#5) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "zkf_654a0e58b11e83f398996b9e830df00890bec0f8dc08a65c5750d6d9c759b643", sym_visibility = "private"}> ({
    ^bb0(%arg77: !algebra.field_vector<"bls12-381.fr">, %arg78: ui64, %arg79: ui64, %arg80: !algebra.field<"bls12-381.fr">):
      %157 = "func.call"(%arg77, %arg78, %arg79) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">
      %158 = "func.call"(%157) <{callee = @zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e}> : (!algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %159 = "algebra.field_equal"(%arg80, %158) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "func.return"(%159) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">, sym_name = "zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", sym_visibility = "private"}> ({
    ^bb0(%arg74: !algebra.field_vector<"bls12-381.fr">, %arg75: ui64, %arg76: ui64):
      "func.return"(%arg74) : (!algebra.field_vector<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64, sym_name = "zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275", sym_visibility = "private"}> ({
    ^bb0(%arg71: !algebra.field_vector<"bls12-381.fr">, %arg72: ui64, %arg73: ui64):
      "func.return"(%arg73) : (ui64) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64, sym_name = "zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94", sym_visibility = "private"}> ({
    ^bb0(%arg68: !algebra.field_vector<"bls12-381.fr">, %arg69: ui64, %arg70: ui64):
      "func.return"(%arg69) : (ui64) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", sym_visibility = "private"}> ({
    ^bb0(%arg67: !runtime.scope):
      %152 = "exec.apply"(%arg67) <{binding = @zkl_binding_7, parameters = [], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%152)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%153: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %154 = "exec.returned"(%153) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%154) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%155: !exec.stop):  // pred: ^bb0
      %156 = "exec.failed"(%155) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%156) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6310h7072696d6974697665736h766563746f725h656d707479", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_532a609cf36a935835501ca51308940142121e647ca360843a880bf231f04aa6", sym_visibility = "private"}> ({
    ^bb0(%arg63: !runtime.scope, %arg64: !algebra.field_vector<"bls12-381.fr">, %arg65: ui64, %arg66: ui64):
      %142 = "func.call"(%arg63, %arg64, %arg65, %arg66) <{callee = @zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087}> {runtime.site = "s0"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%142)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%143: !algebra.field_vector<"bls12-381.fr">, %144: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %145 = "exec.apply"(%arg63, %143) <{binding = @zkl_binding_8, parameters = [], site = "s3"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%145)[^bb3, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%146: !exec.stop):  // 3 preds: ^bb0, ^bb1, ^bb3
      %147 = "exec.failed"(%146) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%147) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb3(%148: !algebra.field<"bls12-381.fr">):  // pred: ^bb1
      %149 = "exec.apply"(%arg63, %144) <{binding = @zkl_binding_8, parameters = [], site = "s5"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%149)[^bb4, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb4(%150: !algebra.field<"bls12-381.fr">):  // pred: ^bb3
      %151 = "exec.returned"(%148, %150) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%151) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s8h73756d636865636b4h73756d73", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087", sym_visibility = "private"}> ({
    ^bb0(%arg59: !runtime.scope, %arg60: !algebra.field_vector<"bls12-381.fr">, %arg61: ui64, %arg62: ui64):
      %118 = "exec.apply"(%arg59) <{binding = @zkl_binding_0, parameters = ["0"], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%118)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%119: ui64):  // pred: ^bb0
      %120 = "func.call"(%arg59, %119, %arg61) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s2"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%120)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%121: !exec.stop):  // 10 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12
      %122 = "exec.failed"(%121) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%122) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%123: i1):  // pred: ^bb1
      %124 = "exec.test"(%arg59, %123) <{site = "s3"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%124)[^bb4, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb4(%125: i1):  // pred: ^bb3
      "cf.cond_br"(%125)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %126 = "runtime.enter_scope"(%arg59) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s3"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%126)[^bb8, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %127 = "runtime.enter_scope"(%arg59) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s3"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%127)[^bb11, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // 2 preds: ^bb10, ^bb13
      %128 = "exec.apply"(%arg59, %arg60) <{binding = @zkl_binding_9, parameters = [], site = "s5"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%128)[^bb14, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%129: !runtime.scope):  // pred: ^bb5
      %130 = "func.call"(%129) <{callee = @zkl_control_11}> : (!runtime.scope) -> !exec.outcome<>
      %131 = "runtime.exit_scope"(%129, %130) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%131)[^bb9, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb9(%132: !runtime.transfer<>):  // pred: ^bb8
      %133 = "runtime.accept_transfer"(%arg59, %132) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%133)[^bb10, ^bb2] : (!exec.outcome<>) -> ()
    ^bb10:  // pred: ^bb9
      "cf.br"()[^bb7] : () -> ()
    ^bb11(%134: !runtime.scope):  // pred: ^bb6
      %135 = "func.call"(%134) <{callee = @zkl_control_12}> : (!runtime.scope) -> !exec.outcome<>
      %136 = "runtime.exit_scope"(%134, %135) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%136)[^bb12, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb12(%137: !runtime.transfer<>):  // pred: ^bb11
      %138 = "runtime.accept_transfer"(%arg59, %137) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%138)[^bb13, ^bb2] : (!exec.outcome<>) -> ()
    ^bb13:  // pred: ^bb12
      "cf.br"()[^bb7] : () -> ()
    ^bb14(%139: !algebra.field_vector<"bls12-381.fr">, %140: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb7
      %141 = "exec.returned"(%139, %140) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%141) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561726h68616c766573", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_11", sym_visibility = "private"}> ({
    ^bb0(%arg58: !runtime.scope):
      %117 = "exec.complete"(%arg58) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%117) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_12", sym_visibility = "private"}> ({
    ^bb0(%arg57: !runtime.scope):
      %114 = "exec.reject"(%arg57) <{reason = "reject", site = "s3_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%114)[^bb1] : (!exec.stop) -> ()
    ^bb1(%115: !exec.stop):  // pred: ^bb0
      %116 = "exec.failed"(%115) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%116) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d", sym_visibility = "private"}> ({
    ^bb0(%arg52: !runtime.scope, %arg53: !algebra.field_vector<"bls12-381.fr">, %arg54: ui64, %arg55: ui64, %arg56: !algebra.field<"bls12-381.fr">):
      %102 = "func.call"(%arg52, %arg53, %arg54, %arg55) <{callee = @zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087}> {runtime.site = "s0"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%102)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%103: !algebra.field_vector<"bls12-381.fr">, %104: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %105 = "exec.collect"(%arg52, %103, %104, %arg56) <{body = @zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body, domain = @zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_domain, site = "s4"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%105)[^bb3, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%106: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %107 = "exec.failed"(%106) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%107) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb3(%108: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb1
      %109 = "exec.apply"(%arg52) <{binding = @zkl_binding_0, parameters = ["1"], site = "s7"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%109)[^bb4, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%110: ui64):  // pred: ^bb3
      %111 = "exec.apply"(%arg52, %arg54, %110) <{binding = @zkl_binding_10, parameters = [], site = "s8"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%111)[^bb5, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%112: ui64):  // pred: ^bb4
      %113 = "exec.returned"(%108, %112, %arg55) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%113) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561729h6669785f6669727374", []]} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, sym_name = "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_domain", sym_visibility = "private"}> ({
    ^bb0(%arg50: !algebra.field_vector<"bls12-381.fr">, %arg51: !algebra.field_vector<"bls12-381.fr">):
      %99 = "data.domain_elements"(%arg50) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %100 = "data.domain_elements"(%arg51) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %101 = "data.domain_zip"(%99, %100) : (!data.domain<!algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%101) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body", sym_visibility = "private"}> ({
    ^bb0(%arg44: !runtime.scope, %arg45: !algebra.field<"bls12-381.fr">, %arg46: !algebra.field<"bls12-381.fr">, %arg47: !algebra.field_vector<"bls12-381.fr">, %arg48: !algebra.field_vector<"bls12-381.fr">, %arg49: !algebra.field<"bls12-381.fr">):
      %94 = "exec.compute"(%arg44, %arg45, %arg46, %arg49) <{callee = @zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5, site = "body"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%94)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%95: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %96 = "exec.returned"(%95) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%96) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%97: !exec.stop):  // pred: ^bb0
      %98 = "exec.failed"(%97) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%98) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5", sym_visibility = "private"}> ({
    ^bb0(%arg41: !algebra.field<"bls12-381.fr">, %arg42: !algebra.field<"bls12-381.fr">, %arg43: !algebra.field<"bls12-381.fr">):
      %91 = "algebra.field_subtract"(%arg42, %arg41) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %92 = "algebra.field_multiply"(%91, %arg43) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %93 = "algebra.field_add"(%arg41, %92) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%93) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", sym_visibility = "private"}> ({
    ^bb0(%arg38: !runtime.scope, %arg39: !algebra.field_vector<"bls12-381.fr">, %arg40: !algebra.field<"bls12-381.fr">):
      %86 = "exec.apply"(%arg38, %arg39, %arg40) <{binding = @zkl_binding_11, parameters = [], site = "s0"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%86)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%87: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %88 = "exec.returned"(%87) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%88) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%89: !exec.stop):  // pred: ^bb0
      %90 = "exec.failed"(%89) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%90) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6310h7072696d6974697665736h766563746f726h617070656e64", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc", sym_visibility = "private"}> ({
    ^bb0(%arg34: !runtime.scope, %arg35: !algebra.field_vector<"bls12-381.fr">, %arg36: !algebra.field_vector<"bls12-381.fr">, %arg37: !algebra.field<"bls12-381.fr">):
      %60 = "exec.apply"(%arg34, %arg36) <{binding = @zkl_binding_1, parameters = [], site = "s1"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%60)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%61: ui64):  // pred: ^bb0
      %62 = "exec.apply"(%arg34) <{binding = @zkl_binding_0, parameters = ["1"], site = "s2"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%62)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%63: !exec.stop):  // 10 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb6, ^bb7, ^bb9, ^bb10, ^bb12, ^bb13
      %64 = "exec.failed"(%63) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%64) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%65: ui64):  // pred: ^bb1
      %66 = "func.call"(%arg34, %arg35, %61, %65) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655}> {runtime.site = "s3"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%66)[^bb4, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb4(%67: i1):  // pred: ^bb3
      %68 = "exec.test"(%arg34, %67) <{site = "s6"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%68)[^bb5, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb5(%69: i1):  // pred: ^bb4
      "cf.cond_br"(%69)[^bb6, ^bb7] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb6:  // pred: ^bb5
      %70 = "runtime.enter_scope"(%arg34, %arg35, %arg36, %arg37) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "then", site = "s6"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%70)[^bb9, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // pred: ^bb5
      %71 = "runtime.enter_scope"(%arg34, %arg35, %arg36, %arg37) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "else", site = "s6"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%71)[^bb12, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb8(%72: i1):  // 2 preds: ^bb11, ^bb14
      %73 = "exec.returned"(%72) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%73) : (!exec.outcome<(i1)>) -> ()
    ^bb9(%74: !runtime.scope):  // pred: ^bb6
      %75 = "func.call"(%74, %arg35, %arg36, %arg37) <{callee = @zkl_control_13}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>
      %76 = "runtime.exit_scope"(%74, %75) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%76)[^bb10, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb10(%77: !runtime.transfer<(i1)>):  // pred: ^bb9
      %78 = "runtime.accept_transfer"(%arg34, %77) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%78)[^bb11, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb11(%79: i1):  // pred: ^bb10
      "cf.br"(%79)[^bb8] : (i1) -> ()
    ^bb12(%80: !runtime.scope):  // pred: ^bb7
      %81 = "func.call"(%80, %arg35, %arg36, %arg37) <{callee = @zkl_control_14}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>
      %82 = "runtime.exit_scope"(%80, %81) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%82)[^bb13, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb13(%83: !runtime.transfer<(i1)>):  // pred: ^bb12
      %84 = "runtime.accept_transfer"(%arg34, %83) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%84)[^bb14, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb14(%85: i1):  // pred: ^bb13
      "cf.br"(%85)[^bb8] : (i1) -> ()
    }) {runtime.origin = ["s8h73756d636865636b5h636865636b", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_13", sym_visibility = "private"}> ({
    ^bb0(%arg30: !runtime.scope, %arg31: !algebra.field_vector<"bls12-381.fr">, %arg32: !algebra.field_vector<"bls12-381.fr">, %arg33: !algebra.field<"bls12-381.fr">):
      %55 = "func.call"(%arg30, %arg31, %arg32, %arg33) <{callee = @zkl_3b67bb5451d0deeed7ab9379c12e7c154a5c16946b7db9b65bc0d4be6b613f1d}> {runtime.site = "s7"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>
      "exec.dispatch"(%55)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%56: i1):  // pred: ^bb0
      %57 = "exec.complete"(%arg30, %56) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%57) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%58: !exec.stop):  // pred: ^bb0
      %59 = "exec.failed"(%58) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%59) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_14", sym_visibility = "private"}> ({
    ^bb0(%arg26: !runtime.scope, %arg27: !algebra.field_vector<"bls12-381.fr">, %arg28: !algebra.field_vector<"bls12-381.fr">, %arg29: !algebra.field<"bls12-381.fr">):
      %50 = "exec.boolean"(%arg26) <{site = "s9", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%50)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%51: i1):  // pred: ^bb0
      %52 = "exec.complete"(%arg26, %51) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%52) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%53: !exec.stop):  // pred: ^bb0
      %54 = "exec.failed"(%53) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%54) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_3b67bb5451d0deeed7ab9379c12e7c154a5c16946b7db9b65bc0d4be6b613f1d", sym_visibility = "private"}> ({
    ^bb0(%arg22: !runtime.scope, %arg23: !algebra.field_vector<"bls12-381.fr">, %arg24: !algebra.field_vector<"bls12-381.fr">, %arg25: !algebra.field<"bls12-381.fr">):
      %29 = "exec.apply"(%arg22, %arg24) <{binding = @zkl_binding_1, parameters = [], site = "s1"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%29)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%30: ui64):  // pred: ^bb0
      %31 = "exec.apply"(%arg22) <{binding = @zkl_binding_0, parameters = ["1"], site = "s2"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%31)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%32: !exec.stop):  // 7 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7
      %33 = "exec.failed"(%32) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%33) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%34: ui64):  // pred: ^bb1
      %35 = "func.call"(%arg22, %arg23, %30, %34) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a}> {runtime.site = "s3"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%35)[^bb4, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb4(%36: !algebra.field_vector<"bls12-381.fr">, %37: ui64, %38: ui64):  // pred: ^bb3
      %39 = "func.call"(%arg22, %36, %37, %38, %arg24) <{callee = @zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be}> {runtime.site = "s6"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%39)[^bb5, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb5(%40: !algebra.field_vector<"bls12-381.fr">, %41: ui64, %42: ui64):  // pred: ^bb4
      %43 = "exec.compute"(%arg22, %40, %41, %42) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33, site = "s8"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%43)[^bb6, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb6(%44: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb5
      %45 = "exec.apply"(%arg22, %44) <{binding = @zkl_binding_8, parameters = [], site = "s9"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%45)[^bb7, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb7(%46: !algebra.field<"bls12-381.fr">):  // pred: ^bb6
      %47 = "exec.apply"(%arg22, %46, %arg25) <{binding = @zkl_binding_12, parameters = [], site = "s11"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>
      "exec.dispatch"(%47)[^bb8, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb8(%48: i1):  // pred: ^bb7
      %49 = "exec.returned"(%48) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%49) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.origin = ["s8h73756d636865636b11h636865636b5f7461626c65", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be", sym_visibility = "private"}> ({
    ^bb0(%arg17: !runtime.scope, %arg18: !algebra.field_vector<"bls12-381.fr">, %arg19: ui64, %arg20: ui64, %arg21: !algebra.field_vector<"bls12-381.fr">):
      %22 = "func.call"(%arg17, %arg18, %arg19, %arg20, %arg21) <{callee = @zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2}> {runtime.site = "s0"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%22)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb1(%23: !algebra.field_vector<"bls12-381.fr">, %24: ui64, %25: ui64):  // pred: ^bb0
      %26 = "exec.returned"(%23, %24, %25) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%26) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb2(%27: !exec.stop):  // pred: ^bb0
      %28 = "exec.failed"(%27) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%28) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e65617210h6669785f707265666978", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_195a79478f48dffc2a6917273d8317df0fabae786920a46fa2ac6b2737144299", sym_visibility = "private"}> ({
    ^bb0(%arg12: !runtime.scope, %arg13: !algebra.field_vector<"bls12-381.fr">, %arg14: ui64, %arg15: ui64, %arg16: !algebra.field<"bls12-381.fr">):
      %15 = "func.call"(%arg12, %arg13, %arg14, %arg15, %arg16) <{callee = @zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d}> {runtime.site = "s2"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%15)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb1(%16: !algebra.field_vector<"bls12-381.fr">, %17: ui64, %18: ui64):  // pred: ^bb0
      %19 = "exec.returned"(%16, %17, %18) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%19) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb2(%20: !exec.stop):  // pred: ^bb0
      %21 = "exec.failed"(%20) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%21) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["zks_50b2228592370f9a2bce2e71277fbb9bf36d691d6ece4416923708e3a0c063ae", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2", sym_visibility = "private"}> ({
    ^bb0(%arg7: !runtime.scope, %arg8: !algebra.field_vector<"bls12-381.fr">, %arg9: ui64, %arg10: ui64, %arg11: !algebra.field_vector<"bls12-381.fr">):
      %8 = "exec.fold"(%arg7, %arg11, %arg8, %arg9, %arg10) <{domain = @finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_domain, site = "s0", step = @finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%8)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb1(%9: !algebra.field_vector<"bls12-381.fr">, %10: ui64, %11: ui64):  // pred: ^bb0
      %12 = "exec.returned"(%9, %10, %11) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%12) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb2(%13: !exec.stop):  // pred: ^bb0
      %14 = "exec.failed"(%13) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%14) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b636h66696e6974654h666f6c64", []]} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_domain", sym_visibility = "private"}> ({
    ^bb0(%arg6: !algebra.field_vector<"bls12-381.fr">):
      %7 = "data.domain_elements"(%arg6) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%7) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body", sym_visibility = "private"}> ({
    ^bb0(%arg0: !runtime.scope, %arg1: !algebra.field_vector<"bls12-381.fr">, %arg2: ui64, %arg3: ui64, %arg4: !algebra.field<"bls12-381.fr">, %arg5: !algebra.field_vector<"bls12-381.fr">):
      %0 = "func.call"(%arg0, %arg1, %arg2, %arg3, %arg4) <{callee = @zkl_195a79478f48dffc2a6917273d8317df0fabae786920a46fa2ac6b2737144299}> {runtime.site = "body"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb1(%1: !algebra.field_vector<"bls12-381.fr">, %2: ui64, %3: ui64):  // pred: ^bb0
      %4 = "exec.returned"(%1, %2, %3) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%4) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb2(%5: !exec.stop):  // pred: ^bb0
      %6 = "exec.failed"(%5) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%6) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body", []]} : () -> ()
    "relation.declare"() <{formula = @zkf_9ca6c98faa0d00ed80eb608a89db1544ad71443a8944af6ac99e6fd78cb3660b, key = "zkl_733a9984be750c90a7e40f8fc81c10a284cb9ecaf745c62024f07f1a3806a10c", kind = "zkc.language.formula/0", purposes = ["parameter", "parameter"], revision = "fef4042b36eb69492320800630ec190760414ad82c4859a47d2aac19bf270e5c", signature = (!algebra.field_vector<"bls12-381.fr">, ui64) -> i1, sym_name = "zkl_733a9984be750c90a7e40f8fc81c10a284cb9ecaf745c62024f07f1a3806a10c"}> : () -> ()
    "relation.declare"() <{formula = @zkf_116f3285742dd1275b8149c69b78a6713cd6256a8af715be7c346da1c793a766, key = "zkl_1c2e12f894c2f4b39d38adc87f1dedbaf7856eb6985dba89eb2261c88030aef2", kind = "zkc.language.formula/0", purposes = ["parameter", "statement"], revision = "a60d910bb6e61b3f4d146e863f02155af13cfbdf8ddd5538ee0d89004c93bd71", signature = (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "zkl_1c2e12f894c2f4b39d38adc87f1dedbaf7856eb6985dba89eb2261c88030aef2"}> : () -> ()
    "relation.declare"() <{formula = @zkf_654a0e58b11e83f398996b9e830df00890bec0f8dc08a65c5750d6d9c759b643, key = "zkl_11c80248216cbe579879aabc5c6f64d5f465a4db68261d6da29eab7c94d7679c", kind = "zkc.language.formula/0", purposes = ["parameter", "parameter", "parameter", "statement"], revision = "2c4b933d7a6995f34b80f29d1478e98e81ee53f22c19789c1c06958fba515a0f", signature = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "zkl_11c80248216cbe579879aabc5c6f64d5f465a4db68261d6da29eab7c94d7679c"}> : () -> ()
  }) : () -> ()
}) : () -> ()

