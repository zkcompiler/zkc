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
    ^bb0(%arg157: !algebra.field_vector<"bls12-381.fr">, %arg158: !algebra.field<"bls12-381.fr">, %arg159: ui64, %arg160: !protocol.service_ref<"random.bls12-381.fr/0">):
      %407 = "data.index"() <{value = "1"}> : () -> ui64
      %408:3 = "protocol.local_call"(%arg157, %arg159, %407) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a, role = "role00000000", site = "s1"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      %409:2 = "protocol.local_call"(%arg158) <{callee = @zkl_c0a3a2b8b5f989e0e9c138a171631d20dc8bd296769b6ee7636d2d79a8518ba0, role = "role00000001", site = "s3"}> : (!algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %410:6 = "protocol.apply"(%408#0, %408#1, %408#2, %409#0, %409#1, %arg159, %arg160) <{callee = @zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5, roles = ["role00000000", "role00000001"], site = "label_726564756365"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %411 = "protocol.local_call"(%arg157, %410#4, %410#5) <{callee = @zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc, role = "role00000001", site = "s9"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "protocol.return"(%411) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64) -> i1, sym_name = "zkf_9ca6c98faa0d00ed80eb608a89db1544ad71443a8944af6ac99e6fd78cb3660b", sym_visibility = "private"}> ({
    ^bb0(%arg155: !algebra.field_vector<"bls12-381.fr">, %arg156: ui64):
      %400 = "data.dim"(%arg155) <{axis = 0 : i64}> : (!algebra.field_vector<"bls12-381.fr">) -> ui64
      %401 = "data.index_power_of_two"(%400, %arg156) : (ui64, ui64) -> i1
      %402 = "data.index"() <{value = "2"}> : () -> ui64
      %403 = "data.index_less"(%402, %arg156) : (ui64, ui64) -> i1
      %404 = "arith.constant"() <{value = false}> : () -> i1
      %405 = "arith.cmpi"(%403, %404) <{predicate = 0 : i64}> : (i1, i1) -> i1
      %406 = "arith.andi"(%401, %405) : (i1, i1) -> i1
      "func.return"(%406) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "zkf_116f3285742dd1275b8149c69b78a6713cd6256a8af715be7c346da1c793a766", sym_visibility = "private"}> ({
    ^bb0(%arg153: !algebra.field_vector<"bls12-381.fr">, %arg154: !algebra.field<"bls12-381.fr">):
      %398 = "func.call"(%arg153) <{callee = @zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e}> : (!algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %399 = "algebra.field_equal"(%arg154, %398) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "func.return"(%399) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e", sym_visibility = "private"}> ({
    ^bb0(%arg152: !algebra.field_vector<"bls12-381.fr">):
      %396 = "algebra.constant"() <{value = "0"}> : () -> !algebra.field<"bls12-381.fr">
      %397 = "algebra.finite_fold"(%arg152, %396) <{domain = @finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_domain, step = @finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_body}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%397) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_domain", sym_visibility = "private"}> ({
    ^bb0(%arg151: !algebra.field_vector<"bls12-381.fr">):
      %395 = "data.domain_elements"(%arg151) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%395) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_body", sym_visibility = "private"}> ({
    ^bb0(%arg148: !algebra.field<"bls12-381.fr">, %arg149: !algebra.field<"bls12-381.fr">, %arg150: !algebra.field_vector<"bls12-381.fr">):
      %394 = "func.call"(%arg148, %arg149) <{callee = @zkl_3fc17a64a5bb6e75192d0a1362e9954f0d434a10d0f93e319db6b516835a1005}> : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%394) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_3fc17a64a5bb6e75192d0a1362e9954f0d434a10d0f93e319db6b516835a1005", sym_visibility = "private"}> ({
    ^bb0(%arg146: !algebra.field<"bls12-381.fr">, %arg147: !algebra.field<"bls12-381.fr">):
      %393 = "algebra.field_add"(%arg146, %arg147) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%393) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", sym_visibility = "private"}> ({
    ^bb0(%arg142: !runtime.scope, %arg143: !algebra.field_vector<"bls12-381.fr">, %arg144: ui64, %arg145: ui64):
      %374 = "func.call"(%arg142, %arg143, %arg144, %arg145) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655}> {runtime.site = "s0"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%374)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%375: i1):  // pred: ^bb0
      %376 = "exec.test"(%arg142, %375) <{site = "s1"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%376)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%377: !exec.stop):  // 8 preds: ^bb0, ^bb1, ^bb4, ^bb5, ^bb7, ^bb8, ^bb10, ^bb11
      %378 = "exec.failed"(%377) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%378) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb3(%379: i1):  // pred: ^bb1
      "cf.cond_br"(%379)[^bb4, ^bb5] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb4:  // pred: ^bb3
      %380 = "runtime.enter_scope"(%arg142) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%380)[^bb7, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb5:  // pred: ^bb3
      %381 = "runtime.enter_scope"(%arg142) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%381)[^bb10, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // 2 preds: ^bb9, ^bb12
      %382 = "exec.returned"(%arg143, %arg144, %arg145) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%382) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb7(%383: !runtime.scope):  // pred: ^bb4
      %384 = "func.call"(%383) <{callee = @zkl_control_0}> : (!runtime.scope) -> !exec.outcome<>
      %385 = "runtime.exit_scope"(%383, %384) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%385)[^bb8, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb8(%386: !runtime.transfer<>):  // pred: ^bb7
      %387 = "runtime.accept_transfer"(%arg142, %386) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%387)[^bb9, ^bb2] : (!exec.outcome<>) -> ()
    ^bb9:  // pred: ^bb8
      "cf.br"()[^bb6] : () -> ()
    ^bb10(%388: !runtime.scope):  // pred: ^bb5
      %389 = "func.call"(%388) <{callee = @zkl_control_1}> : (!runtime.scope) -> !exec.outcome<>
      %390 = "runtime.exit_scope"(%388, %389) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%390)[^bb11, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb11(%391: !runtime.transfer<>):  // pred: ^bb10
      %392 = "runtime.accept_transfer"(%arg142, %391) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%392)[^bb12, ^bb2] : (!exec.outcome<>) -> ()
    ^bb12:  // pred: ^bb11
      "cf.br"()[^bb6] : () -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561725h7461626c65", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_0", sym_visibility = "private"}> ({
    ^bb0(%arg141: !runtime.scope):
      %373 = "exec.complete"(%arg141) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%373) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_1", sym_visibility = "private"}> ({
    ^bb0(%arg140: !runtime.scope):
      %370 = "exec.reject"(%arg140) <{reason = "reject", site = "s1_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%370)[^bb1] : (!exec.stop) -> ()
    ^bb1(%371: !exec.stop):  // pred: ^bb0
      %372 = "exec.failed"(%371) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%372) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", sym_visibility = "private"}> ({
    ^bb0(%arg136: !runtime.scope, %arg137: !algebra.field_vector<"bls12-381.fr">, %arg138: ui64, %arg139: ui64):
      %312 = "exec.apply"(%arg136) <{binding = @zkl_binding_0, parameters = ["0"], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%312)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%313: ui64):  // pred: ^bb0
      %314 = "func.call"(%arg136, %313, %arg139) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s1"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%314)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%315: !exec.stop):  // 23 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12, ^bb15, ^bb16, ^bb17, ^bb18, ^bb19, ^bb21, ^bb22, ^bb25, ^bb26, ^bb28, ^bb29, ^bb31, ^bb32
      %316 = "exec.failed"(%315) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%316) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%317: i1):  // pred: ^bb1
      %318 = "exec.test"(%arg136, %317) <{site = "s3"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%318)[^bb4, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb4(%319: i1):  // pred: ^bb3
      "cf.cond_br"(%319)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %320 = "runtime.enter_scope"(%arg136, %arg138) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "then", site = "s3"}> : (!runtime.scope, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%320)[^bb8, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %321 = "runtime.enter_scope"(%arg136, %arg138) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "else", site = "s3"}> : (!runtime.scope, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%321)[^bb11, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7(%322: i1):  // 2 preds: ^bb10, ^bb13
      %323 = "exec.test"(%arg136, %322) <{site = "s11"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%323)[^bb14, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb8(%324: !runtime.scope):  // pred: ^bb5
      %325 = "func.call"(%324, %arg138) <{callee = @zkl_control_2}> : (!runtime.scope, ui64) -> !exec.outcome<(i1)>
      %326 = "runtime.exit_scope"(%324, %325) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%326)[^bb9, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb9(%327: !runtime.transfer<(i1)>):  // pred: ^bb8
      %328 = "runtime.accept_transfer"(%arg136, %327) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%328)[^bb10, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb10(%329: i1):  // pred: ^bb9
      "cf.br"(%329)[^bb7] : (i1) -> ()
    ^bb11(%330: !runtime.scope):  // pred: ^bb6
      %331 = "func.call"(%330, %arg138) <{callee = @zkl_control_3}> : (!runtime.scope, ui64) -> !exec.outcome<(i1)>
      %332 = "runtime.exit_scope"(%330, %331) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%332)[^bb12, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb12(%333: !runtime.transfer<(i1)>):  // pred: ^bb11
      %334 = "runtime.accept_transfer"(%arg136, %333) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%334)[^bb13, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb13(%335: i1):  // pred: ^bb12
      "cf.br"(%335)[^bb7] : (i1) -> ()
    ^bb14(%336: i1):  // pred: ^bb7
      "cf.cond_br"(%336)[^bb15, ^bb16] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb15:  // pred: ^bb14
      %337 = "runtime.enter_scope"(%arg136, %arg137, %arg139) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "then", site = "s11"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%337)[^bb18, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb16:  // pred: ^bb14
      %338 = "runtime.enter_scope"(%arg136, %arg137, %arg139) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "else", site = "s11"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%338)[^bb21, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb17(%339: i1):  // 2 preds: ^bb20, ^bb23
      %340 = "exec.test"(%arg136, %339) <{site = "s22"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%340)[^bb24, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb18(%341: !runtime.scope):  // pred: ^bb15
      %342 = "func.call"(%341, %arg137, %arg139) <{callee = @zkl_control_4}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>
      %343 = "runtime.exit_scope"(%341, %342) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%343)[^bb19, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb19(%344: !runtime.transfer<(i1)>):  // pred: ^bb18
      %345 = "runtime.accept_transfer"(%arg136, %344) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%345)[^bb20, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb20(%346: i1):  // pred: ^bb19
      "cf.br"(%346)[^bb17] : (i1) -> ()
    ^bb21(%347: !runtime.scope):  // pred: ^bb16
      %348 = "func.call"(%347, %arg137, %arg139) <{callee = @zkl_control_5}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>
      %349 = "runtime.exit_scope"(%347, %348) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%349)[^bb22, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb22(%350: !runtime.transfer<(i1)>):  // pred: ^bb21
      %351 = "runtime.accept_transfer"(%arg136, %350) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%351)[^bb23, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb23(%352: i1):  // pred: ^bb22
      "cf.br"(%352)[^bb17] : (i1) -> ()
    ^bb24(%353: i1):  // pred: ^bb17
      "cf.cond_br"(%353)[^bb25, ^bb26] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb25:  // pred: ^bb24
      %354 = "runtime.enter_scope"(%arg136, %arg137, %arg138, %arg139) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "then", site = "s22"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%354)[^bb28, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb26:  // pred: ^bb24
      %355 = "runtime.enter_scope"(%arg136, %arg137, %arg138, %arg139) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "else", site = "s22"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%355)[^bb31, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb27(%356: i1):  // 2 preds: ^bb30, ^bb33
      %357 = "exec.returned"(%356) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%357) : (!exec.outcome<(i1)>) -> ()
    ^bb28(%358: !runtime.scope):  // pred: ^bb25
      %359 = "func.call"(%358, %arg137, %arg138, %arg139) <{callee = @zkl_control_6}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      %360 = "runtime.exit_scope"(%358, %359) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%360)[^bb29, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb29(%361: !runtime.transfer<(i1)>):  // pred: ^bb28
      %362 = "runtime.accept_transfer"(%arg136, %361) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%362)[^bb30, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb30(%363: i1):  // pred: ^bb29
      "cf.br"(%363)[^bb27] : (i1) -> ()
    ^bb31(%364: !runtime.scope):  // pred: ^bb26
      %365 = "func.call"(%364, %arg137, %arg138, %arg139) <{callee = @zkl_control_7}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      %366 = "runtime.exit_scope"(%364, %365) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%366)[^bb32, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb32(%367: !runtime.transfer<(i1)>):  // pred: ^bb31
      %368 = "runtime.accept_transfer"(%arg136, %367) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%368)[^bb33, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb33(%369: i1):  // pred: ^bb32
      "cf.br"(%369)[^bb27] : (i1) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_2", sym_visibility = "private"}> ({
    ^bb0(%arg134: !runtime.scope, %arg135: ui64):
      %305 = "exec.apply"(%arg134) <{binding = @zkl_binding_0, parameters = ["64"], site = "s4"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%305)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%306: ui64):  // pred: ^bb0
      %307 = "func.call"(%arg134, %arg135, %306) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s5"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%307)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%308: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %309 = "exec.failed"(%308) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%309) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%310: i1):  // pred: ^bb1
      %311 = "exec.complete"(%arg134, %310) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%311) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_3", sym_visibility = "private"}> ({
    ^bb0(%arg132: !runtime.scope, %arg133: ui64):
      %300 = "exec.boolean"(%arg132) <{site = "s7", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%300)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%301: i1):  // pred: ^bb0
      %302 = "exec.complete"(%arg132, %301) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%302) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%303: !exec.stop):  // pred: ^bb0
      %304 = "exec.failed"(%303) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%304) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_4", sym_visibility = "private"}> ({
    ^bb0(%arg129: !runtime.scope, %arg130: !algebra.field_vector<"bls12-381.fr">, %arg131: ui64):
      %289 = "exec.apply"(%arg129, %arg130) <{binding = @zkl_binding_1, parameters = [], site = "s12"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%289)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%290: ui64):  // pred: ^bb0
      %291 = "exec.apply"(%arg129, %290, %arg131) <{binding = @zkl_binding_2, parameters = [], site = "s13"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%291)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%292: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %293 = "exec.failed"(%292) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%293) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%294: ui64):  // pred: ^bb1
      %295 = "exec.apply"(%arg129) <{binding = @zkl_binding_0, parameters = ["0"], site = "s14"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%295)[^bb4, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%296: ui64):  // pred: ^bb3
      %297 = "exec.apply"(%arg129, %294, %296) <{binding = @zkl_binding_3, parameters = [], site = "s15"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%297)[^bb5, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb5(%298: i1):  // pred: ^bb4
      %299 = "exec.complete"(%arg129, %298) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%299) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_5", sym_visibility = "private"}> ({
    ^bb0(%arg126: !runtime.scope, %arg127: !algebra.field_vector<"bls12-381.fr">, %arg128: ui64):
      %284 = "exec.boolean"(%arg126) <{site = "s17", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%284)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%285: i1):  // pred: ^bb0
      %286 = "exec.complete"(%arg126, %285) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%286) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%287: !exec.stop):  // pred: ^bb0
      %288 = "exec.failed"(%287) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%288) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_6", sym_visibility = "private"}> ({
    ^bb0(%arg122: !runtime.scope, %arg123: !algebra.field_vector<"bls12-381.fr">, %arg124: ui64, %arg125: ui64):
      %273 = "exec.apply"(%arg122, %arg123) <{binding = @zkl_binding_1, parameters = [], site = "s23"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%273)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%274: ui64):  // pred: ^bb0
      %275 = "exec.apply"(%arg122, %274, %arg125) <{binding = @zkl_binding_4, parameters = [], site = "s24"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%275)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%276: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %277 = "exec.failed"(%276) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%277) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%278: ui64):  // pred: ^bb1
      %279 = "func.call"(%arg122, %arg124) <{callee = @s3h7a6b6311h6d756c74696c696e6561724h726f7773}> {runtime.site = "s25"} : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%279)[^bb4, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%280: ui64):  // pred: ^bb3
      %281 = "exec.apply"(%arg122, %278, %280) <{binding = @zkl_binding_3, parameters = [], site = "s26"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%281)[^bb5, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb5(%282: i1):  // pred: ^bb4
      %283 = "exec.complete"(%arg122, %282) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%283) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_7", sym_visibility = "private"}> ({
    ^bb0(%arg118: !runtime.scope, %arg119: !algebra.field_vector<"bls12-381.fr">, %arg120: ui64, %arg121: ui64):
      %268 = "exec.boolean"(%arg118) <{site = "s28", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%268)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%269: i1):  // pred: ^bb0
      %270 = "exec.complete"(%arg118, %269) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%270) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%271: !exec.stop):  // pred: ^bb0
      %272 = "exec.failed"(%271) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%272) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "s3h7a6b637h696e64696365734h6c657373", sym_visibility = "private"}> ({
    ^bb0(%arg115: !runtime.scope, %arg116: ui64, %arg117: ui64):
      %263 = "exec.apply"(%arg115, %arg116, %arg117) <{binding = @zkl_binding_5, parameters = [], site = "s0"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%263)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%264: i1):  // pred: ^bb0
      %265 = "exec.returned"(%264) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%265) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%266: !exec.stop):  // pred: ^bb0
      %267 = "exec.failed"(%266) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%267) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.origin = ["s3h7a6b637h696e64696365734h6c657373", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "s3h7a6b6311h6d756c74696c696e6561724h726f7773", sym_visibility = "private"}> ({
    ^bb0(%arg113: !runtime.scope, %arg114: ui64):
      %216 = "exec.apply"(%arg113) <{binding = @zkl_binding_0, parameters = ["64"], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%216)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%217: ui64):  // pred: ^bb0
      %218 = "func.call"(%arg113, %arg114, %217) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s1"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%218)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%219: !exec.stop):  // 14 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12, ^bb14, ^bb15, ^bb19, ^bb21
      %220 = "exec.failed"(%219) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%220) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%221: i1):  // pred: ^bb1
      %222 = "exec.test"(%arg113, %221) <{site = "s2"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%222)[^bb4, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb4(%223: i1):  // pred: ^bb3
      "cf.cond_br"(%223)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %224 = "runtime.enter_scope"(%arg113) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s2"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%224)[^bb8, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %225 = "runtime.enter_scope"(%arg113) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s2"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%225)[^bb11, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // 2 preds: ^bb10, ^bb13
      %226 = "exec.apply"(%arg113) <{binding = @zkl_binding_0, parameters = ["1"], site = "s3"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%226)[^bb14, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb8(%227: !runtime.scope):  // pred: ^bb5
      %228 = "func.call"(%227) <{callee = @zkl_control_8}> : (!runtime.scope) -> !exec.outcome<>
      %229 = "runtime.exit_scope"(%227, %228) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%229)[^bb9, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb9(%230: !runtime.transfer<>):  // pred: ^bb8
      %231 = "runtime.accept_transfer"(%arg113, %230) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%231)[^bb10, ^bb2] : (!exec.outcome<>) -> ()
    ^bb10:  // pred: ^bb9
      "cf.br"()[^bb7] : () -> ()
    ^bb11(%232: !runtime.scope):  // pred: ^bb6
      %233 = "func.call"(%232) <{callee = @zkl_control_9}> : (!runtime.scope) -> !exec.outcome<>
      %234 = "runtime.exit_scope"(%232, %233) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%234)[^bb12, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb12(%235: !runtime.transfer<>):  // pred: ^bb11
      %236 = "runtime.accept_transfer"(%arg113, %235) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%236)[^bb13, ^bb2] : (!exec.outcome<>) -> ()
    ^bb13:  // pred: ^bb12
      "cf.br"()[^bb7] : () -> ()
    ^bb14(%237: ui64):  // pred: ^bb7
      %238 = "exec.apply"(%arg113) <{binding = @zkl_binding_0, parameters = ["0"], site = "s5"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%238)[^bb15, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb15(%239: ui64):  // pred: ^bb14
      %240 = "exec.range"(%arg113, %239, %arg114) <{site = "s6"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%240)[^bb16, ^bb2] : (!exec.outcome<(i64, i64)>) -> ()
    ^bb16(%241: i64, %242: i64):  // pred: ^bb15
      %243 = "runtime.borrow_transfer"(%arg113, %237) : (!runtime.scope, ui64) -> !runtime.transfer<(ui64)>
      "cf.br"(%241, %243)[^bb17] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb17(%244: i64, %245: !runtime.transfer<(ui64)>):  // 2 preds: ^bb16, ^bb20
      %246 = "arith.cmpi"(%244, %242) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%246, %245)[^bb18, ^bb19] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(ui64)>) -> ()
    ^bb18:  // pred: ^bb17
      %247 = "runtime.iteration"(%arg113, %244) <{site = "s6"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%247)[^bb22, ^bb21] : (!exec.outcome<(ui64)>) -> ()
    ^bb19(%248: !runtime.transfer<(ui64)>):  // pred: ^bb17
      %249 = "runtime.accept_transfer"(%arg113, %248) : (!runtime.scope, !runtime.transfer<(ui64)>) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%249)[^bb25, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb20(%250: !runtime.transfer<(ui64)>):  // pred: ^bb24
      %251 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %252 = "arith.addi"(%244, %251) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%252, %250)[^bb17] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb21(%253: !exec.stop):  // 3 preds: ^bb18, ^bb22, ^bb23
      "runtime.release_transfer"(%245) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%253)[^bb2] : (!exec.stop) -> ()
    ^bb22(%254: ui64):  // pred: ^bb18
      %255 = "runtime.transfer_values"(%245) : (!runtime.transfer<(ui64)>) -> ui64
      %256 = "runtime.enter_scope"(%arg113, %244, %254, %255) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 2>, site = "s6"}> : (!runtime.scope, i64, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%256)[^bb23, ^bb21] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb23(%257: !runtime.scope):  // pred: ^bb22
      %258 = "func.call"(%257, %254, %255) <{callee = @zkl_control_10}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      %259 = "runtime.exit_scope"(%257, %258) : (!runtime.scope, !exec.outcome<(ui64)>) -> !exec.outcome<(!runtime.transfer<(ui64)>)>
      "exec.dispatch"(%259)[^bb24, ^bb21] : (!exec.outcome<(!runtime.transfer<(ui64)>)>) -> ()
    ^bb24(%260: !runtime.transfer<(ui64)>):  // pred: ^bb23
      "runtime.release_transfer"(%245) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%260)[^bb20] : (!runtime.transfer<(ui64)>) -> ()
    ^bb25(%261: ui64):  // pred: ^bb19
      %262 = "exec.returned"(%261) : (ui64) -> !exec.outcome<(ui64)>
      "func.return"(%262) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561724h726f7773", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_8", sym_visibility = "private"}> ({
    ^bb0(%arg112: !runtime.scope):
      %215 = "exec.complete"(%arg112) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%215) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_9", sym_visibility = "private"}> ({
    ^bb0(%arg111: !runtime.scope):
      %212 = "exec.reject"(%arg111) <{reason = "reject", site = "s2_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%212)[^bb1] : (!exec.stop) -> ()
    ^bb1(%213: !exec.stop):  // pred: ^bb0
      %214 = "exec.failed"(%213) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%214) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "zkl_control_10", sym_visibility = "private"}> ({
    ^bb0(%arg108: !runtime.scope, %arg109: ui64, %arg110: ui64):
      %205 = "exec.apply"(%arg108) <{binding = @zkl_binding_0, parameters = ["2"], site = "s7"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%205)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%206: ui64):  // pred: ^bb0
      %207 = "exec.apply"(%arg108, %arg110, %206) <{binding = @zkl_binding_6, parameters = [], site = "s8"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%207)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%208: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %209 = "exec.failed"(%208) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%209) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%210: ui64):  // pred: ^bb1
      %211 = "exec.complete"(%arg108, %210) : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "func.return"(%211) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_c0a3a2b8b5f989e0e9c138a171631d20dc8bd296769b6ee7636d2d79a8518ba0", sym_visibility = "private"}> ({
    ^bb0(%arg106: !runtime.scope, %arg107: !algebra.field<"bls12-381.fr">):
      %200 = "exec.apply"(%arg106) <{binding = @zkl_binding_7, parameters = [], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%200)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%201: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %202 = "exec.returned"(%201, %arg107) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%202) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%203: !exec.stop):  // pred: ^bb0
      %204 = "exec.failed"(%203) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%204) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s8h73756d636865636b7h70656e64696e67", []]} : () -> ()
    "protocol.func"() <{contracts = [["input", "shape", [@zkl_8c866415d5a42d7cb60d6b39dd52568c20001248a901906f13a3d5d9dd8f74ac, [["input", 0, "role00000000"], ["input", 1, "role00000000"], ["input", 2, "role00000000"]]], unit, unit], ["continuation", "initial_sum", [@zkl_f03c5af270c09f9d5e832cdb0dc1d71151cebecfaaa08c6cacd997dde03860e9, [["input", 0, "role00000000"], ["input", 1, "role00000000"], ["input", 2, "role00000000"], ["input", 3, "role00000001"], ["input", 4, "role00000001"]]], [@zkl_f03c5af270c09f9d5e832cdb0dc1d71151cebecfaaa08c6cacd997dde03860e9, [["input", 0, "role00000000"], ["input", 1, "role00000000"], ["input", 2, "role00000000"], ["output", 4, "role00000001"], ["output", 5, "role00000001"]]], unit]], function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), input_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"], ["role00000000", "role00000001"], ["role00000001"]], origin = ["sumcheck::Reduce", [["F", ["field", "bls12-381.fr"]], ["Max", ["nat", "2"]]]], output_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5"}> ({
    ^bb0(%arg91: !algebra.field_vector<"bls12-381.fr">, %arg92: ui64, %arg93: ui64, %arg94: !algebra.field_vector<"bls12-381.fr">, %arg95: !algebra.field<"bls12-381.fr">, %arg96: ui64, %arg97: !protocol.service_ref<"random.bls12-381.fr/0">):
      %171 = "func.call"(%arg91, %arg92, %arg93) <{callee = @zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %172 = "data.index"() <{value = "1"}> : () -> ui64
      %173 = "data.index_equal"(%171, %172) : (ui64, ui64) -> i1
      "protocol.guard"(%173) <{owner = "role00000000", site = "s3"}> : (i1) -> ()
      %174 = "func.call"(%arg91, %arg92, %arg93) <{callee = @zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %175 = "protocol.local_call"(%174, %arg96) <{callee = @s3h7a6b637h696e64696365734h6c657373, role = "role00000000", site = "s5"}> : (ui64, ui64) -> i1
      %176 = "arith.constant"() <{value = false}> : () -> i1
      %177 = "arith.cmpi"(%175, %176) <{predicate = 0 : i64}> : (i1, i1) -> i1
      "protocol.guard"(%177) <{owner = "role00000000", site = "s8"}> : (i1) -> ()
      %178 = "protocol.local_call"() <{callee = @zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f, role = "role00000000", site = "s10"}> : () -> !algebra.field_vector<"bls12-381.fr">
      %179:2 = "protocol.local_call"(%arg94, %arg95) <{callee = @zkl_e8df957aab384c1d5416600c13a571512206e97abfbf6e0e9cddac5c84860d07, role = "role00000001", site = "s12"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %180:6 = "protocol.repeat"(%arg96, %arg91, %arg92, %arg93, %178, %179#0, %179#1, %arg97) <{carried = 6 : i64, carried_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"]], maximum = 2 : i64, roles = ["role00000000", "role00000001"], site = "s18"}> ({
      ^bb0(%arg98: ui64, %arg99: !algebra.field_vector<"bls12-381.fr">, %arg100: ui64, %arg101: ui64, %arg102: !algebra.field_vector<"bls12-381.fr">, %arg103: !algebra.field_vector<"bls12-381.fr">, %arg104: !algebra.field<"bls12-381.fr">, %arg105: !protocol.service_ref<"random.bls12-381.fr/0">):
        %182:2 = "protocol.local_call"(%arg99, %arg100, %arg101) <{callee = @zkl_532a609cf36a935835501ca51308940142121e647ca360843a880bf231f04aa6, role = "role00000000", site = "s19"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %183 = "protocol.exchange"(%182#0) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %184 = "protocol.restrict_roles"(%183) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %185 = "protocol.exchange"(%182#1) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_1"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %186 = "protocol.restrict_roles"(%185) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %187 = "algebra.field_add"(%184, %186) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %188 = "algebra.field_equal"(%arg104, %187) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
        "protocol.guard"(%188) <{owner = "role00000001", site = "s27"}> : (i1) -> ()
        %189 = "protocol.query"(%arg105) <{method = "draw", owner = "role00000001", site = "label_6368616c6c656e6765"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
        %190 = "protocol.exchange"(%189) <{receiver = "role00000000", sender = "role00000001", site = "label_64656c6976657279_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %191 = "protocol.restrict_roles"(%190) <{roles = ["role00000000"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %192:3 = "protocol.local_call"(%arg99, %arg100, %arg101, %191) <{callee = @zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d, role = "role00000000", site = "s32"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
        %193 = "protocol.local_call"(%arg102, %191) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000000", site = "s34"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
        %194 = "protocol.local_call"(%arg103, %189) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000001", site = "s36"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
        %195 = "algebra.constant"() <{value = "1"}> : () -> !algebra.field<"bls12-381.fr">
        %196 = "algebra.field_subtract"(%195, %189) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %197 = "algebra.field_multiply"(%196, %184) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %198 = "algebra.field_multiply"(%189, %186) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %199 = "algebra.field_add"(%197, %198) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        "protocol.yield"(%192#0, %192#1, %192#2, %193, %194, %199) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
      }) : (ui64, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %181:2 = "protocol.local_call"(%180#4, %180#5) <{callee = @zkl_c36a2d2c6bd38573735fb9b90d1a3848c562d2c1f688234e2b669408e9c9eea9, role = "role00000001", site = "s48"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      "protocol.return"(%180#3, %180#0, %180#1, %180#2, %181#0, %181#1) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1, sym_name = "zkf_326ab2331715c62ba21cb6a967c927ba6ad7f7f2da5e84eb0e5de0fc610f26ca", sym_visibility = "private"}> ({
    ^bb0(%arg88: !algebra.field_vector<"bls12-381.fr">, %arg89: ui64, %arg90: ui64):
      %163 = "func.call"(%arg88, %arg89, %arg90) <{callee = @zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %164 = "data.index"() <{value = "1"}> : () -> ui64
      %165 = "data.index_equal"(%163, %164) : (ui64, ui64) -> i1
      %166 = "func.call"(%arg88, %arg89, %arg90) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">
      %167 = "data.dim"(%166) <{axis = 0 : i64}> : (!algebra.field_vector<"bls12-381.fr">) -> ui64
      %168 = "func.call"(%arg88, %arg89, %arg90) <{callee = @zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %169 = "data.index_power_of_two"(%167, %168) : (ui64, ui64) -> i1
      %170 = "arith.andi"(%165, %169) : (i1, i1) -> i1
      "func.return"(%170) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64, sym_name = "zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275", sym_visibility = "private"}> ({
    ^bb0(%arg85: !algebra.field_vector<"bls12-381.fr">, %arg86: ui64, %arg87: ui64):
      "func.return"(%arg87) : (ui64) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">, sym_name = "zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", sym_visibility = "private"}> ({
    ^bb0(%arg82: !algebra.field_vector<"bls12-381.fr">, %arg83: ui64, %arg84: ui64):
      "func.return"(%arg82) : (!algebra.field_vector<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64, sym_name = "zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94", sym_visibility = "private"}> ({
    ^bb0(%arg79: !algebra.field_vector<"bls12-381.fr">, %arg80: ui64, %arg81: ui64):
      "func.return"(%arg80) : (ui64) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "zkf_c51d11bf318ad26bc2fce7b89eec63f85b98f57e91e0e9e6256f84a573b5b6e6", sym_visibility = "private"}> ({
    ^bb0(%arg74: !algebra.field_vector<"bls12-381.fr">, %arg75: ui64, %arg76: ui64, %arg77: !algebra.field_vector<"bls12-381.fr">, %arg78: !algebra.field<"bls12-381.fr">):
      %159 = "func.call"(%arg74, %arg75, %arg76) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">
      %160 = "algebra.multilinear_restrict_prefix"(%159, %arg77) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
      %161 = "func.call"(%160) <{callee = @zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e}> : (!algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %162 = "algebra.field_equal"(%arg78, %161) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "func.return"(%162) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", sym_visibility = "private"}> ({
    ^bb0(%arg73: !runtime.scope):
      %154 = "exec.apply"(%arg73) <{binding = @zkl_binding_7, parameters = [], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%154)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%155: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %156 = "exec.returned"(%155) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%156) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%157: !exec.stop):  // pred: ^bb0
      %158 = "exec.failed"(%157) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%158) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6310h7072696d6974697665736h766563746f725h656d707479", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_e8df957aab384c1d5416600c13a571512206e97abfbf6e0e9cddac5c84860d07", sym_visibility = "private"}> ({
    ^bb0(%arg70: !runtime.scope, %arg71: !algebra.field_vector<"bls12-381.fr">, %arg72: !algebra.field<"bls12-381.fr">):
      %153 = "exec.returned"(%arg71, %arg72) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%153) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s8h73756d636865636b10h6f70656e5f636c61696d", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_532a609cf36a935835501ca51308940142121e647ca360843a880bf231f04aa6", sym_visibility = "private"}> ({
    ^bb0(%arg66: !runtime.scope, %arg67: !algebra.field_vector<"bls12-381.fr">, %arg68: ui64, %arg69: ui64):
      %143 = "func.call"(%arg66, %arg67, %arg68, %arg69) <{callee = @zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087}> {runtime.site = "s0"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%143)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%144: !algebra.field_vector<"bls12-381.fr">, %145: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %146 = "exec.apply"(%arg66, %144) <{binding = @zkl_binding_8, parameters = [], site = "s3"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%146)[^bb3, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%147: !exec.stop):  // 3 preds: ^bb0, ^bb1, ^bb3
      %148 = "exec.failed"(%147) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%148) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb3(%149: !algebra.field<"bls12-381.fr">):  // pred: ^bb1
      %150 = "exec.apply"(%arg66, %145) <{binding = @zkl_binding_8, parameters = [], site = "s5"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%150)[^bb4, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb4(%151: !algebra.field<"bls12-381.fr">):  // pred: ^bb3
      %152 = "exec.returned"(%149, %151) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%152) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s8h73756d636865636b4h73756d73", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087", sym_visibility = "private"}> ({
    ^bb0(%arg62: !runtime.scope, %arg63: !algebra.field_vector<"bls12-381.fr">, %arg64: ui64, %arg65: ui64):
      %119 = "exec.apply"(%arg62) <{binding = @zkl_binding_0, parameters = ["0"], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%119)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%120: ui64):  // pred: ^bb0
      %121 = "func.call"(%arg62, %120, %arg64) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s2"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%121)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%122: !exec.stop):  // 10 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12
      %123 = "exec.failed"(%122) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%123) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%124: i1):  // pred: ^bb1
      %125 = "exec.test"(%arg62, %124) <{site = "s3"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%125)[^bb4, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb4(%126: i1):  // pred: ^bb3
      "cf.cond_br"(%126)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %127 = "runtime.enter_scope"(%arg62) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s3"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%127)[^bb8, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %128 = "runtime.enter_scope"(%arg62) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s3"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%128)[^bb11, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // 2 preds: ^bb10, ^bb13
      %129 = "exec.apply"(%arg62, %arg63) <{binding = @zkl_binding_9, parameters = [], site = "s5"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%129)[^bb14, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%130: !runtime.scope):  // pred: ^bb5
      %131 = "func.call"(%130) <{callee = @zkl_control_11}> : (!runtime.scope) -> !exec.outcome<>
      %132 = "runtime.exit_scope"(%130, %131) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%132)[^bb9, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb9(%133: !runtime.transfer<>):  // pred: ^bb8
      %134 = "runtime.accept_transfer"(%arg62, %133) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%134)[^bb10, ^bb2] : (!exec.outcome<>) -> ()
    ^bb10:  // pred: ^bb9
      "cf.br"()[^bb7] : () -> ()
    ^bb11(%135: !runtime.scope):  // pred: ^bb6
      %136 = "func.call"(%135) <{callee = @zkl_control_12}> : (!runtime.scope) -> !exec.outcome<>
      %137 = "runtime.exit_scope"(%135, %136) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%137)[^bb12, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb12(%138: !runtime.transfer<>):  // pred: ^bb11
      %139 = "runtime.accept_transfer"(%arg62, %138) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%139)[^bb13, ^bb2] : (!exec.outcome<>) -> ()
    ^bb13:  // pred: ^bb12
      "cf.br"()[^bb7] : () -> ()
    ^bb14(%140: !algebra.field_vector<"bls12-381.fr">, %141: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb7
      %142 = "exec.returned"(%140, %141) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%142) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561726h68616c766573", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_11", sym_visibility = "private"}> ({
    ^bb0(%arg61: !runtime.scope):
      %118 = "exec.complete"(%arg61) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%118) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_12", sym_visibility = "private"}> ({
    ^bb0(%arg60: !runtime.scope):
      %115 = "exec.reject"(%arg60) <{reason = "reject", site = "s3_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%115)[^bb1] : (!exec.stop) -> ()
    ^bb1(%116: !exec.stop):  // pred: ^bb0
      %117 = "exec.failed"(%116) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%117) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d", sym_visibility = "private"}> ({
    ^bb0(%arg55: !runtime.scope, %arg56: !algebra.field_vector<"bls12-381.fr">, %arg57: ui64, %arg58: ui64, %arg59: !algebra.field<"bls12-381.fr">):
      %103 = "func.call"(%arg55, %arg56, %arg57, %arg58) <{callee = @zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087}> {runtime.site = "s0"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%103)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%104: !algebra.field_vector<"bls12-381.fr">, %105: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %106 = "exec.collect"(%arg55, %104, %105, %arg59) <{body = @zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body, domain = @zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_domain, site = "s4"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%106)[^bb3, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%107: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %108 = "exec.failed"(%107) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%108) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb3(%109: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb1
      %110 = "exec.apply"(%arg55) <{binding = @zkl_binding_0, parameters = ["1"], site = "s7"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%110)[^bb4, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%111: ui64):  // pred: ^bb3
      %112 = "exec.apply"(%arg55, %arg57, %111) <{binding = @zkl_binding_10, parameters = [], site = "s8"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%112)[^bb5, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%113: ui64):  // pred: ^bb4
      %114 = "exec.returned"(%109, %113, %arg58) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%114) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561729h6669785f6669727374", []]} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, sym_name = "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_domain", sym_visibility = "private"}> ({
    ^bb0(%arg53: !algebra.field_vector<"bls12-381.fr">, %arg54: !algebra.field_vector<"bls12-381.fr">):
      %100 = "data.domain_elements"(%arg53) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %101 = "data.domain_elements"(%arg54) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %102 = "data.domain_zip"(%100, %101) : (!data.domain<!algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%102) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body", sym_visibility = "private"}> ({
    ^bb0(%arg47: !runtime.scope, %arg48: !algebra.field<"bls12-381.fr">, %arg49: !algebra.field<"bls12-381.fr">, %arg50: !algebra.field_vector<"bls12-381.fr">, %arg51: !algebra.field_vector<"bls12-381.fr">, %arg52: !algebra.field<"bls12-381.fr">):
      %95 = "exec.compute"(%arg47, %arg48, %arg49, %arg52) <{callee = @zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5, site = "body"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%95)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%96: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %97 = "exec.returned"(%96) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%97) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%98: !exec.stop):  // pred: ^bb0
      %99 = "exec.failed"(%98) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%99) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5", sym_visibility = "private"}> ({
    ^bb0(%arg44: !algebra.field<"bls12-381.fr">, %arg45: !algebra.field<"bls12-381.fr">, %arg46: !algebra.field<"bls12-381.fr">):
      %92 = "algebra.field_subtract"(%arg45, %arg44) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %93 = "algebra.field_multiply"(%92, %arg46) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %94 = "algebra.field_add"(%arg44, %93) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%94) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", sym_visibility = "private"}> ({
    ^bb0(%arg41: !runtime.scope, %arg42: !algebra.field_vector<"bls12-381.fr">, %arg43: !algebra.field<"bls12-381.fr">):
      %87 = "exec.apply"(%arg41, %arg42, %arg43) <{binding = @zkl_binding_11, parameters = [], site = "s0"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%87)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%88: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %89 = "exec.returned"(%88) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%89) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%90: !exec.stop):  // pred: ^bb0
      %91 = "exec.failed"(%90) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%91) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6310h7072696d6974697665736h766563746f726h617070656e64", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_c36a2d2c6bd38573735fb9b90d1a3848c562d2c1f688234e2b669408e9c9eea9", sym_visibility = "private"}> ({
    ^bb0(%arg38: !runtime.scope, %arg39: !algebra.field_vector<"bls12-381.fr">, %arg40: !algebra.field<"bls12-381.fr">):
      %86 = "exec.returned"(%arg39, %arg40) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%86) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s8h73756d636865636b9h61745f707265666978", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc", sym_visibility = "private"}> ({
    ^bb0(%arg34: !runtime.scope, %arg35: !algebra.field_vector<"bls12-381.fr">, %arg36: !algebra.field_vector<"bls12-381.fr">, %arg37: !algebra.field<"bls12-381.fr">):
      %60 = "exec.apply"(%arg34, %arg36) <{binding = @zkl_binding_1, parameters = [], site = "s3"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%60)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%61: ui64):  // pred: ^bb0
      %62 = "exec.apply"(%arg34) <{binding = @zkl_binding_0, parameters = ["1"], site = "s4"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%62)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%63: !exec.stop):  // 10 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb6, ^bb7, ^bb9, ^bb10, ^bb12, ^bb13
      %64 = "exec.failed"(%63) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%64) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%65: ui64):  // pred: ^bb1
      %66 = "func.call"(%arg34, %arg35, %61, %65) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655}> {runtime.site = "s5"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%66)[^bb4, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb4(%67: i1):  // pred: ^bb3
      %68 = "exec.test"(%arg34, %67) <{site = "s9"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%68)[^bb5, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb5(%69: i1):  // pred: ^bb4
      "cf.cond_br"(%69)[^bb6, ^bb7] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb6:  // pred: ^bb5
      %70 = "runtime.enter_scope"(%arg34, %arg35, %arg36, %arg37) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "then", site = "s9"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%70)[^bb9, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // pred: ^bb5
      %71 = "runtime.enter_scope"(%arg34, %arg35, %arg36, %arg37) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "else", site = "s9"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
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
      %55 = "func.call"(%arg30, %arg31, %arg32, %arg33) <{callee = @zkl_967e003dd39c9e1730d1e9e543081e08e351228ff07f85fb14e1e88dbded8a99}> {runtime.site = "s12"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>
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
      %50 = "exec.boolean"(%arg26) <{site = "s14", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%50)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%51: i1):  // pred: ^bb0
      %52 = "exec.complete"(%arg26, %51) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%52) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%53: !exec.stop):  // pred: ^bb0
      %54 = "exec.failed"(%53) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%54) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_967e003dd39c9e1730d1e9e543081e08e351228ff07f85fb14e1e88dbded8a99", sym_visibility = "private"}> ({
    ^bb0(%arg22: !runtime.scope, %arg23: !algebra.field_vector<"bls12-381.fr">, %arg24: !algebra.field_vector<"bls12-381.fr">, %arg25: !algebra.field<"bls12-381.fr">):
      %29 = "exec.apply"(%arg22, %arg24) <{binding = @zkl_binding_1, parameters = [], site = "s0"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%29)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%30: ui64):  // pred: ^bb0
      %31 = "exec.apply"(%arg22) <{binding = @zkl_binding_0, parameters = ["1"], site = "s1"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%31)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%32: !exec.stop):  // 7 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7
      %33 = "exec.failed"(%32) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%33) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%34: ui64):  // pred: ^bb1
      %35 = "func.call"(%arg22, %arg23, %30, %34) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a}> {runtime.site = "s2"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%35)[^bb4, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb4(%36: !algebra.field_vector<"bls12-381.fr">, %37: ui64, %38: ui64):  // pred: ^bb3
      %39 = "func.call"(%arg22, %36, %37, %38, %arg24) <{callee = @zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be}> {runtime.site = "s4"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%39)[^bb5, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb5(%40: !algebra.field_vector<"bls12-381.fr">, %41: ui64, %42: ui64):  // pred: ^bb4
      %43 = "exec.compute"(%arg22, %40, %41, %42) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33, site = "s6"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%43)[^bb6, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb6(%44: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb5
      %45 = "exec.apply"(%arg22, %44) <{binding = @zkl_binding_8, parameters = [], site = "s7"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%45)[^bb7, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb7(%46: !algebra.field<"bls12-381.fr">):  // pred: ^bb6
      %47 = "exec.apply"(%arg22, %46, %arg25) <{binding = @zkl_binding_12, parameters = [], site = "s8"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>
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
    "relation.declare"() <{formula = @zkf_9ca6c98faa0d00ed80eb608a89db1544ad71443a8944af6ac99e6fd78cb3660b, key = "zkl_733a9984be750c90a7e40f8fc81c10a284cb9ecaf745c62024f07f1a3806a10c", kind = "zkc.language.formula/0", purposes = ["parameter", "parameter"], revision = "fef4042b36eb69492320800630ec190760414ad82c4859a47d2aac19bf270e5c", signature = (!algebra.field_vector<"bls12-381.fr">, ui64) -> i1, static_arguments = [], sym_name = "zkl_733a9984be750c90a7e40f8fc81c10a284cb9ecaf745c62024f07f1a3806a10c"}> : () -> ()
    "relation.declare"() <{formula = @zkf_116f3285742dd1275b8149c69b78a6713cd6256a8af715be7c346da1c793a766, key = "zkl_1c2e12f894c2f4b39d38adc87f1dedbaf7856eb6985dba89eb2261c88030aef2", kind = "zkc.language.formula/0", purposes = ["parameter", "statement"], revision = "a60d910bb6e61b3f4d146e863f02155af13cfbdf8ddd5538ee0d89004c93bd71", signature = (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, static_arguments = [], sym_name = "zkl_1c2e12f894c2f4b39d38adc87f1dedbaf7856eb6985dba89eb2261c88030aef2"}> : () -> ()
    "relation.declare"() <{formula = @zkf_326ab2331715c62ba21cb6a967c927ba6ad7f7f2da5e84eb0e5de0fc610f26ca, key = "zkl_8c866415d5a42d7cb60d6b39dd52568c20001248a901906f13a3d5d9dd8f74ac", kind = "zkc.language.formula/0", purposes = ["parameter", "parameter", "parameter"], revision = "68f32f59f6f51bf609caa3011d403333e122834ebc8b40f75aa8b71e05b226f9", signature = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1, static_arguments = [], sym_name = "zkl_8c866415d5a42d7cb60d6b39dd52568c20001248a901906f13a3d5d9dd8f74ac"}> : () -> ()
    "relation.declare"() <{formula = @zkf_c51d11bf318ad26bc2fce7b89eec63f85b98f57e91e0e9e6256f84a573b5b6e6, key = "zkl_f03c5af270c09f9d5e832cdb0dc1d71151cebecfaaa08c6cacd997dde03860e9", kind = "zkc.language.formula/0", purposes = ["parameter", "parameter", "parameter", "statement", "statement"], revision = "d03f98f010ae1cb9e5b251d8a51e9642396e316bec6646da5d20d334ec8ee874", signature = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, static_arguments = [], sym_name = "zkl_f03c5af270c09f9d5e832cdb0dc1d71151cebecfaaa08c6cacd997dde03860e9"}> : () -> ()
  }) {source_declarations = "[[[[\22nominal\22,\22record\22,\22zkc::multilinear::Table\22,[[\22field\22,\22bls12-381.fr\22]]],\22ordinary\22,false,[[\22entries\22,[\22builtin\22,\22vector\22,[[\22field\22,\22bls12-381.fr\22]]]],[\22dimensions\22,[\22index\22]],[\22columns\22,[\22index\22]]]],[[\22nominal\22,\22record\22,\22sumcheck::Pending\22,[[\22field\22,\22bls12-381.fr\22]]],\22linear\22,true,[[\22point\22,[\22builtin\22,\22vector\22,[[\22field\22,\22bls12-381.fr\22]]]],[\22value\22,[\22field\22,\22bls12-381.fr\22]]]]],[[\22zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071\22,[[\22values\22,[\22builtin\22,\22vector\22,[[\22field\22,\22bls12-381.fr\22]]],[\22role00000000\22,\22role00000001\22],0,1],[\22claim\22,[\22field\22,\22bls12-381.fr\22],[\22role00000001\22],1,1],[\22rounds\22,[\22index\22],[\22role00000000\22,\22role00000001\22],2,1]],[[\22accepted\22,[\22bool\22],[\22role00000001\22],0,1]]],[\22zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5\22,[[\22values\22,[\22nominal\22,\22record\22,\22zkc::multilinear::Table\22,[[\22field\22,\22bls12-381.fr\22]]],[\22role00000000\22],0,3],[\22claim\22,[\22nominal\22,\22record\22,\22sumcheck::Pending\22,[[\22field\22,\22bls12-381.fr\22]]],[\22role00000001\22],3,2],[\22rounds\22,[\22index\22],[\22role00000000\22,\22role00000001\22],5,1]],[[\22point\22,[\22builtin\22,\22vector\22,[[\22field\22,\22bls12-381.fr\22]]],[\22role00000000\22],0,1],[\22residual\22,[\22nominal\22,\22record\22,\22zkc::multilinear::Table\22,[[\22field\22,\22bls12-381.fr\22]]],[\22role00000000\22],1,3],[\22evaluation\22,[\22nominal\22,\22record\22,\22sumcheck::Pending\22,[[\22field\22,\22bls12-381.fr\22]]],[\22role00000001\22],4,2]]]]]"} : () -> ()
}) : () -> ()

