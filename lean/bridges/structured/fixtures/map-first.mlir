"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.split", function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>, implementation = "", sym_name = "zkl_binding_8"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.sub", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_7"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.mul", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_6"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.less", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>, implementation = "", sym_name = "zkl_binding_5"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.div", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_4"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.equal", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>, implementation = "", sym_name = "zkl_binding_3"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.mod", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_2"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.length", function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_1"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.constant", function_type = (!runtime.scope) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_0"}> : () -> ()
    "protocol.func"() <{contracts = [], function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), input_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"]], origin = ["map_examples::First", []], output_roles = [["role00000000"], ["role00000000"], ["role00000000"]], roles = ["role00000000"], sym_name = "s12h6d61705f6578616d706c65735h4669727374"}> ({
    ^bb0(%arg74: !algebra.field_vector<"bls12-381.fr">, %arg75: ui64, %arg76: ui64, %arg77: !algebra.field<"bls12-381.fr">):
      %256:3 = "protocol.local_call"(%arg74, %arg75, %arg76, %arg77) <{callee = @s12h6d61705f6578616d706c65735h6669727374, role = "role00000000", site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      "protocol.return"(%256#0, %256#1, %256#2) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "s12h6d61705f6578616d706c65735h6669727374", sym_visibility = "private"}> ({
    ^bb0(%arg69: !runtime.scope, %arg70: !algebra.field_vector<"bls12-381.fr">, %arg71: ui64, %arg72: ui64, %arg73: !algebra.field<"bls12-381.fr">):
      %239 = "func.call"(%arg69, %arg70, %arg71, %arg72) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a}> {runtime.site = "s0"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%239)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb1(%240: !algebra.field_vector<"bls12-381.fr">, %241: ui64, %242: ui64):  // pred: ^bb0
      %243 = "func.call"(%arg69, %240, %241, %242, %arg73) <{callee = @zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d}> {runtime.site = "s1"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "exec.dispatch"(%243)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb2(%244: !exec.stop):  // 5 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5
      %245 = "exec.failed"(%244) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%245) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb3(%246: !algebra.field_vector<"bls12-381.fr">, %247: ui64, %248: ui64):  // pred: ^bb1
      %249 = "exec.compute"(%arg69, %246, %247, %248) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33, site = "s3"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%249)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb4(%250: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb3
      %251 = "exec.compute"(%arg69, %246, %247, %248) <{callee = @zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94, site = "s4"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%251)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%252: ui64):  // pred: ^bb4
      %253 = "exec.compute"(%arg69, %246, %247, %248) <{callee = @zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275, site = "s5"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%253)[^bb6, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb6(%254: ui64):  // pred: ^bb5
      %255 = "exec.returned"(%250, %252, %254) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%255) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["s12h6d61705f6578616d706c65735h6669727374", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", sym_visibility = "private"}> ({
    ^bb0(%arg65: !runtime.scope, %arg66: !algebra.field_vector<"bls12-381.fr">, %arg67: ui64, %arg68: ui64):
      %220 = "func.call"(%arg65, %arg66, %arg67, %arg68) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655}> {runtime.site = "s0"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%220)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%221: i1):  // pred: ^bb0
      %222 = "exec.test"(%arg65, %221) <{site = "s1"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%222)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%223: !exec.stop):  // 8 preds: ^bb0, ^bb1, ^bb4, ^bb5, ^bb7, ^bb8, ^bb10, ^bb11
      %224 = "exec.failed"(%223) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%224) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb3(%225: i1):  // pred: ^bb1
      "cf.cond_br"(%225)[^bb4, ^bb5] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb4:  // pred: ^bb3
      %226 = "runtime.enter_scope"(%arg65) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%226)[^bb7, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb5:  // pred: ^bb3
      %227 = "runtime.enter_scope"(%arg65) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%227)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // 2 preds: ^bb9, ^bb12
      %228 = "exec.returned"(%arg66, %arg67, %arg68) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%228) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb7(%229: !runtime.scope):  // pred: ^bb4
      %230 = "func.call"(%229) <{callee = @zkl_control_0}> : (!runtime.scope) -> !exec.outcome<>
      %231 = "runtime.exit_scope"(%229, %230) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%231)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb8(%232: !runtime.transfer<>):  // pred: ^bb7
      %233 = "runtime.accept_transfer"(%arg65, %232) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%233)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb9:  // pred: ^bb8
      "cf.br"()[^bb6] : () -> ()
    ^bb10(%234: !runtime.scope):  // pred: ^bb5
      %235 = "func.call"(%234) <{callee = @zkl_control_1}> : (!runtime.scope) -> !exec.outcome<>
      %236 = "runtime.exit_scope"(%234, %235) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%236)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb11(%237: !runtime.transfer<>):  // pred: ^bb10
      %238 = "runtime.accept_transfer"(%arg65, %237) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%238)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb12:  // pred: ^bb11
      "cf.br"()[^bb6] : () -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561725h7461626c65", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_0", sym_visibility = "private"}> ({
    ^bb0(%arg64: !runtime.scope):
      %219 = "exec.complete"(%arg64) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%219) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_1", sym_visibility = "private"}> ({
    ^bb0(%arg63: !runtime.scope):
      %216 = "exec.reject"(%arg63) <{reason = "reject", site = "s1_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%216)[^bb1] : (!exec.stop) -> ()
    ^bb1(%217: !exec.stop):  // pred: ^bb0
      %218 = "exec.failed"(%217) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%218) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", sym_visibility = "private"}> ({
    ^bb0(%arg59: !runtime.scope, %arg60: !algebra.field_vector<"bls12-381.fr">, %arg61: ui64, %arg62: ui64):
      %158 = "exec.apply"(%arg59) <{binding = @zkl_binding_0, parameters = [0 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%158)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%159: ui64):  // pred: ^bb0
      %160 = "func.call"(%arg59, %159, %arg62) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s1"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%160)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%161: !exec.stop):  // 23 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12, ^bb15, ^bb16, ^bb17, ^bb18, ^bb19, ^bb21, ^bb22, ^bb25, ^bb26, ^bb28, ^bb29, ^bb31, ^bb32
      %162 = "exec.failed"(%161) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%162) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%163: i1):  // pred: ^bb1
      %164 = "exec.test"(%arg59, %163) <{site = "s3"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%164)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb4(%165: i1):  // pred: ^bb3
      "cf.cond_br"(%165)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %166 = "runtime.enter_scope"(%arg59, %arg61) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "then", site = "s3"}> : (!runtime.scope, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%166)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %167 = "runtime.enter_scope"(%arg59, %arg61) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "else", site = "s3"}> : (!runtime.scope, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%167)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7(%168: i1):  // 2 preds: ^bb10, ^bb13
      %169 = "exec.test"(%arg59, %168) <{site = "s11"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%169)[^bb14, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb8(%170: !runtime.scope):  // pred: ^bb5
      %171 = "func.call"(%170, %arg61) <{callee = @zkl_control_2}> : (!runtime.scope, ui64) -> !exec.outcome<(i1)>
      %172 = "runtime.exit_scope"(%170, %171) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%172)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb9(%173: !runtime.transfer<(i1)>):  // pred: ^bb8
      %174 = "runtime.accept_transfer"(%arg59, %173) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%174)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb10(%175: i1):  // pred: ^bb9
      "cf.br"(%175)[^bb7] : (i1) -> ()
    ^bb11(%176: !runtime.scope):  // pred: ^bb6
      %177 = "func.call"(%176, %arg61) <{callee = @zkl_control_3}> : (!runtime.scope, ui64) -> !exec.outcome<(i1)>
      %178 = "runtime.exit_scope"(%176, %177) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%178)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb12(%179: !runtime.transfer<(i1)>):  // pred: ^bb11
      %180 = "runtime.accept_transfer"(%arg59, %179) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%180)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb13(%181: i1):  // pred: ^bb12
      "cf.br"(%181)[^bb7] : (i1) -> ()
    ^bb14(%182: i1):  // pred: ^bb7
      "cf.cond_br"(%182)[^bb15, ^bb16] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb15:  // pred: ^bb14
      %183 = "runtime.enter_scope"(%arg59, %arg60, %arg62) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "then", site = "s11"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%183)[^bb18, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb16:  // pred: ^bb14
      %184 = "runtime.enter_scope"(%arg59, %arg60, %arg62) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "else", site = "s11"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%184)[^bb21, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb17(%185: i1):  // 2 preds: ^bb20, ^bb23
      %186 = "exec.test"(%arg59, %185) <{site = "s22"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%186)[^bb24, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb18(%187: !runtime.scope):  // pred: ^bb15
      %188 = "func.call"(%187, %arg60, %arg62) <{callee = @zkl_control_4}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>
      %189 = "runtime.exit_scope"(%187, %188) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%189)[^bb19, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb19(%190: !runtime.transfer<(i1)>):  // pred: ^bb18
      %191 = "runtime.accept_transfer"(%arg59, %190) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%191)[^bb20, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb20(%192: i1):  // pred: ^bb19
      "cf.br"(%192)[^bb17] : (i1) -> ()
    ^bb21(%193: !runtime.scope):  // pred: ^bb16
      %194 = "func.call"(%193, %arg60, %arg62) <{callee = @zkl_control_5}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>
      %195 = "runtime.exit_scope"(%193, %194) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%195)[^bb22, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb22(%196: !runtime.transfer<(i1)>):  // pred: ^bb21
      %197 = "runtime.accept_transfer"(%arg59, %196) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%197)[^bb23, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb23(%198: i1):  // pred: ^bb22
      "cf.br"(%198)[^bb17] : (i1) -> ()
    ^bb24(%199: i1):  // pred: ^bb17
      "cf.cond_br"(%199)[^bb25, ^bb26] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb25:  // pred: ^bb24
      %200 = "runtime.enter_scope"(%arg59, %arg60, %arg61, %arg62) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "then", site = "s22"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%200)[^bb28, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb26:  // pred: ^bb24
      %201 = "runtime.enter_scope"(%arg59, %arg60, %arg61, %arg62) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "else", site = "s22"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%201)[^bb31, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb27(%202: i1):  // 2 preds: ^bb30, ^bb33
      %203 = "exec.returned"(%202) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%203) : (!exec.outcome<(i1)>) -> ()
    ^bb28(%204: !runtime.scope):  // pred: ^bb25
      %205 = "func.call"(%204, %arg60, %arg61, %arg62) <{callee = @zkl_control_6}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      %206 = "runtime.exit_scope"(%204, %205) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%206)[^bb29, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb29(%207: !runtime.transfer<(i1)>):  // pred: ^bb28
      %208 = "runtime.accept_transfer"(%arg59, %207) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%208)[^bb30, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb30(%209: i1):  // pred: ^bb29
      "cf.br"(%209)[^bb27] : (i1) -> ()
    ^bb31(%210: !runtime.scope):  // pred: ^bb26
      %211 = "func.call"(%210, %arg60, %arg61, %arg62) <{callee = @zkl_control_7}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      %212 = "runtime.exit_scope"(%210, %211) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%212)[^bb32, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb32(%213: !runtime.transfer<(i1)>):  // pred: ^bb31
      %214 = "runtime.accept_transfer"(%arg59, %213) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%214)[^bb33, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb33(%215: i1):  // pred: ^bb32
      "cf.br"(%215)[^bb27] : (i1) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_2", sym_visibility = "private"}> ({
    ^bb0(%arg57: !runtime.scope, %arg58: ui64):
      %151 = "exec.apply"(%arg57) <{binding = @zkl_binding_0, parameters = [64 : ui64], site = "s4"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%151)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%152: ui64):  // pred: ^bb0
      %153 = "func.call"(%arg57, %arg58, %152) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s5"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%153)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%154: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %155 = "exec.failed"(%154) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%155) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%156: i1):  // pred: ^bb1
      %157 = "exec.complete"(%arg57, %156) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%157) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_3", sym_visibility = "private"}> ({
    ^bb0(%arg55: !runtime.scope, %arg56: ui64):
      %146 = "exec.boolean"(%arg55) <{site = "s7", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%146)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%147: i1):  // pred: ^bb0
      %148 = "exec.complete"(%arg55, %147) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%148) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%149: !exec.stop):  // pred: ^bb0
      %150 = "exec.failed"(%149) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%150) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_4", sym_visibility = "private"}> ({
    ^bb0(%arg52: !runtime.scope, %arg53: !algebra.field_vector<"bls12-381.fr">, %arg54: ui64):
      %135 = "exec.apply"(%arg52, %arg53) <{binding = @zkl_binding_1, parameters = [], site = "s12"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%135)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%136: ui64):  // pred: ^bb0
      %137 = "exec.apply"(%arg52, %136, %arg54) <{binding = @zkl_binding_2, parameters = [], site = "s13"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%137)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%138: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %139 = "exec.failed"(%138) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%139) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%140: ui64):  // pred: ^bb1
      %141 = "exec.apply"(%arg52) <{binding = @zkl_binding_0, parameters = [0 : ui64], site = "s14"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%141)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%142: ui64):  // pred: ^bb3
      %143 = "exec.apply"(%arg52, %140, %142) <{binding = @zkl_binding_3, parameters = [], site = "s15"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%143)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb5(%144: i1):  // pred: ^bb4
      %145 = "exec.complete"(%arg52, %144) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%145) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_5", sym_visibility = "private"}> ({
    ^bb0(%arg49: !runtime.scope, %arg50: !algebra.field_vector<"bls12-381.fr">, %arg51: ui64):
      %130 = "exec.boolean"(%arg49) <{site = "s17", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%130)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%131: i1):  // pred: ^bb0
      %132 = "exec.complete"(%arg49, %131) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%132) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%133: !exec.stop):  // pred: ^bb0
      %134 = "exec.failed"(%133) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%134) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_6", sym_visibility = "private"}> ({
    ^bb0(%arg45: !runtime.scope, %arg46: !algebra.field_vector<"bls12-381.fr">, %arg47: ui64, %arg48: ui64):
      %119 = "exec.apply"(%arg45, %arg46) <{binding = @zkl_binding_1, parameters = [], site = "s23"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%119)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%120: ui64):  // pred: ^bb0
      %121 = "exec.apply"(%arg45, %120, %arg48) <{binding = @zkl_binding_4, parameters = [], site = "s24"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%121)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%122: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %123 = "exec.failed"(%122) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%123) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%124: ui64):  // pred: ^bb1
      %125 = "func.call"(%arg45, %arg47) <{callee = @s3h7a6b6311h6d756c74696c696e6561724h726f7773}> {runtime.site = "s25"} : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%125)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%126: ui64):  // pred: ^bb3
      %127 = "exec.apply"(%arg45, %124, %126) <{binding = @zkl_binding_3, parameters = [], site = "s26"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%127)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb5(%128: i1):  // pred: ^bb4
      %129 = "exec.complete"(%arg45, %128) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%129) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_7", sym_visibility = "private"}> ({
    ^bb0(%arg41: !runtime.scope, %arg42: !algebra.field_vector<"bls12-381.fr">, %arg43: ui64, %arg44: ui64):
      %114 = "exec.boolean"(%arg41) <{site = "s28", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%114)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%115: i1):  // pred: ^bb0
      %116 = "exec.complete"(%arg41, %115) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%116) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%117: !exec.stop):  // pred: ^bb0
      %118 = "exec.failed"(%117) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%118) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "s3h7a6b637h696e64696365734h6c657373", sym_visibility = "private"}> ({
    ^bb0(%arg38: !runtime.scope, %arg39: ui64, %arg40: ui64):
      %109 = "exec.apply"(%arg38, %arg39, %arg40) <{binding = @zkl_binding_5, parameters = [], site = "s0"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%109)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%110: i1):  // pred: ^bb0
      %111 = "exec.returned"(%110) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%111) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%112: !exec.stop):  // pred: ^bb0
      %113 = "exec.failed"(%112) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%113) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.origin = ["s3h7a6b637h696e64696365734h6c657373", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "s3h7a6b6311h6d756c74696c696e6561724h726f7773", sym_visibility = "private"}> ({
    ^bb0(%arg36: !runtime.scope, %arg37: ui64):
      %62 = "exec.apply"(%arg36) <{binding = @zkl_binding_0, parameters = [64 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%62)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%63: ui64):  // pred: ^bb0
      %64 = "func.call"(%arg36, %arg37, %63) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s1"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%64)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%65: !exec.stop):  // 14 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12, ^bb14, ^bb15, ^bb19, ^bb21
      %66 = "exec.failed"(%65) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%66) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%67: i1):  // pred: ^bb1
      %68 = "exec.test"(%arg36, %67) <{site = "s2"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%68)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb4(%69: i1):  // pred: ^bb3
      "cf.cond_br"(%69)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %70 = "runtime.enter_scope"(%arg36) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s2"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%70)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %71 = "runtime.enter_scope"(%arg36) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s2"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%71)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // 2 preds: ^bb10, ^bb13
      %72 = "exec.apply"(%arg36) <{binding = @zkl_binding_0, parameters = [1 : ui64], site = "s3"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%72)[^bb14, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb8(%73: !runtime.scope):  // pred: ^bb5
      %74 = "func.call"(%73) <{callee = @zkl_control_8}> : (!runtime.scope) -> !exec.outcome<>
      %75 = "runtime.exit_scope"(%73, %74) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%75)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb9(%76: !runtime.transfer<>):  // pred: ^bb8
      %77 = "runtime.accept_transfer"(%arg36, %76) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%77)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb10:  // pred: ^bb9
      "cf.br"()[^bb7] : () -> ()
    ^bb11(%78: !runtime.scope):  // pred: ^bb6
      %79 = "func.call"(%78) <{callee = @zkl_control_9}> : (!runtime.scope) -> !exec.outcome<>
      %80 = "runtime.exit_scope"(%78, %79) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%80)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb12(%81: !runtime.transfer<>):  // pred: ^bb11
      %82 = "runtime.accept_transfer"(%arg36, %81) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%82)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb13:  // pred: ^bb12
      "cf.br"()[^bb7] : () -> ()
    ^bb14(%83: ui64):  // pred: ^bb7
      %84 = "exec.apply"(%arg36) <{binding = @zkl_binding_0, parameters = [0 : ui64], site = "s5"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%84)[^bb15, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb15(%85: ui64):  // pred: ^bb14
      %86 = "exec.range"(%arg36, %85, %arg37) <{site = "s6"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%86)[^bb16, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i64, i64)>) -> ()
    ^bb16(%87: i64, %88: i64):  // pred: ^bb15
      %89 = "runtime.borrow_transfer"(%arg36, %83) : (!runtime.scope, ui64) -> !runtime.transfer<(ui64)>
      "cf.br"(%87, %89)[^bb17] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb17(%90: i64, %91: !runtime.transfer<(ui64)>):  // 2 preds: ^bb16, ^bb20
      %92 = "arith.cmpi"(%90, %88) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%92, %91)[^bb18, ^bb19] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(ui64)>) -> ()
    ^bb18:  // pred: ^bb17
      %93 = "runtime.iteration"(%arg36, %90) <{site = "s6"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%93)[^bb22, ^bb21] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb19(%94: !runtime.transfer<(ui64)>):  // pred: ^bb17
      %95 = "runtime.accept_transfer"(%arg36, %94) : (!runtime.scope, !runtime.transfer<(ui64)>) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%95)[^bb25, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb20(%96: !runtime.transfer<(ui64)>):  // pred: ^bb24
      %97 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %98 = "arith.addi"(%90, %97) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%98, %96)[^bb17] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb21(%99: !exec.stop):  // 3 preds: ^bb18, ^bb22, ^bb23
      "runtime.release_transfer"(%91) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%99)[^bb2] : (!exec.stop) -> ()
    ^bb22(%100: ui64):  // pred: ^bb18
      %101 = "runtime.transfer_values"(%91) : (!runtime.transfer<(ui64)>) -> ui64
      %102 = "runtime.enter_scope"(%arg36, %90, %100, %101) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 2>, site = "s6"}> : (!runtime.scope, i64, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%102)[^bb23, ^bb21] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb23(%103: !runtime.scope):  // pred: ^bb22
      %104 = "func.call"(%103, %100, %101) <{callee = @zkl_control_10}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      %105 = "runtime.exit_scope"(%103, %104) : (!runtime.scope, !exec.outcome<(ui64)>) -> !exec.outcome<(!runtime.transfer<(ui64)>)>
      "exec.dispatch"(%105)[^bb24, ^bb21] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(ui64)>)>) -> ()
    ^bb24(%106: !runtime.transfer<(ui64)>):  // pred: ^bb23
      "runtime.release_transfer"(%91) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%106)[^bb20] : (!runtime.transfer<(ui64)>) -> ()
    ^bb25(%107: ui64):  // pred: ^bb19
      %108 = "exec.returned"(%107) : (ui64) -> !exec.outcome<(ui64)>
      "func.return"(%108) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561724h726f7773", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_8", sym_visibility = "private"}> ({
    ^bb0(%arg35: !runtime.scope):
      %61 = "exec.complete"(%arg35) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%61) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_9", sym_visibility = "private"}> ({
    ^bb0(%arg34: !runtime.scope):
      %58 = "exec.reject"(%arg34) <{reason = "reject", site = "s2_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%58)[^bb1] : (!exec.stop) -> ()
    ^bb1(%59: !exec.stop):  // pred: ^bb0
      %60 = "exec.failed"(%59) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%60) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "zkl_control_10", sym_visibility = "private"}> ({
    ^bb0(%arg31: !runtime.scope, %arg32: ui64, %arg33: ui64):
      %51 = "exec.apply"(%arg31) <{binding = @zkl_binding_0, parameters = [2 : ui64], site = "s7"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%51)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%52: ui64):  // pred: ^bb0
      %53 = "exec.apply"(%arg31, %arg33, %52) <{binding = @zkl_binding_6, parameters = [], site = "s8"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%53)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%54: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %55 = "exec.failed"(%54) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%55) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%56: ui64):  // pred: ^bb1
      %57 = "exec.complete"(%arg31, %56) : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "func.return"(%57) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d", sym_visibility = "private"}> ({
    ^bb0(%arg26: !runtime.scope, %arg27: !algebra.field_vector<"bls12-381.fr">, %arg28: ui64, %arg29: ui64, %arg30: !algebra.field<"bls12-381.fr">):
      %39 = "func.call"(%arg26, %arg27, %arg28, %arg29) <{callee = @zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087}> {runtime.site = "s0"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%39)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%40: !algebra.field_vector<"bls12-381.fr">, %41: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %42 = "exec.collect"(%arg26, %40, %41, %arg30) <{body = @zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body, domain = @zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_domain, site = "s4"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%42)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%43: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %44 = "exec.failed"(%43) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%44) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb3(%45: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb1
      %46 = "exec.apply"(%arg26) <{binding = @zkl_binding_0, parameters = [1 : ui64], site = "s7"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%46)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%47: ui64):  // pred: ^bb3
      %48 = "exec.apply"(%arg26, %arg28, %47) <{binding = @zkl_binding_7, parameters = [], site = "s8"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%48)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%49: ui64):  // pred: ^bb4
      %50 = "exec.returned"(%45, %49, %arg29) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%50) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561729h6669785f6669727374", []]} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, sym_name = "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_domain", sym_visibility = "private"}> ({
    ^bb0(%arg24: !algebra.field_vector<"bls12-381.fr">, %arg25: !algebra.field_vector<"bls12-381.fr">):
      %36 = "data.domain_elements"(%arg24) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %37 = "data.domain_elements"(%arg25) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %38 = "data.domain_zip"(%36, %37) : (!data.domain<!algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%38) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body", sym_visibility = "private"}> ({
    ^bb0(%arg18: !runtime.scope, %arg19: !algebra.field<"bls12-381.fr">, %arg20: !algebra.field<"bls12-381.fr">, %arg21: !algebra.field_vector<"bls12-381.fr">, %arg22: !algebra.field_vector<"bls12-381.fr">, %arg23: !algebra.field<"bls12-381.fr">):
      %31 = "exec.compute"(%arg18, %arg19, %arg20, %arg23) <{callee = @zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5, site = "body"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%31)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%32: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %33 = "exec.returned"(%32) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%33) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%34: !exec.stop):  // pred: ^bb0
      %35 = "exec.failed"(%34) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%35) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087", sym_visibility = "private"}> ({
    ^bb0(%arg14: !runtime.scope, %arg15: !algebra.field_vector<"bls12-381.fr">, %arg16: ui64, %arg17: ui64):
      %7 = "exec.apply"(%arg14) <{binding = @zkl_binding_0, parameters = [0 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%7)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%8: ui64):  // pred: ^bb0
      %9 = "func.call"(%arg14, %8, %arg16) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s2"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%9)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%10: !exec.stop):  // 10 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12
      %11 = "exec.failed"(%10) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%11) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%12: i1):  // pred: ^bb1
      %13 = "exec.test"(%arg14, %12) <{site = "s3"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%13)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb4(%14: i1):  // pred: ^bb3
      "cf.cond_br"(%14)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %15 = "runtime.enter_scope"(%arg14) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s3"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%15)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %16 = "runtime.enter_scope"(%arg14) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s3"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%16)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // 2 preds: ^bb10, ^bb13
      %17 = "exec.apply"(%arg14, %arg15) <{binding = @zkl_binding_8, parameters = [], site = "s5"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%17)[^bb14, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%18: !runtime.scope):  // pred: ^bb5
      %19 = "func.call"(%18) <{callee = @zkl_control_11}> : (!runtime.scope) -> !exec.outcome<>
      %20 = "runtime.exit_scope"(%18, %19) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%20)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb9(%21: !runtime.transfer<>):  // pred: ^bb8
      %22 = "runtime.accept_transfer"(%arg14, %21) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%22)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb10:  // pred: ^bb9
      "cf.br"()[^bb7] : () -> ()
    ^bb11(%23: !runtime.scope):  // pred: ^bb6
      %24 = "func.call"(%23) <{callee = @zkl_control_12}> : (!runtime.scope) -> !exec.outcome<>
      %25 = "runtime.exit_scope"(%23, %24) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%25)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb12(%26: !runtime.transfer<>):  // pred: ^bb11
      %27 = "runtime.accept_transfer"(%arg14, %26) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%27)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb13:  // pred: ^bb12
      "cf.br"()[^bb7] : () -> ()
    ^bb14(%28: !algebra.field_vector<"bls12-381.fr">, %29: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb7
      %30 = "exec.returned"(%28, %29) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%30) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561726h68616c766573", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_11", sym_visibility = "private"}> ({
    ^bb0(%arg13: !runtime.scope):
      %6 = "exec.complete"(%arg13) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%6) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_12", sym_visibility = "private"}> ({
    ^bb0(%arg12: !runtime.scope):
      %3 = "exec.reject"(%arg12) <{reason = "reject", site = "s3_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%3)[^bb1] : (!exec.stop) -> ()
    ^bb1(%4: !exec.stop):  // pred: ^bb0
      %5 = "exec.failed"(%4) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%5) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5", sym_visibility = "private"}> ({
    ^bb0(%arg9: !algebra.field<"bls12-381.fr">, %arg10: !algebra.field<"bls12-381.fr">, %arg11: !algebra.field<"bls12-381.fr">):
      %0 = "algebra.field_subtract"(%arg10, %arg9) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %1 = "algebra.field_multiply"(%0, %arg11) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %2 = "algebra.field_add"(%arg9, %1) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%2) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">, sym_name = "zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", sym_visibility = "private"}> ({
    ^bb0(%arg6: !algebra.field_vector<"bls12-381.fr">, %arg7: ui64, %arg8: ui64):
      "func.return"(%arg6) : (!algebra.field_vector<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64, sym_name = "zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94", sym_visibility = "private"}> ({
    ^bb0(%arg3: !algebra.field_vector<"bls12-381.fr">, %arg4: ui64, %arg5: ui64):
      "func.return"(%arg4) : (ui64) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64, sym_name = "zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275", sym_visibility = "private"}> ({
    ^bb0(%arg0: !algebra.field_vector<"bls12-381.fr">, %arg1: ui64, %arg2: ui64):
      "func.return"(%arg2) : (ui64) -> ()
    }) : () -> ()
  }) : () -> ()
}) : () -> ()

