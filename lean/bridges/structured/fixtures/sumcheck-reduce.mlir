"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
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
    "protocol.func"() <{contracts = [], function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), input_roles = [["role00000000"], ["role00000000"], ["role00000001"], ["role00000000", "role00000001"], ["role00000001"]], origin = ["sums::Reduction", [["F", ["field", "bls12-381.fr"]], ["Max", ["nat", "4"]]]], output_roles = [["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_cf3586ba980b617860654dacf2506dd277a78d1dcf5b84bcc6376225e7fe4f45"}> ({
    ^bb0(%arg115: !algebra.field_vector<"bls12-381.fr">, %arg116: ui64, %arg117: !algebra.field<"bls12-381.fr">, %arg118: ui64, %arg119: !protocol.service_ref<"random.bls12-381.fr/0">):
      %312 = "data.index"() <{value = "1"}> : () -> ui64
      %313:3 = "protocol.local_call"(%arg115, %arg116, %312) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a, role = "role00000000", site = "s1"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      %314:2 = "protocol.local_call"(%arg117) <{callee = @zkl_c0a3a2b8b5f989e0e9c138a171631d20dc8bd296769b6ee7636d2d79a8518ba0, role = "role00000001", site = "s3"}> : (!algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %315:6 = "protocol.apply"(%313#0, %313#1, %313#2, %314#0, %314#1, %arg118, %arg119) <{callee = @zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d, roles = ["role00000000", "role00000001"], site = "s5"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %316 = "func.call"(%315#1, %315#2, %315#3) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">
      "protocol.return"(%315#0, %316, %315#4, %315#5) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", sym_visibility = "private"}> ({
    ^bb0(%arg111: !runtime.scope, %arg112: !algebra.field_vector<"bls12-381.fr">, %arg113: ui64, %arg114: ui64):
      %293 = "func.call"(%arg111, %arg112, %arg113, %arg114) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655}> {runtime.site = "s0"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%293)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%294: i1):  // pred: ^bb0
      %295 = "exec.test"(%arg111, %294) <{site = "s1"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%295)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%296: !exec.stop):  // 8 preds: ^bb0, ^bb1, ^bb4, ^bb5, ^bb7, ^bb8, ^bb10, ^bb11
      %297 = "exec.failed"(%296) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%297) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb3(%298: i1):  // pred: ^bb1
      "cf.cond_br"(%298)[^bb4, ^bb5] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb4:  // pred: ^bb3
      %299 = "runtime.enter_scope"(%arg111) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%299)[^bb7, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb5:  // pred: ^bb3
      %300 = "runtime.enter_scope"(%arg111) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%300)[^bb10, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // 2 preds: ^bb9, ^bb12
      %301 = "exec.returned"(%arg112, %arg113, %arg114) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%301) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb7(%302: !runtime.scope):  // pred: ^bb4
      %303 = "func.call"(%302) <{callee = @zkl_control_0}> : (!runtime.scope) -> !exec.outcome<>
      %304 = "runtime.exit_scope"(%302, %303) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%304)[^bb8, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb8(%305: !runtime.transfer<>):  // pred: ^bb7
      %306 = "runtime.accept_transfer"(%arg111, %305) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%306)[^bb9, ^bb2] : (!exec.outcome<>) -> ()
    ^bb9:  // pred: ^bb8
      "cf.br"()[^bb6] : () -> ()
    ^bb10(%307: !runtime.scope):  // pred: ^bb5
      %308 = "func.call"(%307) <{callee = @zkl_control_1}> : (!runtime.scope) -> !exec.outcome<>
      %309 = "runtime.exit_scope"(%307, %308) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%309)[^bb11, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb11(%310: !runtime.transfer<>):  // pred: ^bb10
      %311 = "runtime.accept_transfer"(%arg111, %310) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%311)[^bb12, ^bb2] : (!exec.outcome<>) -> ()
    ^bb12:  // pred: ^bb11
      "cf.br"()[^bb6] : () -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561725h7461626c65", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_0", sym_visibility = "private"}> ({
    ^bb0(%arg110: !runtime.scope):
      %292 = "exec.complete"(%arg110) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%292) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_1", sym_visibility = "private"}> ({
    ^bb0(%arg109: !runtime.scope):
      %289 = "exec.reject"(%arg109) <{reason = "reject", site = "s1_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%289)[^bb1] : (!exec.stop) -> ()
    ^bb1(%290: !exec.stop):  // pred: ^bb0
      %291 = "exec.failed"(%290) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%291) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", sym_visibility = "private"}> ({
    ^bb0(%arg105: !runtime.scope, %arg106: !algebra.field_vector<"bls12-381.fr">, %arg107: ui64, %arg108: ui64):
      %231 = "exec.apply"(%arg105) <{binding = @zkl_binding_0, parameters = ["0"], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%231)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%232: ui64):  // pred: ^bb0
      %233 = "func.call"(%arg105, %232, %arg108) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s1"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%233)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%234: !exec.stop):  // 23 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12, ^bb15, ^bb16, ^bb17, ^bb18, ^bb19, ^bb21, ^bb22, ^bb25, ^bb26, ^bb28, ^bb29, ^bb31, ^bb32
      %235 = "exec.failed"(%234) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%235) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%236: i1):  // pred: ^bb1
      %237 = "exec.test"(%arg105, %236) <{site = "s3"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%237)[^bb4, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb4(%238: i1):  // pred: ^bb3
      "cf.cond_br"(%238)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %239 = "runtime.enter_scope"(%arg105, %arg107) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "then", site = "s3"}> : (!runtime.scope, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%239)[^bb8, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %240 = "runtime.enter_scope"(%arg105, %arg107) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "else", site = "s3"}> : (!runtime.scope, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%240)[^bb11, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7(%241: i1):  // 2 preds: ^bb10, ^bb13
      %242 = "exec.test"(%arg105, %241) <{site = "s11"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%242)[^bb14, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb8(%243: !runtime.scope):  // pred: ^bb5
      %244 = "func.call"(%243, %arg107) <{callee = @zkl_control_2}> : (!runtime.scope, ui64) -> !exec.outcome<(i1)>
      %245 = "runtime.exit_scope"(%243, %244) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%245)[^bb9, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb9(%246: !runtime.transfer<(i1)>):  // pred: ^bb8
      %247 = "runtime.accept_transfer"(%arg105, %246) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%247)[^bb10, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb10(%248: i1):  // pred: ^bb9
      "cf.br"(%248)[^bb7] : (i1) -> ()
    ^bb11(%249: !runtime.scope):  // pred: ^bb6
      %250 = "func.call"(%249, %arg107) <{callee = @zkl_control_3}> : (!runtime.scope, ui64) -> !exec.outcome<(i1)>
      %251 = "runtime.exit_scope"(%249, %250) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%251)[^bb12, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb12(%252: !runtime.transfer<(i1)>):  // pred: ^bb11
      %253 = "runtime.accept_transfer"(%arg105, %252) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%253)[^bb13, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb13(%254: i1):  // pred: ^bb12
      "cf.br"(%254)[^bb7] : (i1) -> ()
    ^bb14(%255: i1):  // pred: ^bb7
      "cf.cond_br"(%255)[^bb15, ^bb16] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb15:  // pred: ^bb14
      %256 = "runtime.enter_scope"(%arg105, %arg106, %arg108) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "then", site = "s11"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%256)[^bb18, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb16:  // pred: ^bb14
      %257 = "runtime.enter_scope"(%arg105, %arg106, %arg108) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "else", site = "s11"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%257)[^bb21, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb17(%258: i1):  // 2 preds: ^bb20, ^bb23
      %259 = "exec.test"(%arg105, %258) <{site = "s22"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%259)[^bb24, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb18(%260: !runtime.scope):  // pred: ^bb15
      %261 = "func.call"(%260, %arg106, %arg108) <{callee = @zkl_control_4}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>
      %262 = "runtime.exit_scope"(%260, %261) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%262)[^bb19, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb19(%263: !runtime.transfer<(i1)>):  // pred: ^bb18
      %264 = "runtime.accept_transfer"(%arg105, %263) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%264)[^bb20, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb20(%265: i1):  // pred: ^bb19
      "cf.br"(%265)[^bb17] : (i1) -> ()
    ^bb21(%266: !runtime.scope):  // pred: ^bb16
      %267 = "func.call"(%266, %arg106, %arg108) <{callee = @zkl_control_5}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>
      %268 = "runtime.exit_scope"(%266, %267) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%268)[^bb22, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb22(%269: !runtime.transfer<(i1)>):  // pred: ^bb21
      %270 = "runtime.accept_transfer"(%arg105, %269) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%270)[^bb23, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb23(%271: i1):  // pred: ^bb22
      "cf.br"(%271)[^bb17] : (i1) -> ()
    ^bb24(%272: i1):  // pred: ^bb17
      "cf.cond_br"(%272)[^bb25, ^bb26] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb25:  // pred: ^bb24
      %273 = "runtime.enter_scope"(%arg105, %arg106, %arg107, %arg108) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "then", site = "s22"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%273)[^bb28, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb26:  // pred: ^bb24
      %274 = "runtime.enter_scope"(%arg105, %arg106, %arg107, %arg108) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "else", site = "s22"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%274)[^bb31, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb27(%275: i1):  // 2 preds: ^bb30, ^bb33
      %276 = "exec.returned"(%275) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%276) : (!exec.outcome<(i1)>) -> ()
    ^bb28(%277: !runtime.scope):  // pred: ^bb25
      %278 = "func.call"(%277, %arg106, %arg107, %arg108) <{callee = @zkl_control_6}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      %279 = "runtime.exit_scope"(%277, %278) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%279)[^bb29, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb29(%280: !runtime.transfer<(i1)>):  // pred: ^bb28
      %281 = "runtime.accept_transfer"(%arg105, %280) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%281)[^bb30, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb30(%282: i1):  // pred: ^bb29
      "cf.br"(%282)[^bb27] : (i1) -> ()
    ^bb31(%283: !runtime.scope):  // pred: ^bb26
      %284 = "func.call"(%283, %arg106, %arg107, %arg108) <{callee = @zkl_control_7}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      %285 = "runtime.exit_scope"(%283, %284) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%285)[^bb32, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb32(%286: !runtime.transfer<(i1)>):  // pred: ^bb31
      %287 = "runtime.accept_transfer"(%arg105, %286) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%287)[^bb33, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb33(%288: i1):  // pred: ^bb32
      "cf.br"(%288)[^bb27] : (i1) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_2", sym_visibility = "private"}> ({
    ^bb0(%arg103: !runtime.scope, %arg104: ui64):
      %224 = "exec.apply"(%arg103) <{binding = @zkl_binding_0, parameters = ["64"], site = "s4"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%224)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%225: ui64):  // pred: ^bb0
      %226 = "func.call"(%arg103, %arg104, %225) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s5"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%226)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%227: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %228 = "exec.failed"(%227) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%228) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%229: i1):  // pred: ^bb1
      %230 = "exec.complete"(%arg103, %229) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%230) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_3", sym_visibility = "private"}> ({
    ^bb0(%arg101: !runtime.scope, %arg102: ui64):
      %219 = "exec.boolean"(%arg101) <{site = "s7", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%219)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%220: i1):  // pred: ^bb0
      %221 = "exec.complete"(%arg101, %220) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%221) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%222: !exec.stop):  // pred: ^bb0
      %223 = "exec.failed"(%222) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%223) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_4", sym_visibility = "private"}> ({
    ^bb0(%arg98: !runtime.scope, %arg99: !algebra.field_vector<"bls12-381.fr">, %arg100: ui64):
      %208 = "exec.apply"(%arg98, %arg99) <{binding = @zkl_binding_1, parameters = [], site = "s12"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%208)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%209: ui64):  // pred: ^bb0
      %210 = "exec.apply"(%arg98, %209, %arg100) <{binding = @zkl_binding_2, parameters = [], site = "s13"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%210)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%211: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %212 = "exec.failed"(%211) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%212) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%213: ui64):  // pred: ^bb1
      %214 = "exec.apply"(%arg98) <{binding = @zkl_binding_0, parameters = ["0"], site = "s14"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%214)[^bb4, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%215: ui64):  // pred: ^bb3
      %216 = "exec.apply"(%arg98, %213, %215) <{binding = @zkl_binding_3, parameters = [], site = "s15"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%216)[^bb5, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb5(%217: i1):  // pred: ^bb4
      %218 = "exec.complete"(%arg98, %217) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%218) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_5", sym_visibility = "private"}> ({
    ^bb0(%arg95: !runtime.scope, %arg96: !algebra.field_vector<"bls12-381.fr">, %arg97: ui64):
      %203 = "exec.boolean"(%arg95) <{site = "s17", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%203)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%204: i1):  // pred: ^bb0
      %205 = "exec.complete"(%arg95, %204) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%205) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%206: !exec.stop):  // pred: ^bb0
      %207 = "exec.failed"(%206) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%207) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_6", sym_visibility = "private"}> ({
    ^bb0(%arg91: !runtime.scope, %arg92: !algebra.field_vector<"bls12-381.fr">, %arg93: ui64, %arg94: ui64):
      %192 = "exec.apply"(%arg91, %arg92) <{binding = @zkl_binding_1, parameters = [], site = "s23"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%192)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%193: ui64):  // pred: ^bb0
      %194 = "exec.apply"(%arg91, %193, %arg94) <{binding = @zkl_binding_4, parameters = [], site = "s24"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%194)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%195: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %196 = "exec.failed"(%195) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%196) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%197: ui64):  // pred: ^bb1
      %198 = "func.call"(%arg91, %arg93) <{callee = @s3h7a6b6311h6d756c74696c696e6561724h726f7773}> {runtime.site = "s25"} : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%198)[^bb4, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%199: ui64):  // pred: ^bb3
      %200 = "exec.apply"(%arg91, %197, %199) <{binding = @zkl_binding_3, parameters = [], site = "s26"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%200)[^bb5, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb5(%201: i1):  // pred: ^bb4
      %202 = "exec.complete"(%arg91, %201) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%202) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_7", sym_visibility = "private"}> ({
    ^bb0(%arg87: !runtime.scope, %arg88: !algebra.field_vector<"bls12-381.fr">, %arg89: ui64, %arg90: ui64):
      %187 = "exec.boolean"(%arg87) <{site = "s28", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%187)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%188: i1):  // pred: ^bb0
      %189 = "exec.complete"(%arg87, %188) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%189) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%190: !exec.stop):  // pred: ^bb0
      %191 = "exec.failed"(%190) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%191) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "s3h7a6b637h696e64696365734h6c657373", sym_visibility = "private"}> ({
    ^bb0(%arg84: !runtime.scope, %arg85: ui64, %arg86: ui64):
      %182 = "exec.apply"(%arg84, %arg85, %arg86) <{binding = @zkl_binding_5, parameters = [], site = "s0"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%182)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%183: i1):  // pred: ^bb0
      %184 = "exec.returned"(%183) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%184) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%185: !exec.stop):  // pred: ^bb0
      %186 = "exec.failed"(%185) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%186) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.origin = ["s3h7a6b637h696e64696365734h6c657373", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "s3h7a6b6311h6d756c74696c696e6561724h726f7773", sym_visibility = "private"}> ({
    ^bb0(%arg82: !runtime.scope, %arg83: ui64):
      %135 = "exec.apply"(%arg82) <{binding = @zkl_binding_0, parameters = ["64"], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%135)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%136: ui64):  // pred: ^bb0
      %137 = "func.call"(%arg82, %arg83, %136) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s1"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%137)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%138: !exec.stop):  // 14 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12, ^bb14, ^bb15, ^bb19, ^bb21
      %139 = "exec.failed"(%138) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%139) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%140: i1):  // pred: ^bb1
      %141 = "exec.test"(%arg82, %140) <{site = "s2"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%141)[^bb4, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb4(%142: i1):  // pred: ^bb3
      "cf.cond_br"(%142)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %143 = "runtime.enter_scope"(%arg82) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s2"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%143)[^bb8, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %144 = "runtime.enter_scope"(%arg82) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s2"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%144)[^bb11, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // 2 preds: ^bb10, ^bb13
      %145 = "exec.apply"(%arg82) <{binding = @zkl_binding_0, parameters = ["1"], site = "s3"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%145)[^bb14, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb8(%146: !runtime.scope):  // pred: ^bb5
      %147 = "func.call"(%146) <{callee = @zkl_control_8}> : (!runtime.scope) -> !exec.outcome<>
      %148 = "runtime.exit_scope"(%146, %147) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%148)[^bb9, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb9(%149: !runtime.transfer<>):  // pred: ^bb8
      %150 = "runtime.accept_transfer"(%arg82, %149) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%150)[^bb10, ^bb2] : (!exec.outcome<>) -> ()
    ^bb10:  // pred: ^bb9
      "cf.br"()[^bb7] : () -> ()
    ^bb11(%151: !runtime.scope):  // pred: ^bb6
      %152 = "func.call"(%151) <{callee = @zkl_control_9}> : (!runtime.scope) -> !exec.outcome<>
      %153 = "runtime.exit_scope"(%151, %152) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%153)[^bb12, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb12(%154: !runtime.transfer<>):  // pred: ^bb11
      %155 = "runtime.accept_transfer"(%arg82, %154) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%155)[^bb13, ^bb2] : (!exec.outcome<>) -> ()
    ^bb13:  // pred: ^bb12
      "cf.br"()[^bb7] : () -> ()
    ^bb14(%156: ui64):  // pred: ^bb7
      %157 = "exec.apply"(%arg82) <{binding = @zkl_binding_0, parameters = ["0"], site = "s5"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%157)[^bb15, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb15(%158: ui64):  // pred: ^bb14
      %159 = "exec.range"(%arg82, %158, %arg83) <{site = "s6"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%159)[^bb16, ^bb2] : (!exec.outcome<(i64, i64)>) -> ()
    ^bb16(%160: i64, %161: i64):  // pred: ^bb15
      %162 = "runtime.borrow_transfer"(%arg82, %156) : (!runtime.scope, ui64) -> !runtime.transfer<(ui64)>
      "cf.br"(%160, %162)[^bb17] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb17(%163: i64, %164: !runtime.transfer<(ui64)>):  // 2 preds: ^bb16, ^bb20
      %165 = "arith.cmpi"(%163, %161) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%165, %164)[^bb18, ^bb19] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(ui64)>) -> ()
    ^bb18:  // pred: ^bb17
      %166 = "runtime.iteration"(%arg82, %163) <{site = "s6"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%166)[^bb22, ^bb21] : (!exec.outcome<(ui64)>) -> ()
    ^bb19(%167: !runtime.transfer<(ui64)>):  // pred: ^bb17
      %168 = "runtime.accept_transfer"(%arg82, %167) : (!runtime.scope, !runtime.transfer<(ui64)>) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%168)[^bb25, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb20(%169: !runtime.transfer<(ui64)>):  // pred: ^bb24
      %170 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %171 = "arith.addi"(%163, %170) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%171, %169)[^bb17] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb21(%172: !exec.stop):  // 3 preds: ^bb18, ^bb22, ^bb23
      "runtime.release_transfer"(%164) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%172)[^bb2] : (!exec.stop) -> ()
    ^bb22(%173: ui64):  // pred: ^bb18
      %174 = "runtime.transfer_values"(%164) : (!runtime.transfer<(ui64)>) -> ui64
      %175 = "runtime.enter_scope"(%arg82, %163, %173, %174) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 2>, site = "s6"}> : (!runtime.scope, i64, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%175)[^bb23, ^bb21] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb23(%176: !runtime.scope):  // pred: ^bb22
      %177 = "func.call"(%176, %173, %174) <{callee = @zkl_control_10}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      %178 = "runtime.exit_scope"(%176, %177) : (!runtime.scope, !exec.outcome<(ui64)>) -> !exec.outcome<(!runtime.transfer<(ui64)>)>
      "exec.dispatch"(%178)[^bb24, ^bb21] : (!exec.outcome<(!runtime.transfer<(ui64)>)>) -> ()
    ^bb24(%179: !runtime.transfer<(ui64)>):  // pred: ^bb23
      "runtime.release_transfer"(%164) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%179)[^bb20] : (!runtime.transfer<(ui64)>) -> ()
    ^bb25(%180: ui64):  // pred: ^bb19
      %181 = "exec.returned"(%180) : (ui64) -> !exec.outcome<(ui64)>
      "func.return"(%181) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561724h726f7773", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_8", sym_visibility = "private"}> ({
    ^bb0(%arg81: !runtime.scope):
      %134 = "exec.complete"(%arg81) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%134) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_9", sym_visibility = "private"}> ({
    ^bb0(%arg80: !runtime.scope):
      %131 = "exec.reject"(%arg80) <{reason = "reject", site = "s2_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%131)[^bb1] : (!exec.stop) -> ()
    ^bb1(%132: !exec.stop):  // pred: ^bb0
      %133 = "exec.failed"(%132) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%133) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "zkl_control_10", sym_visibility = "private"}> ({
    ^bb0(%arg77: !runtime.scope, %arg78: ui64, %arg79: ui64):
      %124 = "exec.apply"(%arg77) <{binding = @zkl_binding_0, parameters = ["2"], site = "s7"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%124)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%125: ui64):  // pred: ^bb0
      %126 = "exec.apply"(%arg77, %arg79, %125) <{binding = @zkl_binding_6, parameters = [], site = "s8"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%126)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%127: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %128 = "exec.failed"(%127) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%128) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%129: ui64):  // pred: ^bb1
      %130 = "exec.complete"(%arg77, %129) : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "func.return"(%130) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_c0a3a2b8b5f989e0e9c138a171631d20dc8bd296769b6ee7636d2d79a8518ba0", sym_visibility = "private"}> ({
    ^bb0(%arg75: !runtime.scope, %arg76: !algebra.field<"bls12-381.fr">):
      %119 = "exec.apply"(%arg75) <{binding = @zkl_binding_7, parameters = [], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%119)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%120: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %121 = "exec.returned"(%120, %arg76) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%121) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%122: !exec.stop):  // pred: ^bb0
      %123 = "exec.failed"(%122) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%123) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s8h73756d636865636b7h70656e64696e67", []]} : () -> ()
    "protocol.func"() <{contracts = [["input", "shape", [@zkl_8c866415d5a42d7cb60d6b39dd52568c20001248a901906f13a3d5d9dd8f74ac, [["input", 0, "role00000000"], ["input", 1, "role00000000"], ["input", 2, "role00000000"]]], unit, unit], ["continuation", "initial_sum", [@zkl_f03c5af270c09f9d5e832cdb0dc1d71151cebecfaaa08c6cacd997dde03860e9, [["input", 0, "role00000000"], ["input", 1, "role00000000"], ["input", 2, "role00000000"], ["input", 3, "role00000001"], ["input", 4, "role00000001"]]], [@zkl_f03c5af270c09f9d5e832cdb0dc1d71151cebecfaaa08c6cacd997dde03860e9, [["input", 0, "role00000000"], ["input", 1, "role00000000"], ["input", 2, "role00000000"], ["output", 4, "role00000001"], ["output", 5, "role00000001"]]], unit]], function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), input_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"], ["role00000000", "role00000001"], ["role00000001"]], origin = ["sumcheck::Reduce", [["F", ["field", "bls12-381.fr"]], ["Max", ["nat", "4"]]]], output_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d"}> ({
    ^bb0(%arg60: !algebra.field_vector<"bls12-381.fr">, %arg61: ui64, %arg62: ui64, %arg63: !algebra.field_vector<"bls12-381.fr">, %arg64: !algebra.field<"bls12-381.fr">, %arg65: ui64, %arg66: !protocol.service_ref<"random.bls12-381.fr/0">):
      %90 = "func.call"(%arg60, %arg61, %arg62) <{callee = @zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %91 = "data.index"() <{value = "1"}> : () -> ui64
      %92 = "data.index_equal"(%90, %91) : (ui64, ui64) -> i1
      "protocol.guard"(%92) <{owner = "role00000000", site = "s3"}> : (i1) -> ()
      %93 = "func.call"(%arg60, %arg61, %arg62) <{callee = @zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %94 = "protocol.local_call"(%93, %arg65) <{callee = @s3h7a6b637h696e64696365734h6c657373, role = "role00000000", site = "s5"}> : (ui64, ui64) -> i1
      %95 = "arith.constant"() <{value = false}> : () -> i1
      %96 = "arith.cmpi"(%94, %95) <{predicate = 0 : i64}> : (i1, i1) -> i1
      "protocol.guard"(%96) <{owner = "role00000000", site = "s8"}> : (i1) -> ()
      %97 = "protocol.local_call"() <{callee = @zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f, role = "role00000000", site = "s10"}> : () -> !algebra.field_vector<"bls12-381.fr">
      %98:2 = "protocol.local_call"(%arg63, %arg64) <{callee = @zkl_e8df957aab384c1d5416600c13a571512206e97abfbf6e0e9cddac5c84860d07, role = "role00000001", site = "s12"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %99:6 = "protocol.repeat"(%arg65, %arg60, %arg61, %arg62, %97, %98#0, %98#1, %arg66) <{carried = 6 : i64, carried_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"]], maximum = 4 : i64, roles = ["role00000000", "role00000001"], site = "s18"}> ({
      ^bb0(%arg67: ui64, %arg68: !algebra.field_vector<"bls12-381.fr">, %arg69: ui64, %arg70: ui64, %arg71: !algebra.field_vector<"bls12-381.fr">, %arg72: !algebra.field_vector<"bls12-381.fr">, %arg73: !algebra.field<"bls12-381.fr">, %arg74: !protocol.service_ref<"random.bls12-381.fr/0">):
        %101:2 = "protocol.local_call"(%arg68, %arg69, %arg70) <{callee = @zkl_532a609cf36a935835501ca51308940142121e647ca360843a880bf231f04aa6, role = "role00000000", site = "s19"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %102 = "protocol.exchange"(%101#0) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %103 = "protocol.restrict_roles"(%102) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %104 = "protocol.exchange"(%101#1) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_1"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %105 = "protocol.restrict_roles"(%104) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %106 = "algebra.field_add"(%103, %105) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %107 = "algebra.field_equal"(%arg73, %106) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
        "protocol.guard"(%107) <{owner = "role00000001", site = "s27"}> : (i1) -> ()
        %108 = "protocol.query"(%arg74) <{method = "draw", owner = "role00000001", site = "label_6368616c6c656e6765"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
        %109 = "protocol.exchange"(%108) <{receiver = "role00000000", sender = "role00000001", site = "label_64656c6976657279_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %110 = "protocol.restrict_roles"(%109) <{roles = ["role00000000"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %111:3 = "protocol.local_call"(%arg68, %arg69, %arg70, %110) <{callee = @zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d, role = "role00000000", site = "s32"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
        %112 = "protocol.local_call"(%arg71, %110) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000000", site = "s34"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
        %113 = "protocol.local_call"(%arg72, %108) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000001", site = "s36"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
        %114 = "algebra.constant"() <{value = "1"}> : () -> !algebra.field<"bls12-381.fr">
        %115 = "algebra.field_subtract"(%114, %108) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %116 = "algebra.field_multiply"(%115, %103) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %117 = "algebra.field_multiply"(%108, %105) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %118 = "algebra.field_add"(%116, %117) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        "protocol.yield"(%111#0, %111#1, %111#2, %112, %113, %118) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
      }) : (ui64, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %100:2 = "protocol.local_call"(%99#4, %99#5) <{callee = @zkl_c36a2d2c6bd38573735fb9b90d1a3848c562d2c1f688234e2b669408e9c9eea9, role = "role00000001", site = "s48"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      "protocol.return"(%99#3, %99#0, %99#1, %99#2, %100#0, %100#1) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1, sym_name = "zkf_326ab2331715c62ba21cb6a967c927ba6ad7f7f2da5e84eb0e5de0fc610f26ca", sym_visibility = "private"}> ({
    ^bb0(%arg57: !algebra.field_vector<"bls12-381.fr">, %arg58: ui64, %arg59: ui64):
      %82 = "func.call"(%arg57, %arg58, %arg59) <{callee = @zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %83 = "data.index"() <{value = "1"}> : () -> ui64
      %84 = "data.index_equal"(%82, %83) : (ui64, ui64) -> i1
      %85 = "func.call"(%arg57, %arg58, %arg59) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">
      %86 = "data.dim"(%85) <{axis = 0 : i64}> : (!algebra.field_vector<"bls12-381.fr">) -> ui64
      %87 = "func.call"(%arg57, %arg58, %arg59) <{callee = @zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %88 = "data.index_power_of_two"(%86, %87) : (ui64, ui64) -> i1
      %89 = "arith.andi"(%84, %88) : (i1, i1) -> i1
      "func.return"(%89) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64, sym_name = "zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275", sym_visibility = "private"}> ({
    ^bb0(%arg54: !algebra.field_vector<"bls12-381.fr">, %arg55: ui64, %arg56: ui64):
      "func.return"(%arg56) : (ui64) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">, sym_name = "zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", sym_visibility = "private"}> ({
    ^bb0(%arg51: !algebra.field_vector<"bls12-381.fr">, %arg52: ui64, %arg53: ui64):
      "func.return"(%arg51) : (!algebra.field_vector<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64, sym_name = "zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94", sym_visibility = "private"}> ({
    ^bb0(%arg48: !algebra.field_vector<"bls12-381.fr">, %arg49: ui64, %arg50: ui64):
      "func.return"(%arg49) : (ui64) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "zkf_c51d11bf318ad26bc2fce7b89eec63f85b98f57e91e0e9e6256f84a573b5b6e6", sym_visibility = "private"}> ({
    ^bb0(%arg43: !algebra.field_vector<"bls12-381.fr">, %arg44: ui64, %arg45: ui64, %arg46: !algebra.field_vector<"bls12-381.fr">, %arg47: !algebra.field<"bls12-381.fr">):
      %78 = "func.call"(%arg43, %arg44, %arg45) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">
      %79 = "algebra.multilinear_restrict_prefix"(%78, %arg46) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
      %80 = "func.call"(%79) <{callee = @zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e}> : (!algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %81 = "algebra.field_equal"(%arg47, %80) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "func.return"(%81) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e", sym_visibility = "private"}> ({
    ^bb0(%arg42: !algebra.field_vector<"bls12-381.fr">):
      %76 = "algebra.constant"() <{value = "0"}> : () -> !algebra.field<"bls12-381.fr">
      %77 = "algebra.finite_fold"(%arg42, %76) <{domain = @finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_domain, step = @finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_body}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%77) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_domain", sym_visibility = "private"}> ({
    ^bb0(%arg41: !algebra.field_vector<"bls12-381.fr">):
      %75 = "data.domain_elements"(%arg41) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%75) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_body", sym_visibility = "private"}> ({
    ^bb0(%arg38: !algebra.field<"bls12-381.fr">, %arg39: !algebra.field<"bls12-381.fr">, %arg40: !algebra.field_vector<"bls12-381.fr">):
      %74 = "func.call"(%arg38, %arg39) <{callee = @zkl_3fc17a64a5bb6e75192d0a1362e9954f0d434a10d0f93e319db6b516835a1005}> : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%74) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_3fc17a64a5bb6e75192d0a1362e9954f0d434a10d0f93e319db6b516835a1005", sym_visibility = "private"}> ({
    ^bb0(%arg36: !algebra.field<"bls12-381.fr">, %arg37: !algebra.field<"bls12-381.fr">):
      %73 = "algebra.field_add"(%arg36, %arg37) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%73) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", sym_visibility = "private"}> ({
    ^bb0(%arg35: !runtime.scope):
      %68 = "exec.apply"(%arg35) <{binding = @zkl_binding_7, parameters = [], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%68)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%69: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %70 = "exec.returned"(%69) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%70) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%71: !exec.stop):  // pred: ^bb0
      %72 = "exec.failed"(%71) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%72) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6310h7072696d6974697665736h766563746f725h656d707479", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_e8df957aab384c1d5416600c13a571512206e97abfbf6e0e9cddac5c84860d07", sym_visibility = "private"}> ({
    ^bb0(%arg32: !runtime.scope, %arg33: !algebra.field_vector<"bls12-381.fr">, %arg34: !algebra.field<"bls12-381.fr">):
      %67 = "exec.returned"(%arg33, %arg34) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%67) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s8h73756d636865636b10h6f70656e5f636c61696d", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_532a609cf36a935835501ca51308940142121e647ca360843a880bf231f04aa6", sym_visibility = "private"}> ({
    ^bb0(%arg28: !runtime.scope, %arg29: !algebra.field_vector<"bls12-381.fr">, %arg30: ui64, %arg31: ui64):
      %57 = "func.call"(%arg28, %arg29, %arg30, %arg31) <{callee = @zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087}> {runtime.site = "s0"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%57)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%58: !algebra.field_vector<"bls12-381.fr">, %59: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %60 = "exec.apply"(%arg28, %58) <{binding = @zkl_binding_8, parameters = [], site = "s3"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%60)[^bb3, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%61: !exec.stop):  // 3 preds: ^bb0, ^bb1, ^bb3
      %62 = "exec.failed"(%61) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%62) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb3(%63: !algebra.field<"bls12-381.fr">):  // pred: ^bb1
      %64 = "exec.apply"(%arg28, %59) <{binding = @zkl_binding_8, parameters = [], site = "s5"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%64)[^bb4, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb4(%65: !algebra.field<"bls12-381.fr">):  // pred: ^bb3
      %66 = "exec.returned"(%63, %65) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%66) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s8h73756d636865636b4h73756d73", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087", sym_visibility = "private"}> ({
    ^bb0(%arg24: !runtime.scope, %arg25: !algebra.field_vector<"bls12-381.fr">, %arg26: ui64, %arg27: ui64):
      %33 = "exec.apply"(%arg24) <{binding = @zkl_binding_0, parameters = ["0"], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%33)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%34: ui64):  // pred: ^bb0
      %35 = "func.call"(%arg24, %34, %arg26) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s2"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%35)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%36: !exec.stop):  // 10 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12
      %37 = "exec.failed"(%36) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%37) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%38: i1):  // pred: ^bb1
      %39 = "exec.test"(%arg24, %38) <{site = "s3"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%39)[^bb4, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb4(%40: i1):  // pred: ^bb3
      "cf.cond_br"(%40)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %41 = "runtime.enter_scope"(%arg24) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s3"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%41)[^bb8, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %42 = "runtime.enter_scope"(%arg24) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s3"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%42)[^bb11, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // 2 preds: ^bb10, ^bb13
      %43 = "exec.apply"(%arg24, %arg25) <{binding = @zkl_binding_9, parameters = [], site = "s5"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%43)[^bb14, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%44: !runtime.scope):  // pred: ^bb5
      %45 = "func.call"(%44) <{callee = @zkl_control_11}> : (!runtime.scope) -> !exec.outcome<>
      %46 = "runtime.exit_scope"(%44, %45) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%46)[^bb9, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb9(%47: !runtime.transfer<>):  // pred: ^bb8
      %48 = "runtime.accept_transfer"(%arg24, %47) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%48)[^bb10, ^bb2] : (!exec.outcome<>) -> ()
    ^bb10:  // pred: ^bb9
      "cf.br"()[^bb7] : () -> ()
    ^bb11(%49: !runtime.scope):  // pred: ^bb6
      %50 = "func.call"(%49) <{callee = @zkl_control_12}> : (!runtime.scope) -> !exec.outcome<>
      %51 = "runtime.exit_scope"(%49, %50) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%51)[^bb12, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb12(%52: !runtime.transfer<>):  // pred: ^bb11
      %53 = "runtime.accept_transfer"(%arg24, %52) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%53)[^bb13, ^bb2] : (!exec.outcome<>) -> ()
    ^bb13:  // pred: ^bb12
      "cf.br"()[^bb7] : () -> ()
    ^bb14(%54: !algebra.field_vector<"bls12-381.fr">, %55: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb7
      %56 = "exec.returned"(%54, %55) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%56) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561726h68616c766573", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_11", sym_visibility = "private"}> ({
    ^bb0(%arg23: !runtime.scope):
      %32 = "exec.complete"(%arg23) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%32) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_12", sym_visibility = "private"}> ({
    ^bb0(%arg22: !runtime.scope):
      %29 = "exec.reject"(%arg22) <{reason = "reject", site = "s3_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%29)[^bb1] : (!exec.stop) -> ()
    ^bb1(%30: !exec.stop):  // pred: ^bb0
      %31 = "exec.failed"(%30) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%31) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d", sym_visibility = "private"}> ({
    ^bb0(%arg17: !runtime.scope, %arg18: !algebra.field_vector<"bls12-381.fr">, %arg19: ui64, %arg20: ui64, %arg21: !algebra.field<"bls12-381.fr">):
      %17 = "func.call"(%arg17, %arg18, %arg19, %arg20) <{callee = @zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087}> {runtime.site = "s0"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%17)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%18: !algebra.field_vector<"bls12-381.fr">, %19: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %20 = "exec.collect"(%arg17, %18, %19, %arg21) <{body = @zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body, domain = @zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_domain, site = "s4"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%20)[^bb3, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%21: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %22 = "exec.failed"(%21) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%22) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb3(%23: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb1
      %24 = "exec.apply"(%arg17) <{binding = @zkl_binding_0, parameters = ["1"], site = "s7"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%24)[^bb4, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%25: ui64):  // pred: ^bb3
      %26 = "exec.apply"(%arg17, %arg19, %25) <{binding = @zkl_binding_10, parameters = [], site = "s8"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%26)[^bb5, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%27: ui64):  // pred: ^bb4
      %28 = "exec.returned"(%23, %27, %arg20) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%28) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561729h6669785f6669727374", []]} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, sym_name = "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_domain", sym_visibility = "private"}> ({
    ^bb0(%arg15: !algebra.field_vector<"bls12-381.fr">, %arg16: !algebra.field_vector<"bls12-381.fr">):
      %14 = "data.domain_elements"(%arg15) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %15 = "data.domain_elements"(%arg16) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %16 = "data.domain_zip"(%14, %15) : (!data.domain<!algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%16) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body", sym_visibility = "private"}> ({
    ^bb0(%arg9: !runtime.scope, %arg10: !algebra.field<"bls12-381.fr">, %arg11: !algebra.field<"bls12-381.fr">, %arg12: !algebra.field_vector<"bls12-381.fr">, %arg13: !algebra.field_vector<"bls12-381.fr">, %arg14: !algebra.field<"bls12-381.fr">):
      %9 = "exec.compute"(%arg9, %arg10, %arg11, %arg14) <{callee = @zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5, site = "body"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%9)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%10: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %11 = "exec.returned"(%10) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%11) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%12: !exec.stop):  // pred: ^bb0
      %13 = "exec.failed"(%12) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%13) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5", sym_visibility = "private"}> ({
    ^bb0(%arg6: !algebra.field<"bls12-381.fr">, %arg7: !algebra.field<"bls12-381.fr">, %arg8: !algebra.field<"bls12-381.fr">):
      %6 = "algebra.field_subtract"(%arg7, %arg6) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %7 = "algebra.field_multiply"(%6, %arg8) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %8 = "algebra.field_add"(%arg6, %7) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%8) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", sym_visibility = "private"}> ({
    ^bb0(%arg3: !runtime.scope, %arg4: !algebra.field_vector<"bls12-381.fr">, %arg5: !algebra.field<"bls12-381.fr">):
      %1 = "exec.apply"(%arg3, %arg4, %arg5) <{binding = @zkl_binding_11, parameters = [], site = "s0"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%1)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%2: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %3 = "exec.returned"(%2) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%3) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%4: !exec.stop):  // pred: ^bb0
      %5 = "exec.failed"(%4) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%5) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6310h7072696d6974697665736h766563746f726h617070656e64", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_c36a2d2c6bd38573735fb9b90d1a3848c562d2c1f688234e2b669408e9c9eea9", sym_visibility = "private"}> ({
    ^bb0(%arg0: !runtime.scope, %arg1: !algebra.field_vector<"bls12-381.fr">, %arg2: !algebra.field<"bls12-381.fr">):
      %0 = "exec.returned"(%arg1, %arg2) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%0) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s8h73756d636865636b9h61745f707265666978", []]} : () -> ()
    "relation.declare"() <{formula = @zkf_326ab2331715c62ba21cb6a967c927ba6ad7f7f2da5e84eb0e5de0fc610f26ca, key = "zkl_8c866415d5a42d7cb60d6b39dd52568c20001248a901906f13a3d5d9dd8f74ac", kind = "zkc.language.formula/0", purposes = ["parameter", "parameter", "parameter"], revision = "68f32f59f6f51bf609caa3011d403333e122834ebc8b40f75aa8b71e05b226f9", signature = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1, static_arguments = [], sym_name = "zkl_8c866415d5a42d7cb60d6b39dd52568c20001248a901906f13a3d5d9dd8f74ac"}> : () -> ()
    "relation.declare"() <{formula = @zkf_c51d11bf318ad26bc2fce7b89eec63f85b98f57e91e0e9e6256f84a573b5b6e6, key = "zkl_f03c5af270c09f9d5e832cdb0dc1d71151cebecfaaa08c6cacd997dde03860e9", kind = "zkc.language.formula/0", purposes = ["parameter", "parameter", "parameter", "statement", "statement"], revision = "d03f98f010ae1cb9e5b251d8a51e9642396e316bec6646da5d20d334ec8ee874", signature = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1, static_arguments = [], sym_name = "zkl_f03c5af270c09f9d5e832cdb0dc1d71151cebecfaaa08c6cacd997dde03860e9"}> : () -> ()
  }) {source_declarations = "[[[[\22nominal\22,\22record\22,\22sumcheck::Pending\22,[[\22field\22,\22bls12-381.fr\22]]],\22linear\22,true,[[\22point\22,[\22builtin\22,\22vector\22,[[\22field\22,\22bls12-381.fr\22]]]],[\22value\22,[\22field\22,\22bls12-381.fr\22]]]],[[\22nominal\22,\22record\22,\22zkc::multilinear::Table\22,[[\22field\22,\22bls12-381.fr\22]]],\22ordinary\22,false,[[\22entries\22,[\22builtin\22,\22vector\22,[[\22field\22,\22bls12-381.fr\22]]]],[\22dimensions\22,[\22index\22]],[\22columns\22,[\22index\22]]]]],[[\22zkl_cf3586ba980b617860654dacf2506dd277a78d1dcf5b84bcc6376225e7fe4f45\22,[[\22values\22,[\22builtin\22,\22vector\22,[[\22field\22,\22bls12-381.fr\22]]],[\22role00000000\22],0,1],[\22variables\22,[\22index\22],[\22role00000000\22],1,1],[\22claim\22,[\22field\22,\22bls12-381.fr\22],[\22role00000001\22],2,1],[\22rounds\22,[\22index\22],[\22role00000000\22,\22role00000001\22],3,1]],[[\22point\22,[\22builtin\22,\22vector\22,[[\22field\22,\22bls12-381.fr\22]]],[\22role00000000\22],0,1],[\22residual\22,[\22builtin\22,\22vector\22,[[\22field\22,\22bls12-381.fr\22]]],[\22role00000000\22],1,1],[\22evaluation\22,[\22nominal\22,\22record\22,\22sumcheck::Pending\22,[[\22field\22,\22bls12-381.fr\22]]],[\22role00000001\22],2,2]]],[\22zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d\22,[[\22values\22,[\22nominal\22,\22record\22,\22zkc::multilinear::Table\22,[[\22field\22,\22bls12-381.fr\22]]],[\22role00000000\22],0,3],[\22claim\22,[\22nominal\22,\22record\22,\22sumcheck::Pending\22,[[\22field\22,\22bls12-381.fr\22]]],[\22role00000001\22],3,2],[\22rounds\22,[\22index\22],[\22role00000000\22,\22role00000001\22],5,1]],[[\22point\22,[\22builtin\22,\22vector\22,[[\22field\22,\22bls12-381.fr\22]]],[\22role00000000\22],0,1],[\22residual\22,[\22nominal\22,\22record\22,\22zkc::multilinear::Table\22,[[\22field\22,\22bls12-381.fr\22]]],[\22role00000000\22],1,3],[\22evaluation\22,[\22nominal\22,\22record\22,\22sumcheck::Pending\22,[[\22field\22,\22bls12-381.fr\22]]],[\22role00000001\22],4,2]]]]]"} : () -> ()
}) : () -> ()

