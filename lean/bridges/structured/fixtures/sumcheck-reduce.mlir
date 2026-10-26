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
    ^bb0(%arg102: !algebra.field_vector<"bls12-381.fr">, %arg103: ui64, %arg104: !algebra.field<"bls12-381.fr">, %arg105: ui64, %arg106: !protocol.service_ref<"random.bls12-381.fr/0">):
      %295 = "data.index"() <{value = "1"}> : () -> ui64
      %296:3 = "protocol.local_call"(%arg102, %arg103, %295) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a, role = "role00000000", site = "s1"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      %297:6 = "protocol.apply"(%296#0, %296#1, %296#2, %arg104, %arg105, %arg106) <{callee = @zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d, roles = ["role00000000", "role00000001"], site = "s3"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %298 = "func.call"(%297#1, %297#2, %297#3) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">
      "protocol.return"(%297#0, %298, %297#4, %297#5) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", sym_visibility = "private"}> ({
    ^bb0(%arg98: !runtime.scope, %arg99: !algebra.field_vector<"bls12-381.fr">, %arg100: ui64, %arg101: ui64):
      %276 = "func.call"(%arg98, %arg99, %arg100, %arg101) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655}> {runtime.site = "s0"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%276)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%277: i1):  // pred: ^bb0
      %278 = "exec.test"(%arg98, %277) <{site = "s1"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%278)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%279: !exec.stop):  // 8 preds: ^bb0, ^bb1, ^bb4, ^bb5, ^bb7, ^bb8, ^bb10, ^bb11
      %280 = "exec.failed"(%279) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%280) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb3(%281: i1):  // pred: ^bb1
      "cf.cond_br"(%281)[^bb4, ^bb5] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb4:  // pred: ^bb3
      %282 = "runtime.enter_scope"(%arg98) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%282)[^bb7, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb5:  // pred: ^bb3
      %283 = "runtime.enter_scope"(%arg98) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%283)[^bb10, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // 2 preds: ^bb9, ^bb12
      %284 = "exec.returned"(%arg99, %arg100, %arg101) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%284) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb7(%285: !runtime.scope):  // pred: ^bb4
      %286 = "func.call"(%285) <{callee = @zkl_control_0}> : (!runtime.scope) -> !exec.outcome<>
      %287 = "runtime.exit_scope"(%285, %286) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%287)[^bb8, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb8(%288: !runtime.transfer<>):  // pred: ^bb7
      %289 = "runtime.accept_transfer"(%arg98, %288) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%289)[^bb9, ^bb2] : (!exec.outcome<>) -> ()
    ^bb9:  // pred: ^bb8
      "cf.br"()[^bb6] : () -> ()
    ^bb10(%290: !runtime.scope):  // pred: ^bb5
      %291 = "func.call"(%290) <{callee = @zkl_control_1}> : (!runtime.scope) -> !exec.outcome<>
      %292 = "runtime.exit_scope"(%290, %291) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%292)[^bb11, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb11(%293: !runtime.transfer<>):  // pred: ^bb10
      %294 = "runtime.accept_transfer"(%arg98, %293) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%294)[^bb12, ^bb2] : (!exec.outcome<>) -> ()
    ^bb12:  // pred: ^bb11
      "cf.br"()[^bb6] : () -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561725h7461626c65", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_0", sym_visibility = "private"}> ({
    ^bb0(%arg97: !runtime.scope):
      %275 = "exec.complete"(%arg97) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%275) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_1", sym_visibility = "private"}> ({
    ^bb0(%arg96: !runtime.scope):
      %272 = "exec.reject"(%arg96) <{reason = "reject", site = "s1_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%272)[^bb1] : (!exec.stop) -> ()
    ^bb1(%273: !exec.stop):  // pred: ^bb0
      %274 = "exec.failed"(%273) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%274) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", sym_visibility = "private"}> ({
    ^bb0(%arg92: !runtime.scope, %arg93: !algebra.field_vector<"bls12-381.fr">, %arg94: ui64, %arg95: ui64):
      %214 = "exec.apply"(%arg92) <{binding = @zkl_binding_0, parameters = ["0"], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%214)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%215: ui64):  // pred: ^bb0
      %216 = "func.call"(%arg92, %215, %arg95) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s1"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%216)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%217: !exec.stop):  // 23 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12, ^bb15, ^bb16, ^bb17, ^bb18, ^bb19, ^bb21, ^bb22, ^bb25, ^bb26, ^bb28, ^bb29, ^bb31, ^bb32
      %218 = "exec.failed"(%217) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%218) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%219: i1):  // pred: ^bb1
      %220 = "exec.test"(%arg92, %219) <{site = "s3"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%220)[^bb4, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb4(%221: i1):  // pred: ^bb3
      "cf.cond_br"(%221)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %222 = "runtime.enter_scope"(%arg92, %arg94) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "then", site = "s3"}> : (!runtime.scope, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%222)[^bb8, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %223 = "runtime.enter_scope"(%arg92, %arg94) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "else", site = "s3"}> : (!runtime.scope, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%223)[^bb11, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7(%224: i1):  // 2 preds: ^bb10, ^bb13
      %225 = "exec.test"(%arg92, %224) <{site = "s11"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%225)[^bb14, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb8(%226: !runtime.scope):  // pred: ^bb5
      %227 = "func.call"(%226, %arg94) <{callee = @zkl_control_2}> : (!runtime.scope, ui64) -> !exec.outcome<(i1)>
      %228 = "runtime.exit_scope"(%226, %227) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%228)[^bb9, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb9(%229: !runtime.transfer<(i1)>):  // pred: ^bb8
      %230 = "runtime.accept_transfer"(%arg92, %229) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%230)[^bb10, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb10(%231: i1):  // pred: ^bb9
      "cf.br"(%231)[^bb7] : (i1) -> ()
    ^bb11(%232: !runtime.scope):  // pred: ^bb6
      %233 = "func.call"(%232, %arg94) <{callee = @zkl_control_3}> : (!runtime.scope, ui64) -> !exec.outcome<(i1)>
      %234 = "runtime.exit_scope"(%232, %233) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%234)[^bb12, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb12(%235: !runtime.transfer<(i1)>):  // pred: ^bb11
      %236 = "runtime.accept_transfer"(%arg92, %235) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%236)[^bb13, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb13(%237: i1):  // pred: ^bb12
      "cf.br"(%237)[^bb7] : (i1) -> ()
    ^bb14(%238: i1):  // pred: ^bb7
      "cf.cond_br"(%238)[^bb15, ^bb16] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb15:  // pred: ^bb14
      %239 = "runtime.enter_scope"(%arg92, %arg93, %arg95) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "then", site = "s11"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%239)[^bb18, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb16:  // pred: ^bb14
      %240 = "runtime.enter_scope"(%arg92, %arg93, %arg95) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "else", site = "s11"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%240)[^bb21, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb17(%241: i1):  // 2 preds: ^bb20, ^bb23
      %242 = "exec.test"(%arg92, %241) <{site = "s22"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%242)[^bb24, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb18(%243: !runtime.scope):  // pred: ^bb15
      %244 = "func.call"(%243, %arg93, %arg95) <{callee = @zkl_control_4}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>
      %245 = "runtime.exit_scope"(%243, %244) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%245)[^bb19, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb19(%246: !runtime.transfer<(i1)>):  // pred: ^bb18
      %247 = "runtime.accept_transfer"(%arg92, %246) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%247)[^bb20, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb20(%248: i1):  // pred: ^bb19
      "cf.br"(%248)[^bb17] : (i1) -> ()
    ^bb21(%249: !runtime.scope):  // pred: ^bb16
      %250 = "func.call"(%249, %arg93, %arg95) <{callee = @zkl_control_5}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>
      %251 = "runtime.exit_scope"(%249, %250) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%251)[^bb22, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb22(%252: !runtime.transfer<(i1)>):  // pred: ^bb21
      %253 = "runtime.accept_transfer"(%arg92, %252) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%253)[^bb23, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb23(%254: i1):  // pred: ^bb22
      "cf.br"(%254)[^bb17] : (i1) -> ()
    ^bb24(%255: i1):  // pred: ^bb17
      "cf.cond_br"(%255)[^bb25, ^bb26] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb25:  // pred: ^bb24
      %256 = "runtime.enter_scope"(%arg92, %arg93, %arg94, %arg95) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "then", site = "s22"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%256)[^bb28, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb26:  // pred: ^bb24
      %257 = "runtime.enter_scope"(%arg92, %arg93, %arg94, %arg95) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "else", site = "s22"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%257)[^bb31, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb27(%258: i1):  // 2 preds: ^bb30, ^bb33
      %259 = "exec.returned"(%258) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%259) : (!exec.outcome<(i1)>) -> ()
    ^bb28(%260: !runtime.scope):  // pred: ^bb25
      %261 = "func.call"(%260, %arg93, %arg94, %arg95) <{callee = @zkl_control_6}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      %262 = "runtime.exit_scope"(%260, %261) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%262)[^bb29, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb29(%263: !runtime.transfer<(i1)>):  // pred: ^bb28
      %264 = "runtime.accept_transfer"(%arg92, %263) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%264)[^bb30, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb30(%265: i1):  // pred: ^bb29
      "cf.br"(%265)[^bb27] : (i1) -> ()
    ^bb31(%266: !runtime.scope):  // pred: ^bb26
      %267 = "func.call"(%266, %arg93, %arg94, %arg95) <{callee = @zkl_control_7}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      %268 = "runtime.exit_scope"(%266, %267) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%268)[^bb32, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb32(%269: !runtime.transfer<(i1)>):  // pred: ^bb31
      %270 = "runtime.accept_transfer"(%arg92, %269) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%270)[^bb33, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb33(%271: i1):  // pred: ^bb32
      "cf.br"(%271)[^bb27] : (i1) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_2", sym_visibility = "private"}> ({
    ^bb0(%arg90: !runtime.scope, %arg91: ui64):
      %207 = "exec.apply"(%arg90) <{binding = @zkl_binding_0, parameters = ["64"], site = "s4"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%207)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%208: ui64):  // pred: ^bb0
      %209 = "func.call"(%arg90, %arg91, %208) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s5"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%209)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%210: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %211 = "exec.failed"(%210) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%211) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%212: i1):  // pred: ^bb1
      %213 = "exec.complete"(%arg90, %212) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%213) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_3", sym_visibility = "private"}> ({
    ^bb0(%arg88: !runtime.scope, %arg89: ui64):
      %202 = "exec.boolean"(%arg88) <{site = "s7", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%202)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%203: i1):  // pred: ^bb0
      %204 = "exec.complete"(%arg88, %203) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%204) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%205: !exec.stop):  // pred: ^bb0
      %206 = "exec.failed"(%205) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%206) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_4", sym_visibility = "private"}> ({
    ^bb0(%arg85: !runtime.scope, %arg86: !algebra.field_vector<"bls12-381.fr">, %arg87: ui64):
      %191 = "exec.apply"(%arg85, %arg86) <{binding = @zkl_binding_1, parameters = [], site = "s12"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%191)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%192: ui64):  // pred: ^bb0
      %193 = "exec.apply"(%arg85, %192, %arg87) <{binding = @zkl_binding_2, parameters = [], site = "s13"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%193)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%194: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %195 = "exec.failed"(%194) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%195) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%196: ui64):  // pred: ^bb1
      %197 = "exec.apply"(%arg85) <{binding = @zkl_binding_0, parameters = ["0"], site = "s14"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%197)[^bb4, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%198: ui64):  // pred: ^bb3
      %199 = "exec.apply"(%arg85, %196, %198) <{binding = @zkl_binding_3, parameters = [], site = "s15"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%199)[^bb5, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb5(%200: i1):  // pred: ^bb4
      %201 = "exec.complete"(%arg85, %200) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%201) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_5", sym_visibility = "private"}> ({
    ^bb0(%arg82: !runtime.scope, %arg83: !algebra.field_vector<"bls12-381.fr">, %arg84: ui64):
      %186 = "exec.boolean"(%arg82) <{site = "s17", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%186)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%187: i1):  // pred: ^bb0
      %188 = "exec.complete"(%arg82, %187) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%188) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%189: !exec.stop):  // pred: ^bb0
      %190 = "exec.failed"(%189) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%190) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_6", sym_visibility = "private"}> ({
    ^bb0(%arg78: !runtime.scope, %arg79: !algebra.field_vector<"bls12-381.fr">, %arg80: ui64, %arg81: ui64):
      %175 = "exec.apply"(%arg78, %arg79) <{binding = @zkl_binding_1, parameters = [], site = "s23"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%175)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%176: ui64):  // pred: ^bb0
      %177 = "exec.apply"(%arg78, %176, %arg81) <{binding = @zkl_binding_4, parameters = [], site = "s24"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%177)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%178: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %179 = "exec.failed"(%178) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%179) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%180: ui64):  // pred: ^bb1
      %181 = "func.call"(%arg78, %arg80) <{callee = @s3h7a6b6311h6d756c74696c696e6561724h726f7773}> {runtime.site = "s25"} : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%181)[^bb4, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%182: ui64):  // pred: ^bb3
      %183 = "exec.apply"(%arg78, %180, %182) <{binding = @zkl_binding_3, parameters = [], site = "s26"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%183)[^bb5, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb5(%184: i1):  // pred: ^bb4
      %185 = "exec.complete"(%arg78, %184) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%185) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_7", sym_visibility = "private"}> ({
    ^bb0(%arg74: !runtime.scope, %arg75: !algebra.field_vector<"bls12-381.fr">, %arg76: ui64, %arg77: ui64):
      %170 = "exec.boolean"(%arg74) <{site = "s28", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%170)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%171: i1):  // pred: ^bb0
      %172 = "exec.complete"(%arg74, %171) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%172) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%173: !exec.stop):  // pred: ^bb0
      %174 = "exec.failed"(%173) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%174) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "s3h7a6b637h696e64696365734h6c657373", sym_visibility = "private"}> ({
    ^bb0(%arg71: !runtime.scope, %arg72: ui64, %arg73: ui64):
      %165 = "exec.apply"(%arg71, %arg72, %arg73) <{binding = @zkl_binding_5, parameters = [], site = "s0"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%165)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%166: i1):  // pred: ^bb0
      %167 = "exec.returned"(%166) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%167) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%168: !exec.stop):  // pred: ^bb0
      %169 = "exec.failed"(%168) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%169) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.origin = ["s3h7a6b637h696e64696365734h6c657373", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "s3h7a6b6311h6d756c74696c696e6561724h726f7773", sym_visibility = "private"}> ({
    ^bb0(%arg69: !runtime.scope, %arg70: ui64):
      %118 = "exec.apply"(%arg69) <{binding = @zkl_binding_0, parameters = ["64"], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%118)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%119: ui64):  // pred: ^bb0
      %120 = "func.call"(%arg69, %arg70, %119) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s1"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%120)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%121: !exec.stop):  // 14 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12, ^bb14, ^bb15, ^bb19, ^bb21
      %122 = "exec.failed"(%121) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%122) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%123: i1):  // pred: ^bb1
      %124 = "exec.test"(%arg69, %123) <{site = "s2"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%124)[^bb4, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb4(%125: i1):  // pred: ^bb3
      "cf.cond_br"(%125)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %126 = "runtime.enter_scope"(%arg69) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s2"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%126)[^bb8, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %127 = "runtime.enter_scope"(%arg69) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s2"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%127)[^bb11, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // 2 preds: ^bb10, ^bb13
      %128 = "exec.apply"(%arg69) <{binding = @zkl_binding_0, parameters = ["1"], site = "s3"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%128)[^bb14, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb8(%129: !runtime.scope):  // pred: ^bb5
      %130 = "func.call"(%129) <{callee = @zkl_control_8}> : (!runtime.scope) -> !exec.outcome<>
      %131 = "runtime.exit_scope"(%129, %130) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%131)[^bb9, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb9(%132: !runtime.transfer<>):  // pred: ^bb8
      %133 = "runtime.accept_transfer"(%arg69, %132) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%133)[^bb10, ^bb2] : (!exec.outcome<>) -> ()
    ^bb10:  // pred: ^bb9
      "cf.br"()[^bb7] : () -> ()
    ^bb11(%134: !runtime.scope):  // pred: ^bb6
      %135 = "func.call"(%134) <{callee = @zkl_control_9}> : (!runtime.scope) -> !exec.outcome<>
      %136 = "runtime.exit_scope"(%134, %135) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%136)[^bb12, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb12(%137: !runtime.transfer<>):  // pred: ^bb11
      %138 = "runtime.accept_transfer"(%arg69, %137) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%138)[^bb13, ^bb2] : (!exec.outcome<>) -> ()
    ^bb13:  // pred: ^bb12
      "cf.br"()[^bb7] : () -> ()
    ^bb14(%139: ui64):  // pred: ^bb7
      %140 = "exec.apply"(%arg69) <{binding = @zkl_binding_0, parameters = ["0"], site = "s5"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%140)[^bb15, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb15(%141: ui64):  // pred: ^bb14
      %142 = "exec.range"(%arg69, %141, %arg70) <{site = "s6"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%142)[^bb16, ^bb2] : (!exec.outcome<(i64, i64)>) -> ()
    ^bb16(%143: i64, %144: i64):  // pred: ^bb15
      %145 = "runtime.borrow_transfer"(%arg69, %139) : (!runtime.scope, ui64) -> !runtime.transfer<(ui64)>
      "cf.br"(%143, %145)[^bb17] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb17(%146: i64, %147: !runtime.transfer<(ui64)>):  // 2 preds: ^bb16, ^bb20
      %148 = "arith.cmpi"(%146, %144) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%148, %147)[^bb18, ^bb19] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(ui64)>) -> ()
    ^bb18:  // pred: ^bb17
      %149 = "runtime.iteration"(%arg69, %146) <{site = "s6"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%149)[^bb22, ^bb21] : (!exec.outcome<(ui64)>) -> ()
    ^bb19(%150: !runtime.transfer<(ui64)>):  // pred: ^bb17
      %151 = "runtime.accept_transfer"(%arg69, %150) : (!runtime.scope, !runtime.transfer<(ui64)>) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%151)[^bb25, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb20(%152: !runtime.transfer<(ui64)>):  // pred: ^bb24
      %153 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %154 = "arith.addi"(%146, %153) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%154, %152)[^bb17] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb21(%155: !exec.stop):  // 3 preds: ^bb18, ^bb22, ^bb23
      "runtime.release_transfer"(%147) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%155)[^bb2] : (!exec.stop) -> ()
    ^bb22(%156: ui64):  // pred: ^bb18
      %157 = "runtime.transfer_values"(%147) : (!runtime.transfer<(ui64)>) -> ui64
      %158 = "runtime.enter_scope"(%arg69, %146, %156, %157) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 2>, site = "s6"}> : (!runtime.scope, i64, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%158)[^bb23, ^bb21] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb23(%159: !runtime.scope):  // pred: ^bb22
      %160 = "func.call"(%159, %156, %157) <{callee = @zkl_control_10}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      %161 = "runtime.exit_scope"(%159, %160) : (!runtime.scope, !exec.outcome<(ui64)>) -> !exec.outcome<(!runtime.transfer<(ui64)>)>
      "exec.dispatch"(%161)[^bb24, ^bb21] : (!exec.outcome<(!runtime.transfer<(ui64)>)>) -> ()
    ^bb24(%162: !runtime.transfer<(ui64)>):  // pred: ^bb23
      "runtime.release_transfer"(%147) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%162)[^bb20] : (!runtime.transfer<(ui64)>) -> ()
    ^bb25(%163: ui64):  // pred: ^bb19
      %164 = "exec.returned"(%163) : (ui64) -> !exec.outcome<(ui64)>
      "func.return"(%164) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561724h726f7773", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_8", sym_visibility = "private"}> ({
    ^bb0(%arg68: !runtime.scope):
      %117 = "exec.complete"(%arg68) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%117) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_9", sym_visibility = "private"}> ({
    ^bb0(%arg67: !runtime.scope):
      %114 = "exec.reject"(%arg67) <{reason = "reject", site = "s2_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%114)[^bb1] : (!exec.stop) -> ()
    ^bb1(%115: !exec.stop):  // pred: ^bb0
      %116 = "exec.failed"(%115) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%116) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "zkl_control_10", sym_visibility = "private"}> ({
    ^bb0(%arg64: !runtime.scope, %arg65: ui64, %arg66: ui64):
      %107 = "exec.apply"(%arg64) <{binding = @zkl_binding_0, parameters = ["2"], site = "s7"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%107)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%108: ui64):  // pred: ^bb0
      %109 = "exec.apply"(%arg64, %arg66, %108) <{binding = @zkl_binding_6, parameters = [], site = "s8"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%109)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%110: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %111 = "exec.failed"(%110) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%111) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%112: ui64):  // pred: ^bb1
      %113 = "exec.complete"(%arg64, %112) : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "func.return"(%113) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.region} : () -> ()
    "protocol.func"() <{contracts = [["input", "initial_sum", [@zkl_11c80248216cbe579879aabc5c6f64d5f465a4db68261d6da29eab7c94d7679c, [["input", 0, "role00000000"], ["input", 1, "role00000000"], ["input", 2, "role00000000"], ["input", 3, "role00000001"]]], unit, unit]], function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">, ui64, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), input_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000000", "role00000001"], ["role00000001"]], origin = ["sumcheck::Reduce", [["F", ["field", "bls12-381.fr"]], ["Max", ["nat", "4"]]]], output_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d"}> ({
    ^bb0(%arg50: !algebra.field_vector<"bls12-381.fr">, %arg51: ui64, %arg52: ui64, %arg53: !algebra.field<"bls12-381.fr">, %arg54: ui64, %arg55: !protocol.service_ref<"random.bls12-381.fr/0">):
      %79 = "func.call"(%arg50, %arg51, %arg52) <{callee = @zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %80 = "data.index"() <{value = "1"}> : () -> ui64
      %81 = "data.index_equal"(%79, %80) : (ui64, ui64) -> i1
      "protocol.guard"(%81) <{owner = "role00000000", site = "s3"}> : (i1) -> ()
      %82 = "func.call"(%arg50, %arg51, %arg52) <{callee = @zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64
      %83 = "protocol.local_call"(%82, %arg54) <{callee = @s3h7a6b637h696e64696365734h6c657373, role = "role00000000", site = "s5"}> : (ui64, ui64) -> i1
      %84 = "arith.constant"() <{value = false}> : () -> i1
      %85 = "arith.cmpi"(%83, %84) <{predicate = 0 : i64}> : (i1, i1) -> i1
      "protocol.guard"(%85) <{owner = "role00000000", site = "s8"}> : (i1) -> ()
      %86 = "protocol.local_call"() <{callee = @zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f, role = "role00000000", site = "s10"}> : () -> !algebra.field_vector<"bls12-381.fr">
      %87 = "protocol.local_call"() <{callee = @zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f, role = "role00000001", site = "s12"}> : () -> !algebra.field_vector<"bls12-381.fr">
      %88:6 = "protocol.repeat"(%arg54, %arg50, %arg51, %arg52, %86, %87, %arg53, %arg55) <{carried = 6 : i64, carried_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000001"], ["role00000001"]], maximum = 4 : i64, roles = ["role00000000", "role00000001"], site = "s15"}> ({
      ^bb0(%arg56: ui64, %arg57: !algebra.field_vector<"bls12-381.fr">, %arg58: ui64, %arg59: ui64, %arg60: !algebra.field_vector<"bls12-381.fr">, %arg61: !algebra.field_vector<"bls12-381.fr">, %arg62: !algebra.field<"bls12-381.fr">, %arg63: !protocol.service_ref<"random.bls12-381.fr/0">):
        %89:2 = "protocol.local_call"(%arg57, %arg58, %arg59) <{callee = @zkl_532a609cf36a935835501ca51308940142121e647ca360843a880bf231f04aa6, role = "role00000000", site = "s16"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        %90 = "protocol.exchange"(%89#0) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %91 = "protocol.restrict_roles"(%90) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %92 = "protocol.exchange"(%89#1) <{receiver = "role00000001", sender = "role00000000", site = "label_726f756e64_1"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %93 = "protocol.restrict_roles"(%92) <{roles = ["role00000001"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %94 = "algebra.field_add"(%91, %93) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %95 = "algebra.field_equal"(%arg62, %94) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
        "protocol.guard"(%95) <{owner = "role00000001", site = "s24"}> : (i1) -> ()
        %96 = "protocol.query"(%arg63) <{method = "draw", owner = "role00000001", site = "label_6368616c6c656e6765"}> : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
        %97 = "protocol.exchange"(%96) <{receiver = "role00000000", sender = "role00000001", site = "label_64656c6976657279_0"}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %98 = "protocol.restrict_roles"(%97) <{roles = ["role00000000"]}> : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %99:3 = "protocol.local_call"(%arg57, %arg58, %arg59, %98) <{callee = @zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d, role = "role00000000", site = "s29"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
        %100 = "protocol.local_call"(%arg60, %98) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000000", site = "s31"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
        %101 = "protocol.local_call"(%arg61, %96) <{callee = @zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d, role = "role00000001", site = "s33"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
        %102 = "algebra.constant"() <{value = "1"}> : () -> !algebra.field<"bls12-381.fr">
        %103 = "algebra.field_subtract"(%102, %96) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %104 = "algebra.field_multiply"(%103, %91) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %105 = "algebra.field_multiply"(%96, %93) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        %106 = "algebra.field_add"(%104, %105) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
        "protocol.yield"(%99#0, %99#1, %99#2, %100, %101, %106) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
      }) : (ui64, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      "protocol.return"(%88#3, %88#0, %88#1, %88#2, %88#4, %88#5) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "zkf_654a0e58b11e83f398996b9e830df00890bec0f8dc08a65c5750d6d9c759b643", sym_visibility = "private"}> ({
    ^bb0(%arg46: !algebra.field_vector<"bls12-381.fr">, %arg47: ui64, %arg48: ui64, %arg49: !algebra.field<"bls12-381.fr">):
      %76 = "func.call"(%arg46, %arg47, %arg48) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">
      %77 = "func.call"(%76) <{callee = @zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e}> : (!algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %78 = "algebra.field_equal"(%arg49, %77) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      "func.return"(%78) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">, sym_name = "zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", sym_visibility = "private"}> ({
    ^bb0(%arg43: !algebra.field_vector<"bls12-381.fr">, %arg44: ui64, %arg45: ui64):
      "func.return"(%arg43) : (!algebra.field_vector<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e", sym_visibility = "private"}> ({
    ^bb0(%arg42: !algebra.field_vector<"bls12-381.fr">):
      %74 = "algebra.constant"() <{value = "0"}> : () -> !algebra.field<"bls12-381.fr">
      %75 = "algebra.finite_fold"(%arg42, %74) <{domain = @finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_domain, step = @finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_body}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%75) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>, sym_name = "finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_domain", sym_visibility = "private"}> ({
    ^bb0(%arg41: !algebra.field_vector<"bls12-381.fr">):
      %73 = "data.domain_elements"(%arg41) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%73) : (!data.domain<!algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_body", sym_visibility = "private"}> ({
    ^bb0(%arg38: !algebra.field<"bls12-381.fr">, %arg39: !algebra.field<"bls12-381.fr">, %arg40: !algebra.field_vector<"bls12-381.fr">):
      %72 = "func.call"(%arg38, %arg39) <{callee = @zkl_3fc17a64a5bb6e75192d0a1362e9954f0d434a10d0f93e319db6b516835a1005}> : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%72) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_3fc17a64a5bb6e75192d0a1362e9954f0d434a10d0f93e319db6b516835a1005", sym_visibility = "private"}> ({
    ^bb0(%arg36: !algebra.field<"bls12-381.fr">, %arg37: !algebra.field<"bls12-381.fr">):
      %71 = "algebra.field_add"(%arg36, %arg37) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%71) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64, sym_name = "zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275", sym_visibility = "private"}> ({
    ^bb0(%arg33: !algebra.field_vector<"bls12-381.fr">, %arg34: ui64, %arg35: ui64):
      "func.return"(%arg35) : (ui64) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ui64, sym_name = "zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94", sym_visibility = "private"}> ({
    ^bb0(%arg30: !algebra.field_vector<"bls12-381.fr">, %arg31: ui64, %arg32: ui64):
      "func.return"(%arg31) : (ui64) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", sym_visibility = "private"}> ({
    ^bb0(%arg29: !runtime.scope):
      %66 = "exec.apply"(%arg29) <{binding = @zkl_binding_7, parameters = [], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%66)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%67: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %68 = "exec.returned"(%67) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%68) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%69: !exec.stop):  // pred: ^bb0
      %70 = "exec.failed"(%69) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%70) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6310h7072696d6974697665736h766563746f725h656d707479", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_532a609cf36a935835501ca51308940142121e647ca360843a880bf231f04aa6", sym_visibility = "private"}> ({
    ^bb0(%arg25: !runtime.scope, %arg26: !algebra.field_vector<"bls12-381.fr">, %arg27: ui64, %arg28: ui64):
      %56 = "func.call"(%arg25, %arg26, %arg27, %arg28) <{callee = @zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087}> {runtime.site = "s0"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%56)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%57: !algebra.field_vector<"bls12-381.fr">, %58: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %59 = "exec.apply"(%arg25, %57) <{binding = @zkl_binding_8, parameters = [], site = "s3"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%59)[^bb3, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%60: !exec.stop):  // 3 preds: ^bb0, ^bb1, ^bb3
      %61 = "exec.failed"(%60) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%61) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb3(%62: !algebra.field<"bls12-381.fr">):  // pred: ^bb1
      %63 = "exec.apply"(%arg25, %58) <{binding = @zkl_binding_8, parameters = [], site = "s5"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%63)[^bb4, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb4(%64: !algebra.field<"bls12-381.fr">):  // pred: ^bb3
      %65 = "exec.returned"(%62, %64) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "func.return"(%65) : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s8h73756d636865636b4h73756d73", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087", sym_visibility = "private"}> ({
    ^bb0(%arg21: !runtime.scope, %arg22: !algebra.field_vector<"bls12-381.fr">, %arg23: ui64, %arg24: ui64):
      %32 = "exec.apply"(%arg21) <{binding = @zkl_binding_0, parameters = ["0"], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%32)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%33: ui64):  // pred: ^bb0
      %34 = "func.call"(%arg21, %33, %arg23) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s2"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%34)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%35: !exec.stop):  // 10 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12
      %36 = "exec.failed"(%35) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%36) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%37: i1):  // pred: ^bb1
      %38 = "exec.test"(%arg21, %37) <{site = "s3"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%38)[^bb4, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb4(%39: i1):  // pred: ^bb3
      "cf.cond_br"(%39)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %40 = "runtime.enter_scope"(%arg21) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s3"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%40)[^bb8, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %41 = "runtime.enter_scope"(%arg21) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s3"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%41)[^bb11, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // 2 preds: ^bb10, ^bb13
      %42 = "exec.apply"(%arg21, %arg22) <{binding = @zkl_binding_9, parameters = [], site = "s5"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%42)[^bb14, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%43: !runtime.scope):  // pred: ^bb5
      %44 = "func.call"(%43) <{callee = @zkl_control_11}> : (!runtime.scope) -> !exec.outcome<>
      %45 = "runtime.exit_scope"(%43, %44) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%45)[^bb9, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb9(%46: !runtime.transfer<>):  // pred: ^bb8
      %47 = "runtime.accept_transfer"(%arg21, %46) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%47)[^bb10, ^bb2] : (!exec.outcome<>) -> ()
    ^bb10:  // pred: ^bb9
      "cf.br"()[^bb7] : () -> ()
    ^bb11(%48: !runtime.scope):  // pred: ^bb6
      %49 = "func.call"(%48) <{callee = @zkl_control_12}> : (!runtime.scope) -> !exec.outcome<>
      %50 = "runtime.exit_scope"(%48, %49) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%50)[^bb12, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb12(%51: !runtime.transfer<>):  // pred: ^bb11
      %52 = "runtime.accept_transfer"(%arg21, %51) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%52)[^bb13, ^bb2] : (!exec.outcome<>) -> ()
    ^bb13:  // pred: ^bb12
      "cf.br"()[^bb7] : () -> ()
    ^bb14(%53: !algebra.field_vector<"bls12-381.fr">, %54: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb7
      %55 = "exec.returned"(%53, %54) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%55) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561726h68616c766573", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_11", sym_visibility = "private"}> ({
    ^bb0(%arg20: !runtime.scope):
      %31 = "exec.complete"(%arg20) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%31) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_12", sym_visibility = "private"}> ({
    ^bb0(%arg19: !runtime.scope):
      %28 = "exec.reject"(%arg19) <{reason = "reject", site = "s3_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%28)[^bb1] : (!exec.stop) -> ()
    ^bb1(%29: !exec.stop):  // pred: ^bb0
      %30 = "exec.failed"(%29) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%30) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d", sym_visibility = "private"}> ({
    ^bb0(%arg14: !runtime.scope, %arg15: !algebra.field_vector<"bls12-381.fr">, %arg16: ui64, %arg17: ui64, %arg18: !algebra.field<"bls12-381.fr">):
      %16 = "func.call"(%arg14, %arg15, %arg16, %arg17) <{callee = @zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087}> {runtime.site = "s0"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%16)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%17: !algebra.field_vector<"bls12-381.fr">, %18: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %19 = "exec.collect"(%arg14, %17, %18, %arg18) <{body = @zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body, domain = @zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_domain, site = "s4"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%19)[^bb3, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%20: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %21 = "exec.failed"(%20) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%21) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb3(%22: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb1
      %23 = "exec.apply"(%arg14) <{binding = @zkl_binding_0, parameters = ["1"], site = "s7"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%23)[^bb4, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%24: ui64):  // pred: ^bb3
      %25 = "exec.apply"(%arg14, %arg16, %24) <{binding = @zkl_binding_10, parameters = [], site = "s8"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%25)[^bb5, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%26: ui64):  // pred: ^bb4
      %27 = "exec.returned"(%22, %26, %arg17) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%27) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561729h6669785f6669727374", []]} : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>, sym_name = "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_domain", sym_visibility = "private"}> ({
    ^bb0(%arg12: !algebra.field_vector<"bls12-381.fr">, %arg13: !algebra.field_vector<"bls12-381.fr">):
      %13 = "data.domain_elements"(%arg12) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %14 = "data.domain_elements"(%arg13) : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<!algebra.field<"bls12-381.fr">>
      %15 = "data.domain_zip"(%13, %14) : (!data.domain<!algebra.field<"bls12-381.fr">>, !data.domain<!algebra.field<"bls12-381.fr">>) -> !data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>
      "data.domain_yield"(%15) : (!data.domain<!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">>) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, no_inline, sym_name = "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body", sym_visibility = "private"}> ({
    ^bb0(%arg6: !runtime.scope, %arg7: !algebra.field<"bls12-381.fr">, %arg8: !algebra.field<"bls12-381.fr">, %arg9: !algebra.field_vector<"bls12-381.fr">, %arg10: !algebra.field_vector<"bls12-381.fr">, %arg11: !algebra.field<"bls12-381.fr">):
      %8 = "exec.compute"(%arg6, %arg7, %arg8, %arg11) <{callee = @zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5, site = "body"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%8)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%9: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %10 = "exec.returned"(%9) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%10) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%11: !exec.stop):  // pred: ^bb0
      %12 = "exec.failed"(%11) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "func.return"(%12) : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, sym_name = "zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5", sym_visibility = "private"}> ({
    ^bb0(%arg3: !algebra.field<"bls12-381.fr">, %arg4: !algebra.field<"bls12-381.fr">, %arg5: !algebra.field<"bls12-381.fr">):
      %5 = "algebra.field_subtract"(%arg4, %arg3) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %6 = "algebra.field_multiply"(%5, %arg5) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %7 = "algebra.field_add"(%arg3, %6) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "func.return"(%7) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", sym_visibility = "private"}> ({
    ^bb0(%arg0: !runtime.scope, %arg1: !algebra.field_vector<"bls12-381.fr">, %arg2: !algebra.field<"bls12-381.fr">):
      %0 = "exec.apply"(%arg0, %arg1, %arg2) <{binding = @zkl_binding_11, parameters = [], site = "s0"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%1: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%2) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%4) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6310h7072696d6974697665736h766563746f726h617070656e64", []]} : () -> ()
    "relation.declare"() <{formula = @zkf_654a0e58b11e83f398996b9e830df00890bec0f8dc08a65c5750d6d9c759b643, key = "zkl_11c80248216cbe579879aabc5c6f64d5f465a4db68261d6da29eab7c94d7679c", kind = "zkc.language.formula/0", purposes = ["parameter", "parameter", "parameter", "statement"], revision = "2c4b933d7a6995f34b80f29d1478e98e81ee53f22c19789c1c06958fba515a0f", signature = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, !algebra.field<"bls12-381.fr">) -> i1, sym_name = "zkl_11c80248216cbe579879aabc5c6f64d5f465a4db68261d6da29eab7c94d7679c"}> : () -> ()
  }) : () -> ()
}) : () -> ()

