// Exact encoded-word hash transitions. This is a transcript consistency client.
!words = !algebra.indices
!rounds = !data.sequence<!words>
module { "protocol.module"() ({
 "runtime.binding"() {sym_name="constant",contract="index.constant",arguments=[],implementation="",function_type=(!runtime.scope) -> !exec.outcome<(ui64)>} : ()->()
 "runtime.binding"() {sym_name="length",contract="indices.length",arguments=[],implementation="",function_type=(!runtime.scope, !algebra.indices) -> !exec.outcome<(ui64)>} : ()->()
 "runtime.binding"() {sym_name="at",contract="indices.at",arguments=[],implementation="",function_type=(!runtime.scope, !algebra.indices, ui64) -> !exec.outcome<(ui64)>} : ()->()
 "runtime.binding"() {sym_name="equal",contract="index.equal",arguments=[],implementation="",function_type=(!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>} : ()->()
 "runtime.binding"() {sym_name="and",contract="bool.and",arguments=[],implementation="",function_type=(!runtime.scope, i1, i1) -> !exec.outcome<(i1)>} : ()->()
    func.func @same(%arg0: !runtime.scope, %arg1: !words, %arg2: !words) -> !exec.outcome<(i1)> attributes {no_inline, runtime.origin = ["same", []]} {
      %0 = "exec.apply"(%arg0, %arg1) <{binding = @length, parameters = [], site = "n"}> : (!runtime.scope, !words) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1: ui64):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %arg2) <{binding = @length, parameters = [], site = "m"}> : (!runtime.scope, !words) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%3: !exec.stop):  // 10 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb6, ^bb7, ^bb9, ^bb10, ^bb12, ^bb13
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(i1)>
      return %4 : !exec.outcome<(i1)>
    ^bb3(%5: ui64):  // pred: ^bb1
      %6 = "exec.apply"(%arg0, %1, %5) <{binding = @equal, parameters = [], site = "lengths"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb4(%7: i1):  // pred: ^bb3
      %8 = "exec.test"(%arg0, %7) <{site = "compare"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%8)[^bb5, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb5(%9: i1):  // pred: ^bb4
      cf.cond_br %9, ^bb6, ^bb7
    ^bb6:  // pred: ^bb5
      %10 = "runtime.enter_scope"(%arg0, %arg1, %arg2, %1) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "then", site = "compare"}> : (!runtime.scope, !words, !words, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%10)[^bb9, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // pred: ^bb5
      %11 = "runtime.enter_scope"(%arg0, %arg1, %arg2, %1) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "else", site = "compare"}> : (!runtime.scope, !words, !words, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%11)[^bb12, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb8(%12: i1):  // 2 preds: ^bb11, ^bb14
      %13 = "exec.returned"(%12) : (i1) -> !exec.outcome<(i1)>
      return %13 : !exec.outcome<(i1)>
    ^bb9(%14: !runtime.scope):  // pred: ^bb6
      %15 = call @control_0(%14, %arg1, %arg2, %1) : (!runtime.scope, !words, !words, ui64) -> !exec.outcome<(i1)>
      %16 = "runtime.exit_scope"(%14, %15) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%16)[^bb10, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb10(%17: !runtime.transfer<(i1)>):  // pred: ^bb9
      %18 = "runtime.accept_transfer"(%arg0, %17) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%18)[^bb11, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb11(%19: i1):  // pred: ^bb10
      cf.br ^bb8(%19 : i1)
    ^bb12(%20: !runtime.scope):  // pred: ^bb7
      %21 = call @control_2(%20, %arg1, %arg2, %1) : (!runtime.scope, !words, !words, ui64) -> !exec.outcome<(i1)>
      %22 = "runtime.exit_scope"(%20, %21) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%22)[^bb13, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb13(%23: !runtime.transfer<(i1)>):  // pred: ^bb12
      %24 = "runtime.accept_transfer"(%arg0, %23) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%24)[^bb14, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb14(%25: i1):  // pred: ^bb13
      cf.br ^bb8(%25 : i1)
    }
    func.func private @control_0(%arg0: !runtime.scope, %arg1: !words, %arg2: !words, %arg3: ui64) -> !exec.outcome<(i1)> attributes {no_inline, runtime.region} {
      %0 = "exec.apply"(%arg0) <{binding = @constant, parameters = ["0"], site = "zero"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1: ui64):  // pred: ^bb0
      %2 = "exec.boolean"(%arg0) <{site = "yes", value = true}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%3: !exec.stop):  // 5 preds: ^bb0, ^bb1, ^bb3, ^bb7, ^bb9
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(i1)>
      return %4 : !exec.outcome<(i1)>
    ^bb3(%5: i1):  // pred: ^bb1
      %6 = "exec.range"(%arg0, %1, %arg3) <{site = "elements"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<(i64, i64)>) -> ()
    ^bb4(%7: i64, %8: i64):  // pred: ^bb3
      %9 = "runtime.borrow_transfer"(%arg0, %5) : (!runtime.scope, i1) -> !runtime.transfer<(i1)>
      cf.br ^bb5(%7, %9 : i64, !runtime.transfer<(i1)>)
    ^bb5(%10: i64, %11: !runtime.transfer<(i1)>):  // 2 preds: ^bb4, ^bb8
      %12 = arith.cmpi ult, %10, %8 : i64
      cf.cond_br %12, ^bb6, ^bb7(%11 : !runtime.transfer<(i1)>)
    ^bb6:  // pred: ^bb5
      %13 = "runtime.iteration"(%arg0, %10) <{site = "elements"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%13)[^bb10, ^bb9] : (!exec.outcome<(ui64)>) -> ()
    ^bb7(%14: !runtime.transfer<(i1)>):  // pred: ^bb5
      %15 = "runtime.accept_transfer"(%arg0, %14) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%15)[^bb13, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb8(%16: !runtime.transfer<(i1)>):  // pred: ^bb12
      %c1_i64 = arith.constant 1 : i64
      %17 = arith.addi %10, %c1_i64 : i64
      cf.br ^bb5(%17, %16 : i64, !runtime.transfer<(i1)>)
    ^bb9(%18: !exec.stop):  // 3 preds: ^bb6, ^bb10, ^bb11
      "runtime.release_transfer"(%11) : (!runtime.transfer<(i1)>) -> ()
      cf.br ^bb2(%18 : !exec.stop)
    ^bb10(%19: ui64):  // pred: ^bb6
      %20 = "runtime.transfer_values"(%11) : (!runtime.transfer<(i1)>) -> i1
      %21 = "runtime.enter_scope"(%arg0, %10, %19, %20, %arg1, %arg2) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 4>, site = "elements"}> : (!runtime.scope, i64, ui64, i1, !words, !words) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%21)[^bb11, ^bb9] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb11(%22: !runtime.scope):  // pred: ^bb10
      %23 = call @control_1(%22, %19, %20, %arg1, %arg2) : (!runtime.scope, ui64, i1, !words, !words) -> !exec.outcome<(i1)>
      %24 = "runtime.exit_scope"(%22, %23) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%24)[^bb12, ^bb9] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb12(%25: !runtime.transfer<(i1)>):  // pred: ^bb11
      "runtime.release_transfer"(%11) : (!runtime.transfer<(i1)>) -> ()
      cf.br ^bb8(%25 : !runtime.transfer<(i1)>)
    ^bb13(%26: i1):  // pred: ^bb7
      %27 = "exec.complete"(%arg0, %26) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      return %27 : !exec.outcome<(i1)>
    }
    func.func private @control_1(%arg0: !runtime.scope, %arg1: ui64, %arg2: i1, %arg3: !words, %arg4: !words) -> !exec.outcome<(i1)> attributes {no_inline, runtime.region} {
      %0 = "exec.apply"(%arg0, %arg3, %arg1) <{binding = @at, parameters = [], site = "left"}> : (!runtime.scope, !words, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1: ui64):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %arg4, %arg1) <{binding = @at, parameters = [], site = "right"}> : (!runtime.scope, !words, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%3: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(i1)>
      return %4 : !exec.outcome<(i1)>
    ^bb3(%5: ui64):  // pred: ^bb1
      %6 = "exec.apply"(%arg0, %1, %5) <{binding = @equal, parameters = [], site = "same"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb4(%7: i1):  // pred: ^bb3
      %8 = "exec.apply"(%arg0, %arg2, %7) <{binding = @and, parameters = [], site = "next"}> : (!runtime.scope, i1, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%8)[^bb5, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb5(%9: i1):  // pred: ^bb4
      %10 = "exec.complete"(%arg0, %9) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      return %10 : !exec.outcome<(i1)>
    }
    func.func private @control_2(%arg0: !runtime.scope, %arg1: !words, %arg2: !words, %arg3: ui64) -> !exec.outcome<(i1)> attributes {no_inline, runtime.region} {
      %0 = "exec.boolean"(%arg0) <{site = "no", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1: i1):  // pred: ^bb0
      %2 = "exec.complete"(%arg0, %1) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      return %2 : !exec.outcome<(i1)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(i1)>
      return %4 : !exec.outcome<(i1)>
    }
    func.func @init(%arg0: !runtime.scope, %arg1: !words) -> !exec.outcome<(!words)> attributes {no_inline, runtime.origin = ["init", []]} {
      %0 = "exec.apply"(%arg0, %arg1) <{binding = @binding_init, parameters = [], site = "step"}> : (!runtime.scope, !words) -> !exec.outcome<(!words)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!words)>) -> ()
    ^bb1(%1: !words):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!words) -> !exec.outcome<(!words)>
      return %2 : !exec.outcome<(!words)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!words)>
      return %4 : !exec.outcome<(!words)>
    }
    func.func @update(%arg0: !runtime.scope, %arg1: !words, %arg2: !words) -> !exec.outcome<(!words, !words)> attributes {no_inline, runtime.origin = ["update", []]} {
      %0 = "exec.apply"(%arg0, %arg1, %arg2) <{binding = @binding_update, parameters = [], site = "step"}> : (!runtime.scope, !words, !words) -> !exec.outcome<(!words, !words)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!words, !words)>) -> ()
    ^bb1(%1: !words, %2: !words):  // pred: ^bb0
      %3 = "exec.returned"(%1, %2) : (!words, !words) -> !exec.outcome<(!words, !words)>
      return %3 : !exec.outcome<(!words, !words)>
    ^bb2(%4: !exec.stop):  // pred: ^bb0
      %5 = "exec.failed"(%4) : (!exec.stop) -> !exec.outcome<(!words, !words)>
      return %5 : !exec.outcome<(!words, !words)>
    }
    func.func @round(%arg0: !runtime.scope, %arg1: !data.sequence<!words>, %arg2: ui64) -> !exec.outcome<(!words)> attributes {no_inline, runtime.origin = ["round", []]} {
      %0 = "exec.apply"(%arg0, %arg1, %arg2) <{binding = @round_at, parameters = [], site = "word"}> : (!runtime.scope, !data.sequence<!words>, ui64) -> !exec.outcome<(!words)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!words)>) -> ()
    ^bb1(%1: !words):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!words) -> !exec.outcome<(!words)>
      return %2 : !exec.outcome<(!words)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!words)>
      return %4 : !exec.outcome<(!words)>
    }
    func.func @finish(%arg0: !runtime.scope, %arg1: !words) -> !exec.outcome<(!words)> attributes {no_inline, runtime.origin = ["finish", []]} {
      %0 = "exec.apply"(%arg0) <{binding = @empty, parameters = [], site = "empty"}> : (!runtime.scope) -> !exec.outcome<(!words)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!words)>) -> ()
    ^bb1(%1: !words):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %arg1, %1) <{binding = @binding_update, parameters = [], site = "final"}> : (!runtime.scope, !words, !words) -> !exec.outcome<(!words, !words)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(!words, !words)>) -> ()
    ^bb2(%3: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!words)>
      return %4 : !exec.outcome<(!words)>
    ^bb3(%5: !words, %6: !words):  // pred: ^bb1
      %7 = "exec.returned"(%6) : (!words) -> !exec.outcome<(!words)>
      return %7 : !exec.outcome<(!words)>
    }

 "runtime.binding"() {sym_name="binding_init",contract="external.monero.init",arguments=[],implementation="",function_type=(!runtime.scope, !algebra.indices) -> !exec.outcome<(!algebra.indices)>} : ()->()

 "runtime.binding"() {sym_name="binding_update",contract="external.monero.update",arguments=[],implementation="",function_type=(!runtime.scope, !algebra.indices, !algebra.indices) -> !exec.outcome<(!algebra.indices, !algebra.indices)>} : ()->()

 "runtime.binding"() {sym_name="round_at",contract="sequence.at",arguments=[!algebra.indices],implementation="",function_type=(!runtime.scope, !data.sequence<!algebra.indices>, ui64) -> !exec.outcome<(!algebra.indices)>} : ()->()
 "runtime.binding"() {sym_name="empty",contract="indices.empty",arguments=[],implementation="",function_type=(!runtime.scope) -> !exec.outcome<(!algebra.indices)>} : ()->()


 "protocol.func"() ({ ^entry(%seed:!words,%context:!words,%count:ui64,%rounds:!rounds,%complete:i1):
   %p = "protocol.local_call"(%seed) {callee=@init,role="P",site="init_p"} : (!words)->!words
   %v = "protocol.local_call"(%seed) {callee=@init,role="V",site="init_v"} : (!words)->!words
   %p0:2 = "protocol.local_call"(%p,%context) {callee=@update,role="P",site="context_p"} : (!words,!words)->(!words,!words)
   %v0:2 = "protocol.local_call"(%v,%context) {callee=@update,role="V",site="context_v"} : (!words,!words)->(!words,!words)
   %states:2 = "protocol.repeat"(%count,%p0#0,%v0#0,%rounds) ({ ^step(%i:ui64,%ps:!words,%vs:!words,%items:!rounds):
     %word = "protocol.local_call"(%items,%i) {callee=@round,role="P",site="word"} : (!rounds,ui64)->!words
     %received = protocol.exchange %word {sender="P",receiver="V",site="word_message"} : !words
     %pn:2 = "protocol.local_call"(%ps,%word) {callee=@update,role="P",site="step_p"} : (!words,!words)->(!words,!words)
     %vn:2 = "protocol.local_call"(%vs,%received) {callee=@update,role="V",site="step_v"} : (!words,!words)->(!words,!words)
     "protocol.yield"(%pn#0,%vn#0) : (!words,!words)->()
   }) {site="rounds",carried=2:i64,maximum=64:i64,roles=["P","V"],carried_roles=[["P"],["V"]]} : (ui64,!words,!words,!rounds)->(!words,!words)
   %final_p = "protocol.local_call"(%states#0) {callee=@finish,role="P",site="final_p"} : (!words)->!words
   %final_v = "protocol.local_call"(%states#1) {callee=@finish,role="V",site="final_v"} : (!words)->!words
   %claim = protocol.exchange %final_p {sender="P",receiver="V",site="claim"} : !words
   %ok = "protocol.local_call"(%claim,%final_v) {callee=@same,role="V",site="terminal"} : (!words,!words)->i1
   "protocol.return"(%ok,%complete) : (i1,i1)->()
 }) {sym_name="main",function_type=(!words,!words,ui64,!rounds,i1)->(i1,i1),roles=["P","V"],input_roles=[["P","V"],["P","V"],["P","V"],["P"],["P"]],output_roles=[["V"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
