// Candidate search uses immutable trials and checks the chosen witness on live state.
!words = !data.indices
module { "protocol.module"() ({
 "runtime.binding"() {sym_name="constant",contract="index.constant",arguments=[],implementation="",function_type=(!runtime.scope) -> !exec.outcome<(ui64)>} : ()->()
 "runtime.binding"() {sym_name="length",contract="indices.length",arguments=[],implementation="",function_type=(!runtime.scope, !data.indices) -> !exec.outcome<(ui64)>} : ()->()
 "runtime.binding"() {sym_name="at",contract="indices.at",arguments=[],implementation="",function_type=(!runtime.scope, !data.indices, ui64) -> !exec.outcome<(ui64)>} : ()->()
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
      %0 = "exec.apply"(%arg0) <{binding = @constant, parameters = [0 : ui64], site = "zero"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
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
    func.func @init(%arg0: !runtime.scope) -> !exec.outcome<(!words)> attributes {no_inline, runtime.origin = ["init", []]} {
      %0 = "exec.apply"(%arg0) <{binding = @binding_init, parameters = [], site = "step"}> : (!runtime.scope) -> !exec.outcome<(!words)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!words)>) -> ()
    ^bb1(%1: !words):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!words) -> !exec.outcome<(!words)>
      return %2 : !exec.outcome<(!words)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!words)>
      return %4 : !exec.outcome<(!words)>
    }
    func.func @observe(%arg0: !runtime.scope, %arg1: !words, %arg2: !words) -> !exec.outcome<(!words)> attributes {no_inline, runtime.origin = ["observe", []]} {
      %0 = "exec.apply"(%arg0, %arg1, %arg2) <{binding = @binding_observe, parameters = [], site = "step"}> : (!runtime.scope, !words, !words) -> !exec.outcome<(!words)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!words)>) -> ()
    ^bb1(%1: !words):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!words) -> !exec.outcome<(!words)>
      return %2 : !exec.outcome<(!words)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!words)>
      return %4 : !exec.outcome<(!words)>
    }
    func.func @check(%arg0: !runtime.scope, %arg1: !words, %arg2: ui64, %arg3: ui64) -> !exec.outcome<(!words, i1)> attributes {no_inline, runtime.origin = ["check", []]} {
      %0 = "exec.apply"(%arg0, %arg1, %arg2, %arg3) <{binding = @binding_check, parameters = [], site = "step"}> : (!runtime.scope, !words, ui64, ui64) -> !exec.outcome<(!words, i1)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!words, i1)>) -> ()
    ^bb1(%1: !words, %2: i1):  // pred: ^bb0
      %3 = "exec.returned"(%1, %2) : (!words, i1) -> !exec.outcome<(!words, i1)>
      return %3 : !exec.outcome<(!words, i1)>
    ^bb2(%4: !exec.stop):  // pred: ^bb0
      %5 = "exec.failed"(%4) : (!exec.stop) -> !exec.outcome<(!words, i1)>
      return %5 : !exec.outcome<(!words, i1)>
    }
    func.func @samples(%arg0: !runtime.scope, %arg1: !words, %arg2: ui64) -> !exec.outcome<(!words, ui64, ui64)> attributes {no_inline, runtime.origin = ["samples", []]} {
      %0 = "exec.apply"(%arg0, %arg1) <{binding = @ext, parameters = [], site = "extension"}> : (!runtime.scope, !words) -> !exec.outcome<(!words, !words)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!words, !words)>) -> ()
    ^bb1(%1: !words, %2: !words):  // pred: ^bb0
      %3 = "exec.apply"(%arg0, %1, %arg2) <{binding = @bits, parameters = [], site = "bits"}> : (!runtime.scope, !words, ui64) -> !exec.outcome<(!words, ui64)>
      "exec.dispatch"(%3)[^bb3, ^bb2] : (!exec.outcome<(!words, ui64)>) -> ()
    ^bb2(%4: !exec.stop):  // 3 preds: ^bb0, ^bb1, ^bb3
      %5 = "exec.failed"(%4) : (!exec.stop) -> !exec.outcome<(!words, ui64, ui64)>
      return %5 : !exec.outcome<(!words, ui64, ui64)>
    ^bb3(%6: !words, %7: ui64):  // pred: ^bb1
      %8 = "exec.apply"(%arg0, %6) <{binding = @scalar, parameters = [], site = "scalar"}> : (!runtime.scope, !words) -> !exec.outcome<(!words, ui64)>
      "exec.dispatch"(%8)[^bb4, ^bb2] : (!exec.outcome<(!words, ui64)>) -> ()
    ^bb4(%9: !words, %10: ui64):  // pred: ^bb3
      %11 = "exec.returned"(%2, %7, %10) : (!words, ui64, ui64) -> !exec.outcome<(!words, ui64, ui64)>
      return %11 : !exec.outcome<(!words, ui64, ui64)>
    }
    func.func @search(%arg0: !runtime.scope, %arg1: !words, %arg2: ui64, %arg3: !words) -> !exec.outcome<(ui64, i1)> attributes {no_inline, runtime.origin = ["search", []]} {
      %0 = "exec.apply"(%arg0) <{binding = @constant, parameters = [0 : ui64], site = "zero"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1: ui64):  // pred: ^bb0
      %2 = "exec.boolean"(%arg0) <{site = "no", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%3: !exec.stop):  // 6 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb8, ^bb10
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(ui64, i1)>
      return %4 : !exec.outcome<(ui64, i1)>
    ^bb3(%5: i1):  // pred: ^bb1
      %6 = "exec.apply"(%arg0, %arg3) <{binding = @length, parameters = [], site = "count"}> : (!runtime.scope, !words) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%7: ui64):  // pred: ^bb3
      %8 = "exec.range"(%arg0, %1, %7) <{site = "candidates"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%8)[^bb5, ^bb2] : (!exec.outcome<(i64, i64)>) -> ()
    ^bb5(%9: i64, %10: i64):  // pred: ^bb4
      %11 = "runtime.borrow_transfer"(%arg0, %1, %5) : (!runtime.scope, ui64, i1) -> !runtime.transfer<(ui64, i1)>
      cf.br ^bb6(%9, %11 : i64, !runtime.transfer<(ui64, i1)>)
    ^bb6(%12: i64, %13: !runtime.transfer<(ui64, i1)>):  // 2 preds: ^bb5, ^bb9
      %14 = arith.cmpi ult, %12, %10 : i64
      cf.cond_br %14, ^bb7, ^bb8(%13 : !runtime.transfer<(ui64, i1)>)
    ^bb7:  // pred: ^bb6
      %15 = "runtime.iteration"(%arg0, %12) <{site = "candidates"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%15)[^bb11, ^bb10] : (!exec.outcome<(ui64)>) -> ()
    ^bb8(%16: !runtime.transfer<(ui64, i1)>):  // pred: ^bb6
      %17 = "runtime.accept_transfer"(%arg0, %16) : (!runtime.scope, !runtime.transfer<(ui64, i1)>) -> !exec.outcome<(ui64, i1)>
      "exec.dispatch"(%17)[^bb14, ^bb2] : (!exec.outcome<(ui64, i1)>) -> ()
    ^bb9(%18: !runtime.transfer<(ui64, i1)>):  // pred: ^bb13
      %c1_i64 = arith.constant 1 : i64
      %19 = arith.addi %12, %c1_i64 : i64
      cf.br ^bb6(%19, %18 : i64, !runtime.transfer<(ui64, i1)>)
    ^bb10(%20: !exec.stop):  // 3 preds: ^bb7, ^bb11, ^bb12
      "runtime.release_transfer"(%13) : (!runtime.transfer<(ui64, i1)>) -> ()
      cf.br ^bb2(%20 : !exec.stop)
    ^bb11(%21: ui64):  // pred: ^bb7
      %22:2 = "runtime.transfer_values"(%13) : (!runtime.transfer<(ui64, i1)>) -> (ui64, i1)
      %23 = "runtime.enter_scope"(%arg0, %12, %21, %22#0, %22#1, %arg1, %arg2, %arg3) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 6>, site = "candidates"}> : (!runtime.scope, i64, ui64, ui64, i1, !words, ui64, !words) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%23)[^bb12, ^bb10] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb12(%24: !runtime.scope):  // pred: ^bb11
      %25 = call @control_3(%24, %21, %22#0, %22#1, %arg1, %arg2, %arg3) : (!runtime.scope, ui64, ui64, i1, !words, ui64, !words) -> !exec.outcome<(ui64, i1)>
      %26 = "runtime.exit_scope"(%24, %25) : (!runtime.scope, !exec.outcome<(ui64, i1)>) -> !exec.outcome<(!runtime.transfer<(ui64, i1)>)>
      "exec.dispatch"(%26)[^bb13, ^bb10] : (!exec.outcome<(!runtime.transfer<(ui64, i1)>)>) -> ()
    ^bb13(%27: !runtime.transfer<(ui64, i1)>):  // pred: ^bb12
      "runtime.release_transfer"(%13) : (!runtime.transfer<(ui64, i1)>) -> ()
      cf.br ^bb9(%27 : !runtime.transfer<(ui64, i1)>)
    ^bb14(%28: ui64, %29: i1):  // pred: ^bb8
      %30 = "exec.returned"(%28, %29) : (ui64, i1) -> !exec.outcome<(ui64, i1)>
      return %30 : !exec.outcome<(ui64, i1)>
    }
    func.func private @control_3(%arg0: !runtime.scope, %arg1: ui64, %arg2: ui64, %arg3: i1, %arg4: !words, %arg5: ui64, %arg6: !words) -> !exec.outcome<(ui64, i1)> attributes {no_inline, runtime.region} {
      %0 = "exec.test"(%arg0, %arg3) <{site = "searching"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1: i1):  // pred: ^bb0
      cf.cond_br %1, ^bb3, ^bb4
    ^bb2(%2: !exec.stop):  // 7 preds: ^bb0, ^bb3, ^bb4, ^bb6, ^bb7, ^bb9, ^bb10
      %3 = "exec.failed"(%2) : (!exec.stop) -> !exec.outcome<(ui64, i1)>
      return %3 : !exec.outcome<(ui64, i1)>
    ^bb3:  // pred: ^bb1
      %4 = "runtime.enter_scope"(%arg0, %arg2, %arg4, %arg5, %arg6, %arg1) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 5>, selection = "then", site = "searching"}> : (!runtime.scope, ui64, !words, ui64, !words, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%4)[^bb6, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb4:  // pred: ^bb1
      %5 = "runtime.enter_scope"(%arg0, %arg2, %arg4, %arg5, %arg6, %arg1) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 5>, selection = "else", site = "searching"}> : (!runtime.scope, ui64, !words, ui64, !words, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%5)[^bb9, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb5(%6: ui64, %7: i1):  // 2 preds: ^bb8, ^bb11
      %8 = "exec.complete"(%arg0, %6, %7) : (!runtime.scope, ui64, i1) -> !exec.outcome<(ui64, i1)>
      return %8 : !exec.outcome<(ui64, i1)>
    ^bb6(%9: !runtime.scope):  // pred: ^bb3
      %10 = call @control_4(%9, %arg2, %arg4, %arg5, %arg6, %arg1) : (!runtime.scope, ui64, !words, ui64, !words, ui64) -> !exec.outcome<(ui64, i1)>
      %11 = "runtime.exit_scope"(%9, %10) : (!runtime.scope, !exec.outcome<(ui64, i1)>) -> !exec.outcome<(!runtime.transfer<(ui64, i1)>)>
      "exec.dispatch"(%11)[^bb7, ^bb2] : (!exec.outcome<(!runtime.transfer<(ui64, i1)>)>) -> ()
    ^bb7(%12: !runtime.transfer<(ui64, i1)>):  // pred: ^bb6
      %13 = "runtime.accept_transfer"(%arg0, %12) : (!runtime.scope, !runtime.transfer<(ui64, i1)>) -> !exec.outcome<(ui64, i1)>
      "exec.dispatch"(%13)[^bb8, ^bb2] : (!exec.outcome<(ui64, i1)>) -> ()
    ^bb8(%14: ui64, %15: i1):  // pred: ^bb7
      cf.br ^bb5(%14, %15 : ui64, i1)
    ^bb9(%16: !runtime.scope):  // pred: ^bb4
      %17 = call @control_5(%16, %arg2, %arg4, %arg5, %arg6, %arg1) : (!runtime.scope, ui64, !words, ui64, !words, ui64) -> !exec.outcome<(ui64, i1)>
      %18 = "runtime.exit_scope"(%16, %17) : (!runtime.scope, !exec.outcome<(ui64, i1)>) -> !exec.outcome<(!runtime.transfer<(ui64, i1)>)>
      "exec.dispatch"(%18)[^bb10, ^bb2] : (!exec.outcome<(!runtime.transfer<(ui64, i1)>)>) -> ()
    ^bb10(%19: !runtime.transfer<(ui64, i1)>):  // pred: ^bb9
      %20 = "runtime.accept_transfer"(%arg0, %19) : (!runtime.scope, !runtime.transfer<(ui64, i1)>) -> !exec.outcome<(ui64, i1)>
      "exec.dispatch"(%20)[^bb11, ^bb2] : (!exec.outcome<(ui64, i1)>) -> ()
    ^bb11(%21: ui64, %22: i1):  // pred: ^bb10
      cf.br ^bb5(%21, %22 : ui64, i1)
    }
    func.func private @control_4(%arg0: !runtime.scope, %arg1: ui64, %arg2: !words, %arg3: ui64, %arg4: !words, %arg5: ui64) -> !exec.outcome<(ui64, i1)> attributes {no_inline, runtime.region} {
      %0 = "exec.boolean"(%arg0) <{site = "found", value = true}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1: i1):  // pred: ^bb0
      %2 = "exec.complete"(%arg0, %arg1, %1) : (!runtime.scope, ui64, i1) -> !exec.outcome<(ui64, i1)>
      return %2 : !exec.outcome<(ui64, i1)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(ui64, i1)>
      return %4 : !exec.outcome<(ui64, i1)>
    }
    func.func private @control_5(%arg0: !runtime.scope, %arg1: ui64, %arg2: !words, %arg3: ui64, %arg4: !words, %arg5: ui64) -> !exec.outcome<(ui64, i1)> attributes {no_inline, runtime.region} {
      %0 = "exec.apply"(%arg0, %arg4, %arg5) <{binding = @at, parameters = [], site = "candidate"}> : (!runtime.scope, !words, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1: ui64):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %arg2, %arg3, %1) <{binding = @binding_check, parameters = [], site = "trial"}> : (!runtime.scope, !words, ui64, ui64) -> !exec.outcome<(!words, i1)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(!words, i1)>) -> ()
    ^bb2(%3: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(ui64, i1)>
      return %4 : !exec.outcome<(ui64, i1)>
    ^bb3(%5: !words, %6: i1):  // pred: ^bb1
      %7 = "exec.complete"(%arg0, %1, %6) : (!runtime.scope, ui64, i1) -> !exec.outcome<(ui64, i1)>
      return %7 : !exec.outcome<(ui64, i1)>
    }

 "runtime.binding"() {sym_name="binding_init",contract="external.openvm.init",arguments=[],implementation="",function_type=(!runtime.scope) -> !exec.outcome<(!data.indices)>} : ()->()

 "runtime.binding"() {sym_name="binding_observe",contract="external.openvm.observe",arguments=[],implementation="",function_type=(!runtime.scope, !data.indices, !data.indices) -> !exec.outcome<(!data.indices)>} : ()->()

 "runtime.binding"() {sym_name="binding_check",contract="external.openvm.check_witness",arguments=[],implementation="",function_type=(!runtime.scope, !data.indices, ui64, ui64) -> !exec.outcome<(!data.indices, i1)>} : ()->()

 "runtime.binding"() {sym_name="ext",contract="external.openvm.sample_ext",arguments=[],implementation="",function_type=(!runtime.scope, !data.indices) -> !exec.outcome<(!data.indices, !data.indices)>} : ()->()
 "runtime.binding"() {sym_name="bits",contract="external.openvm.sample_bits",arguments=[],implementation="",function_type=(!runtime.scope, !data.indices, ui64) -> !exec.outcome<(!data.indices, ui64)>} : ()->()
 "runtime.binding"() {sym_name="scalar",contract="external.openvm.sample",arguments=[],implementation="",function_type=(!runtime.scope, !data.indices) -> !exec.outcome<(!data.indices, ui64)>} : ()->()


 "protocol.func"() ({ ^entry(%context:!words,%difficulty:ui64,%width:ui64,%candidates:!words):
   %p = "protocol.local_call"() {callee=@init,role="P",site="init_p"} : ()->!words
   %v = "protocol.local_call"() {callee=@init,role="V",site="init_v"} : ()->!words
   %ps = "protocol.local_call"(%p,%context) {callee=@observe,role="P",site="context_p"} : (!words,!words)->!words
   %vs = "protocol.local_call"(%v,%context) {callee=@observe,role="V",site="context_v"} : (!words,!words)->!words
   %choice:2 = "protocol.local_call"(%ps,%difficulty,%candidates) {callee=@search,role="P",site="search"} : (!words,ui64,!words)->(ui64,i1)
   %witness = protocol.exchange %choice#0 {sender="P",receiver="V",site="witness"} : ui64
   %pchecked:2 = "protocol.local_call"(%ps,%difficulty,%choice#0) {callee=@check,role="P",site="live_p"} : (!words,ui64,ui64)->(!words,i1)
   %vchecked:2 = "protocol.local_call"(%vs,%difficulty,%witness) {callee=@check,role="V",site="live_v"} : (!words,ui64,ui64)->(!words,i1)
   protocol.guard %vchecked#1 {owner="V",site="witness_valid"}
   %pout:3 = "protocol.local_call"(%pchecked#0,%width) {callee=@samples,role="P",site="samples_p"} : (!words,ui64)->(!words,ui64,ui64)
   %vout:3 = "protocol.local_call"(%vchecked#0,%width) {callee=@samples,role="V",site="samples_v"} : (!words,ui64)->(!words,ui64,ui64)
   %extension = protocol.exchange %pout#0 {sender="P",receiver="V",site="extension"} : !words
   %bits = protocol.exchange %pout#1 {sender="P",receiver="V",site="bits"} : ui64
   %scalar = protocol.exchange %pout#2 {sender="P",receiver="V",site="scalar"} : ui64
   %eq = "protocol.local_call"(%extension,%vout#0) {callee=@same,role="V",site="extension_equal"} : (!words,!words)->i1
   %bits_ok = "data.index_equal"(%bits,%vout#1) : (ui64,ui64)->i1
   %scalar_ok = "data.index_equal"(%scalar,%vout#2) : (ui64,ui64)->i1
   %both = arith.andi %eq,%bits_ok : i1
   %ok = arith.andi %both,%scalar_ok : i1
   "protocol.return"(%ok,%choice#1) : (i1,i1)->()
 }) {sym_name="main",function_type=(!words,ui64,ui64,!words)->(i1,i1),roles=["P","V"],input_roles=[["P","V"],["P","V"],["P","V"],["P"]],output_roles=[["V"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
