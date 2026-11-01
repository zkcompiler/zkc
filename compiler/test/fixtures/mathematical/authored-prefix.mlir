// A returned retry skips a local suffix but still reaches the later send.
!words = !data.indices
!f = !algebra.field<"bls12-381.fr">
!rng = !runtime.capability<rng, "bls12-381.fr">
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
    func.func @prepare(%arg0: !runtime.scope, %arg1: !words, %arg2: !words, %arg3: !rng) -> !exec.outcome<(!words, i1, !rng)> attributes {no_inline, runtime.origin = ["prepare", []]} {
      %0 = "exec.apply"(%arg0, %arg3) <{binding = @random, parameters = [], site = "prefix_draw"}> : (!runtime.scope, !rng) -> !exec.outcome<(!f, !rng)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!f, !rng)>) -> ()
    ^bb1(%1: !f, %2: !rng):  // pred: ^bb0
      %3 = "exec.apply"(%arg0, %arg1) <{binding = @init, parameters = [], site = "init"}> : (!runtime.scope, !words) -> !exec.outcome<(!words)>
      "exec.dispatch"(%3)[^bb3, ^bb2] : (!exec.outcome<(!words)>) -> ()
    ^bb2(%4: !exec.stop):  // 12 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb8, ^bb9, ^bb11, ^bb12, ^bb14, ^bb15
      %5 = "exec.failed"(%4) : (!exec.stop) -> !exec.outcome<(!words, i1, !rng)>
      return %5 : !exec.outcome<(!words, i1, !rng)>
    ^bb3(%6: !words):  // pred: ^bb1
      %7 = "exec.apply"(%arg0, %6, %arg2) <{binding = @update, parameters = [], site = "prefix_hash"}> : (!runtime.scope, !words, !words) -> !exec.outcome<(!words, !words)>
      "exec.dispatch"(%7)[^bb4, ^bb2] : (!exec.outcome<(!words, !words)>) -> ()
    ^bb4(%8: !words, %9: !words):  // pred: ^bb3
      %10 = "exec.apply"(%arg0) <{binding = @zero, parameters = [#algebra.literal<!algebra.field<"bls12-381.fr">, 0 : ui255>], site = "zero"}> : (!runtime.scope) -> !exec.outcome<(!f)>
      "exec.dispatch"(%10)[^bb5, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb5(%11: !f):  // pred: ^bb4
      %12 = "exec.apply"(%arg0, %1, %11) <{binding = @field_equal, parameters = [], site = "decision"}> : (!runtime.scope, !f, !f) -> !exec.outcome<(i1)>
      "exec.dispatch"(%12)[^bb6, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb6(%13: i1):  // pred: ^bb5
      %14 = "exec.test"(%arg0, %13) <{site = "suffix"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%14)[^bb7, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb7(%15: i1):  // pred: ^bb6
      cf.cond_br %15, ^bb8, ^bb9
    ^bb8:  // pred: ^bb7
      %16 = "runtime.enter_scope"(%arg0, %8, %9, %arg2, %2) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 4>, selection = "then", site = "suffix"}> : (!runtime.scope, !words, !words, !words, !rng) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%16)[^bb11, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb9:  // pred: ^bb7
      %17 = "runtime.enter_scope"(%arg0, %8, %9, %arg2, %2) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 4>, selection = "else", site = "suffix"}> : (!runtime.scope, !words, !words, !words, !rng) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%17)[^bb14, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb10(%18: !words, %19: i1, %20: !rng):  // 2 preds: ^bb13, ^bb16
      %21 = "exec.returned"(%18, %19, %20) : (!words, i1, !rng) -> !exec.outcome<(!words, i1, !rng)>
      return %21 : !exec.outcome<(!words, i1, !rng)>
    ^bb11(%22: !runtime.scope):  // pred: ^bb8
      %23 = call @control_3(%22, %8, %9, %arg2, %2) : (!runtime.scope, !words, !words, !words, !rng) -> !exec.outcome<(!words, i1, !rng)>
      %24 = "runtime.exit_scope"(%22, %23) : (!runtime.scope, !exec.outcome<(!words, i1, !rng)>) -> !exec.outcome<(!runtime.transfer<(!words, i1, !rng)>)>
      "exec.dispatch"(%24)[^bb12, ^bb2] : (!exec.outcome<(!runtime.transfer<(!words, i1, !rng)>)>) -> ()
    ^bb12(%25: !runtime.transfer<(!words, i1, !rng)>):  // pred: ^bb11
      %26 = "runtime.accept_transfer"(%arg0, %25) : (!runtime.scope, !runtime.transfer<(!words, i1, !rng)>) -> !exec.outcome<(!words, i1, !rng)>
      "exec.dispatch"(%26)[^bb13, ^bb2] : (!exec.outcome<(!words, i1, !rng)>) -> ()
    ^bb13(%27: !words, %28: i1, %29: !rng):  // pred: ^bb12
      cf.br ^bb10(%27, %28, %29 : !words, i1, !rng)
    ^bb14(%30: !runtime.scope):  // pred: ^bb9
      %31 = call @control_4(%30, %8, %9, %arg2, %2) : (!runtime.scope, !words, !words, !words, !rng) -> !exec.outcome<(!words, i1, !rng)>
      %32 = "runtime.exit_scope"(%30, %31) : (!runtime.scope, !exec.outcome<(!words, i1, !rng)>) -> !exec.outcome<(!runtime.transfer<(!words, i1, !rng)>)>
      "exec.dispatch"(%32)[^bb15, ^bb2] : (!exec.outcome<(!runtime.transfer<(!words, i1, !rng)>)>) -> ()
    ^bb15(%33: !runtime.transfer<(!words, i1, !rng)>):  // pred: ^bb14
      %34 = "runtime.accept_transfer"(%arg0, %33) : (!runtime.scope, !runtime.transfer<(!words, i1, !rng)>) -> !exec.outcome<(!words, i1, !rng)>
      "exec.dispatch"(%34)[^bb16, ^bb2] : (!exec.outcome<(!words, i1, !rng)>) -> ()
    ^bb16(%35: !words, %36: i1, %37: !rng):  // pred: ^bb15
      cf.br ^bb10(%35, %36, %37 : !words, i1, !rng)
    }
    func.func private @control_3(%arg0: !runtime.scope, %arg1: !words, %arg2: !words, %arg3: !words, %arg4: !rng) -> !exec.outcome<(!words, i1, !rng)> attributes {no_inline, runtime.region} {
      %0 = "exec.boolean"(%arg0) <{site = "retry", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1: i1):  // pred: ^bb0
      %2 = "exec.complete"(%arg0, %arg2, %1, %arg4) : (!runtime.scope, !words, i1, !rng) -> !exec.outcome<(!words, i1, !rng)>
      return %2 : !exec.outcome<(!words, i1, !rng)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!words, i1, !rng)>
      return %4 : !exec.outcome<(!words, i1, !rng)>
    }
    func.func private @control_4(%arg0: !runtime.scope, %arg1: !words, %arg2: !words, %arg3: !words, %arg4: !rng) -> !exec.outcome<(!words, i1, !rng)> attributes {no_inline, runtime.region} {
      %0 = "exec.apply"(%arg0, %arg4) <{binding = @random, parameters = [], site = "suffix_draw"}> : (!runtime.scope, !rng) -> !exec.outcome<(!f, !rng)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!f, !rng)>) -> ()
    ^bb1(%1: !f, %2: !rng):  // pred: ^bb0
      %3 = "exec.apply"(%arg0, %arg1, %arg3) <{binding = @update, parameters = [], site = "suffix_hash"}> : (!runtime.scope, !words, !words) -> !exec.outcome<(!words, !words)>
      "exec.dispatch"(%3)[^bb3, ^bb2] : (!exec.outcome<(!words, !words)>) -> ()
    ^bb2(%4: !exec.stop):  // 3 preds: ^bb0, ^bb1, ^bb3
      %5 = "exec.failed"(%4) : (!exec.stop) -> !exec.outcome<(!words, i1, !rng)>
      return %5 : !exec.outcome<(!words, i1, !rng)>
    ^bb3(%6: !words, %7: !words):  // pred: ^bb1
      %8 = "exec.boolean"(%arg0) <{site = "complete", value = true}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%8)[^bb4, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb4(%9: i1):  // pred: ^bb3
      %10 = "exec.complete"(%arg0, %7, %9, %2) : (!runtime.scope, !words, i1, !rng) -> !exec.outcome<(!words, i1, !rng)>
      return %10 : !exec.outcome<(!words, i1, !rng)>
    }
    func.func @expected(%arg0: !runtime.scope, %arg1: !words, %arg2: !words) -> !exec.outcome<(!words)> attributes {no_inline, runtime.origin = ["expected", []]} {
      %0 = "exec.apply"(%arg0, %arg1) <{binding = @init, parameters = [], site = "init"}> : (!runtime.scope, !words) -> !exec.outcome<(!words)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!words)>) -> ()
    ^bb1(%1: !words):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %1, %arg2) <{binding = @update, parameters = [], site = "first"}> : (!runtime.scope, !words, !words) -> !exec.outcome<(!words, !words)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(!words, !words)>) -> ()
    ^bb2(%3: !exec.stop):  // 3 preds: ^bb0, ^bb1, ^bb3
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!words)>
      return %4 : !exec.outcome<(!words)>
    ^bb3(%5: !words, %6: !words):  // pred: ^bb1
      %7 = "exec.apply"(%arg0, %5, %arg2) <{binding = @update, parameters = [], site = "second"}> : (!runtime.scope, !words, !words) -> !exec.outcome<(!words, !words)>
      "exec.dispatch"(%7)[^bb4, ^bb2] : (!exec.outcome<(!words, !words)>) -> ()
    ^bb4(%8: !words, %9: !words):  // pred: ^bb3
      %10 = "exec.returned"(%9) : (!words) -> !exec.outcome<(!words)>
      return %10 : !exec.outcome<(!words)>
    }

 "runtime.binding"() {sym_name="init",contract="external.monero.init",arguments=[],implementation="",function_type=(!runtime.scope, !data.indices) -> !exec.outcome<(!data.indices)>} : ()->()
 "runtime.binding"() {sym_name="update",contract="external.monero.update",arguments=[],implementation="",function_type=(!runtime.scope, !data.indices, !data.indices) -> !exec.outcome<(!data.indices, !data.indices)>} : ()->()
 "runtime.binding"() {sym_name="random",contract="random.draw",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope, !runtime.capability<rng, "bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !runtime.capability<rng, "bls12-381.fr">)>} : ()->()
 "runtime.binding"() {sym_name="zero",contract="field.constant",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>} : ()->()
 "runtime.binding"() {sym_name="field_equal",contract="field.equal",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>} : ()->()


 "protocol.func"() ({ ^entry(%seed:!words,%context:!words,%rng:!rng):
   %prepared:3 = "protocol.local_call"(%seed,%context,%rng) {callee=@prepare,role="P",site="prepare"} : (!words,!words,!rng)->(!words,i1,!rng)
   %claim = protocol.exchange %prepared#0 {sender="P",receiver="V",site="claim"} : !words
   %expected = "protocol.local_call"(%seed,%context) {callee=@expected,role="V",site="expected"} : (!words,!words)->!words
   %ok = "protocol.local_call"(%claim,%expected) {callee=@same,role="V",site="terminal"} : (!words,!words)->i1
   "protocol.return"(%ok,%prepared#1,%prepared#2) : (i1,i1,!rng)->()
 }) {sym_name="main",function_type=(!words,!words,!rng)->(i1,i1,!rng),roles=["P","V"],input_roles=[["P","V"],["P","V"],["P"]],output_roles=[["V"],["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
