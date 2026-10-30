// Authored scoped contractions: arithmetic, guard order and cleanup.
!V = !algebra.field_vector<"ristretto255.scalar">
!A = !algebra.group_vector<"ristretto255.group">
!R = !algebra.group<"ristretto255.group">
module {
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "runtime.binding"() <{arguments = ["ristretto255.group"], contract = "curve.scale_each", implementation = "", sym_name = "map",function_type=(!runtime.scope, !algebra.field_vector<"ristretto255.scalar">, !algebra.group_vector<"ristretto255.group">) -> !exec.outcome<(!algebra.group_vector<"ristretto255.group">)>}> : () -> ()
    "runtime.binding"() <{arguments = ["ristretto255.group"], contract = "curve.msm", implementation = "", sym_name = "reduce",function_type=(!runtime.scope, !algebra.field_vector<"ristretto255.scalar">, !algebra.group_vector<"ristretto255.group">) -> !exec.outcome<(!algebra.group<"ristretto255.group">)>}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "control.require", implementation = "", sym_name = "guard",function_type=(!runtime.scope, i1) -> !exec.outcome<>}> : () -> ()
    func.func @Work(%arg0: !runtime.scope, %arg1: !V, %arg2: !V, %arg3: !V, %arg4: !A, %arg5: i1) -> !exec.outcome<(!R, !R)> attributes {no_inline, runtime.origin = ["Work", []]} {
      %0 = "exec.apply"(%arg0) <{binding = @constant, parameters = ["0"], site = "zero"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1: ui64):  // pred: ^bb0
      %2 = "exec.apply"(%arg0) <{binding = @constant, parameters = ["2"], site = "count"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%3: !exec.stop):  // 6 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb8, ^bb10
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!R, !R)>
      return %4 : !exec.outcome<(!R, !R)>
    ^bb3(%5: ui64):  // pred: ^bb1
      %6 = "exec.apply"(%arg0, %arg1, %arg4) <{binding = @reduce, parameters = [], site = "seed"}> : (!runtime.scope, !V, !A) -> !exec.outcome<(!R)>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<(!R)>) -> ()
    ^bb4(%7: !R):  // pred: ^bb3
      %8 = "exec.range"(%arg0, %1, %5) <{site = "loop"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%8)[^bb5, ^bb2] : (!exec.outcome<(i64, i64)>) -> ()
    ^bb5(%9: i64, %10: i64):  // pred: ^bb4
      %11 = "runtime.borrow_transfer"(%arg0, %7, %7) : (!runtime.scope, !R, !R) -> !runtime.transfer<(!R, !R)>
      cf.br ^bb6(%9, %11 : i64, !runtime.transfer<(!R, !R)>)
    ^bb6(%12: i64, %13: !runtime.transfer<(!R, !R)>):  // 2 preds: ^bb5, ^bb9
      %14 = arith.cmpi ult, %12, %10 : i64
      cf.cond_br %14, ^bb7, ^bb8(%13 : !runtime.transfer<(!R, !R)>)
    ^bb7:  // pred: ^bb6
      %15 = "runtime.iteration"(%arg0, %12) <{site = "loop"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%15)[^bb11, ^bb10] : (!exec.outcome<(ui64)>) -> ()
    ^bb8(%16: !runtime.transfer<(!R, !R)>):  // pred: ^bb6
      %17 = "runtime.accept_transfer"(%arg0, %16) : (!runtime.scope, !runtime.transfer<(!R, !R)>) -> !exec.outcome<(!R, !R)>
      "exec.dispatch"(%17)[^bb14, ^bb2] : (!exec.outcome<(!R, !R)>) -> ()
    ^bb9(%18: !runtime.transfer<(!R, !R)>):  // pred: ^bb13
      %c1_i64 = arith.constant 1 : i64
      %19 = arith.addi %12, %c1_i64 : i64
      cf.br ^bb6(%19, %18 : i64, !runtime.transfer<(!R, !R)>)
    ^bb10(%20: !exec.stop):  // 3 preds: ^bb7, ^bb11, ^bb12
      "runtime.release_transfer"(%13) : (!runtime.transfer<(!R, !R)>) -> ()
      cf.br ^bb2(%20 : !exec.stop)
    ^bb11(%21: ui64):  // pred: ^bb7
      %22:2 = "runtime.transfer_values"(%13) : (!runtime.transfer<(!R, !R)>) -> (!R, !R)
      %23 = "runtime.enter_scope"(%arg0, %12, %21, %22#0, %22#1, %arg1, %arg2, %arg3, %arg4, %arg5) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 8>, site = "loop"}> : (!runtime.scope, i64, ui64, !R, !R, !V, !V, !V, !A, i1) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%23)[^bb12, ^bb10] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb12(%24: !runtime.scope):  // pred: ^bb11
      %25 = call @body_0(%24, %21, %22#0, %22#1, %arg1, %arg2, %arg3, %arg4, %arg5) : (!runtime.scope, ui64, !R, !R, !V, !V, !V, !A, i1) -> !exec.outcome<(!R, !R)>
      %26 = "runtime.exit_scope"(%24, %25) : (!runtime.scope, !exec.outcome<(!R, !R)>) -> !exec.outcome<(!runtime.transfer<(!R, !R)>)>
      "exec.dispatch"(%26)[^bb13, ^bb10] : (!exec.outcome<(!runtime.transfer<(!R, !R)>)>) -> ()
    ^bb13(%27: !runtime.transfer<(!R, !R)>):  // pred: ^bb12
      "runtime.release_transfer"(%13) : (!runtime.transfer<(!R, !R)>) -> ()
      cf.br ^bb9(%27 : !runtime.transfer<(!R, !R)>)
    ^bb14(%28: !R, %29: !R):  // pred: ^bb8
      %30 = "exec.returned"(%28, %29) : (!R, !R) -> !exec.outcome<(!R, !R)>
      return %30 : !exec.outcome<(!R, !R)>
    }
    "runtime.binding"() <{arguments = [], contract = "index.constant", implementation = "", sym_name = "constant",function_type=(!runtime.scope) -> !exec.outcome<(ui64)>}> : () -> ()
    func.func private @body_0(%arg0: !runtime.scope, %arg1: ui64, %arg2: !R, %arg3: !R, %arg4: !V, %arg5: !V, %arg6: !V, %arg7: !A, %arg8: i1) -> !exec.outcome<(!R, !R)> attributes {no_inline, runtime.region} {
      %0 = "exec.apply"(%arg0, %arg6, %arg7) <{binding = @map, parameters = [], site = "weighted"}> : (!runtime.scope, !V, !A) -> !exec.outcome<(!A)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!A)>) -> ()
    ^bb1(%1: !A):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %arg4, %1) <{binding = @reduce, parameters = [], site = "first"}> : (!runtime.scope, !V, !A) -> !exec.outcome<(!R)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(!R)>) -> ()
    ^bb2(%3: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!R, !R)>
      return %4 : !exec.outcome<(!R, !R)>
    ^bb3(%5: !R):  // pred: ^bb1
      %6 = "exec.apply"(%arg0, %arg8) <{binding = @guard, parameters = [], site = "between"}> : (!runtime.scope, i1) -> !exec.outcome<>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<>) -> ()
    ^bb4:  // pred: ^bb3
      %7 = "exec.apply"(%arg0, %arg5, %1) <{binding = @reduce, parameters = [], site = "second"}> : (!runtime.scope, !V, !A) -> !exec.outcome<(!R)>
      "exec.dispatch"(%7)[^bb5, ^bb2] : (!exec.outcome<(!R)>) -> ()
    ^bb5(%8: !R):  // pred: ^bb4
      %9 = "exec.complete"(%arg0, %5, %8) : (!runtime.scope, !R, !R) -> !exec.outcome<(!R, !R)>
      return %9 : !exec.outcome<(!R, !R)>
    }
    "protocol.func"() <{function_type = (!V, !V, !V, !A, i1) -> (!R, !R), input_roles = [["P"], ["P"], ["P"], ["P"], ["P"]], origin = ["main", []], output_roles = [["P"], ["P"]], roles = ["P"], sym_name = "main"}> ({
    ^bb0(%arg0: !V, %arg1: !V, %arg2: !V, %arg3: !A, %arg4: i1):
      %0:2 = "protocol.local_call"(%arg0, %arg1, %arg2, %arg3, %arg4) <{callee = @Work, role = "P", site = "work"}> : (!V, !V, !V, !A, i1) -> (!R, !R)
      "protocol.return"(%0#0, %0#1) : (!R, !R) -> ()
    }) : () -> ()
  }) : () -> ()
}
