!F = !algebra.field<"bls12-381.fr">
module {
  "protocol.module"() <{profile = #protocol.profile<exec>}> ({
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "field.add", implementation = "", sym_name = "add"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "field.sub", implementation = "", sym_name = "subtract"}> : () -> ()
    func.func @evaluate(%arg0: !runtime.scope, %arg1: ui64, %arg2: ui64, %arg3: !F, %arg4: !F, %arg5: !F, %arg6: !F) -> !exec.outcome<(!F, !F)> attributes {no_inline, runtime.origin = ["evaluate", []]} {
      %0 = "exec.range"(%arg0, %arg1, %arg2) <{site = "traverse"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(i64, i64)>) -> ()
    ^bb1(%1: i64, %2: i64):  // pred: ^bb0
      %3 = "runtime.borrow_transfer"(%arg0, %arg3, %arg4) : (!runtime.scope, !F, !F) -> !runtime.transfer<(!F, !F)>
      cf.br ^bb3(%1, %3 : i64, !runtime.transfer<(!F, !F)>)
    ^bb2(%4: !exec.stop):  // 3 preds: ^bb0, ^bb5, ^bb7
      %5 = "exec.failed"(%4) : (!exec.stop) -> !exec.outcome<(!F, !F)>
      return %5 : !exec.outcome<(!F, !F)>
    ^bb3(%6: i64, %7: !runtime.transfer<(!F, !F)>):  // 2 preds: ^bb1, ^bb6
      %8 = arith.cmpi ult, %6, %2 : i64
      cf.cond_br %8, ^bb4, ^bb5(%7 : !runtime.transfer<(!F, !F)>)
    ^bb4:  // pred: ^bb3
      %9 = "runtime.iteration"(%arg0, %6) <{site = "traverse"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%9)[^bb8, ^bb7] : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%10: !runtime.transfer<(!F, !F)>):  // pred: ^bb3
      %11 = "runtime.accept_transfer"(%arg0, %10) : (!runtime.scope, !runtime.transfer<(!F, !F)>) -> !exec.outcome<(!F, !F)>
      "exec.dispatch"(%11)[^bb11, ^bb2] : (!exec.outcome<(!F, !F)>) -> ()
    ^bb6(%12: !runtime.transfer<(!F, !F)>):  // pred: ^bb10
      %c1_i64 = arith.constant 1 : i64
      %13 = arith.addi %6, %c1_i64 : i64
      cf.br ^bb3(%13, %12 : i64, !runtime.transfer<(!F, !F)>)
    ^bb7(%14: !exec.stop):  // 3 preds: ^bb4, ^bb8, ^bb9
      "runtime.release_transfer"(%7) : (!runtime.transfer<(!F, !F)>) -> ()
      cf.br ^bb2(%14 : !exec.stop)
    ^bb8(%15: ui64):  // pred: ^bb4
      %16:2 = "runtime.transfer_values"(%7) : (!runtime.transfer<(!F, !F)>) -> (!F, !F)
      %17 = "runtime.enter_scope"(%arg0, %6, %15, %16#0, %16#1, %arg5, %arg6) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 5>, site = "traverse"}> : (!runtime.scope, i64, ui64, !F, !F, !F, !F) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%17)[^bb9, ^bb7] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb9(%18: !runtime.scope):  // pred: ^bb8
      %19 = call @control_0(%18, %15, %16#0, %16#1, %arg5, %arg6) : (!runtime.scope, ui64, !F, !F, !F, !F) -> !exec.outcome<(!F, !F)>
      %20 = "runtime.exit_scope"(%18, %19) : (!runtime.scope, !exec.outcome<(!F, !F)>) -> !exec.outcome<(!runtime.transfer<(!F, !F)>)>
      "exec.dispatch"(%20)[^bb10, ^bb7] : (!exec.outcome<(!runtime.transfer<(!F, !F)>)>) -> ()
    ^bb10(%21: !runtime.transfer<(!F, !F)>):  // pred: ^bb9
      "runtime.release_transfer"(%7) : (!runtime.transfer<(!F, !F)>) -> ()
      cf.br ^bb6(%21 : !runtime.transfer<(!F, !F)>)
    ^bb11(%22: !F, %23: !F):  // pred: ^bb5
      %24 = "exec.returned"(%22, %23) : (!F, !F) -> !exec.outcome<(!F, !F)>
      return %24 : !exec.outcome<(!F, !F)>
    }
    func.func private @control_0(%arg0: !runtime.scope, %arg1: ui64, %arg2: !F, %arg3: !F, %arg4: !F, %arg5: !F) -> !exec.outcome<(!F, !F)> attributes {no_inline, runtime.region} {
      %0 = "exec.apply"(%arg0, %arg2, %arg4) <{binding = @add, parameters = [], site = "sum"}> : (!runtime.scope, !F, !F) -> !exec.outcome<(!F)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!F)>) -> ()
    ^bb1(%1: !F):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %1, %arg5) <{binding = @subtract, parameters = [], site = "next"}> : (!runtime.scope, !F, !F) -> !exec.outcome<(!F)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(!F)>) -> ()
    ^bb2(%3: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!F, !F)>
      return %4 : !exec.outcome<(!F, !F)>
    ^bb3(%5: !F):  // pred: ^bb1
      %6 = "exec.complete"(%arg0, %arg3, %5) : (!runtime.scope, !F, !F) -> !exec.outcome<(!F, !F)>
      return %6 : !exec.outcome<(!F, !F)>
    }
  }) : () -> ()
}
