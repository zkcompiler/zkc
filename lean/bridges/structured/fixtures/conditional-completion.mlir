module {
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    func.func @first(%arg0: !runtime.scope, %arg1: ui64, %arg2: ui64, %arg3: !algebra.field<"bls12-381.fr">, %arg4: !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)> attributes {no_inline, runtime.origin = ["first", []]} {
      %0 = "exec.range"(%arg0, %arg1, %arg2) <{site = "loop"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(i64, i64)>) -> ()
    ^bb1(%1: i64, %2: i64):  // pred: ^bb0
      %3 = "runtime.borrow_transfer"(%arg0, %arg3, %arg4) : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !runtime.transfer<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      cf.br ^bb3(%1, %3 : i64, !runtime.transfer<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>)
    ^bb2(%4: !exec.stop):  // 4 preds: ^bb0, ^bb5, ^bb7, ^bb10
      %5 = "exec.failed"(%4) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      return %5 : !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
    ^bb3(%6: i64, %7: !runtime.transfer<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>):  // 2 preds: ^bb1, ^bb6
      %8 = arith.cmpi ult, %6, %2 : i64
      cf.cond_br %8, ^bb4, ^bb5(%7 : !runtime.transfer<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>)
    ^bb4:  // pred: ^bb3
      %9 = "runtime.iteration"(%arg0, %6) <{site = "loop"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%9)[^bb8, ^bb7] : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%10: !runtime.transfer<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>):  // 2 preds: ^bb3, ^bb11
      %11 = "runtime.accept_transfer"(%arg0, %10) : (!runtime.scope, !runtime.transfer<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%11)[^bb12, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
    ^bb6(%12: !runtime.transfer<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>):  // pred: ^bb11
      %c1_i64 = arith.constant 1 : i64
      %13 = arith.addi %6, %c1_i64 : i64
      cf.br ^bb3(%13, %12 : i64, !runtime.transfer<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>)
    ^bb7(%14: !exec.stop):  // 3 preds: ^bb4, ^bb8, ^bb9
      "runtime.release_transfer"(%7) : (!runtime.transfer<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
      cf.br ^bb2(%14 : !exec.stop)
    ^bb8(%15: ui64):  // pred: ^bb4
      %16:2 = "runtime.transfer_values"(%7) : (!runtime.transfer<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      %17 = "runtime.enter_scope"(%arg0, %6, %15, %16#0, %16#1) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 3>, site = "loop"}> : (!runtime.scope, i64, ui64, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%17)[^bb9, ^bb7] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb9(%18: !runtime.scope):  // pred: ^bb8
      %19 = call @body_0(%18, %15, %16#0, %16#1) : (!runtime.scope, ui64, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      %20 = "runtime.exit_scope"(%18, %19) : (!runtime.scope, !exec.outcome<(i1, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> !exec.outcome<(!runtime.transfer<(i1, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>)>
      "exec.dispatch"(%20)[^bb10, ^bb7] : (!exec.outcome<(!runtime.transfer<(i1, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>)>) -> ()
    ^bb10(%21: !runtime.transfer<(i1, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>):  // pred: ^bb9
      "runtime.release_transfer"(%7) : (!runtime.transfer<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> ()
      %22 = "runtime.take_condition"(%21) : (!runtime.transfer<(i1, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>) -> !exec.outcome<(i1, !runtime.transfer<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>)>
      "exec.dispatch"(%22)[^bb11, ^bb2] : (!exec.outcome<(i1, !runtime.transfer<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>)>) -> ()
    ^bb11(%23: i1, %24: !runtime.transfer<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>):  // pred: ^bb10
      cf.cond_br %23, ^bb6(%24 : !runtime.transfer<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>), ^bb5(%24 : !runtime.transfer<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>)
    ^bb12(%25: !algebra.field<"bls12-381.fr">, %26: !algebra.field<"bls12-381.fr">):  // pred: ^bb5
      %27 = "exec.returned"(%25, %26) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      return %27 : !exec.outcome<(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
    }
    func.func private @body_0(%arg0: !runtime.scope, %arg1: ui64, %arg2: !algebra.field<"bls12-381.fr">, %arg3: !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)> attributes {no_inline, runtime.region} {
      %0 = "exec.boolean"(%arg0) <{site = "finish", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1: i1):  // pred: ^bb0
      %2 = "exec.complete"(%arg0, %1, %arg3, %arg2) : (!runtime.scope, i1, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      return %2 : !exec.outcome<(i1, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(i1, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
      return %4 : !exec.outcome<(i1, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)>
    }
    "protocol.func"() <{function_type = (ui64, ui64, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), input_roles = [["P"], ["P"], ["P"], ["P"]], output_roles = [["P"], ["P"]], roles = ["P"], sym_name = "main", origin = ["main", []]}> ({
    ^bb0(%arg0: ui64, %arg1: ui64, %arg2: !algebra.field<"bls12-381.fr">, %arg3: !algebra.field<"bls12-381.fr">):
      %0:2 = "protocol.local_call"(%arg0, %arg1, %arg2, %arg3) <{callee = @first, role = "P", site = "first"}> : (ui64, ui64, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      "protocol.return"(%0#0, %0#1) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
  }) : () -> ()
}
