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
      %0 = "exec.boolean"(%arg0) <{site = "yes", value = true}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1: i1):  // pred: ^bb0
      %2 = "exec.test"(%arg0, %1) <{site = "branch"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%3: !exec.stop):  // 8 preds: ^bb0, ^bb1, ^bb4, ^bb5, ^bb7, ^bb8, ^bb10, ^bb11
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!R, !R)>
      return %4 : !exec.outcome<(!R, !R)>
    ^bb3(%5: i1):  // pred: ^bb1
      cf.cond_br %5, ^bb4, ^bb5
    ^bb4:  // pred: ^bb3
      %6 = "runtime.enter_scope"(%arg0, %arg1, %arg2, %arg3, %arg4, %arg5) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 5>, selection = "then", site = "branch"}> : (!runtime.scope, !V, !V, !V, !A, i1) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%6)[^bb7, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb5:  // pred: ^bb3
      %7 = "runtime.enter_scope"(%arg0, %arg1, %arg2, %arg3, %arg4, %arg5) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 5>, selection = "else", site = "branch"}> : (!runtime.scope, !V, !V, !V, !A, i1) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%7)[^bb10, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6(%8: !R, %9: !R):  // 2 preds: ^bb9, ^bb12
      %10 = "exec.returned"(%8, %9) : (!R, !R) -> !exec.outcome<(!R, !R)>
      return %10 : !exec.outcome<(!R, !R)>
    ^bb7(%11: !runtime.scope):  // pred: ^bb4
      %12 = call @body_0(%11, %arg1, %arg2, %arg3, %arg4, %arg5) : (!runtime.scope, !V, !V, !V, !A, i1) -> !exec.outcome<(!R, !R)>
      %13 = "runtime.exit_scope"(%11, %12) : (!runtime.scope, !exec.outcome<(!R, !R)>) -> !exec.outcome<(!runtime.transfer<(!R, !R)>)>
      "exec.dispatch"(%13)[^bb8, ^bb2] : (!exec.outcome<(!runtime.transfer<(!R, !R)>)>) -> ()
    ^bb8(%14: !runtime.transfer<(!R, !R)>):  // pred: ^bb7
      %15 = "runtime.accept_transfer"(%arg0, %14) : (!runtime.scope, !runtime.transfer<(!R, !R)>) -> !exec.outcome<(!R, !R)>
      "exec.dispatch"(%15)[^bb9, ^bb2] : (!exec.outcome<(!R, !R)>) -> ()
    ^bb9(%16: !R, %17: !R):  // pred: ^bb8
      cf.br ^bb6(%16, %17 : !R, !R)
    ^bb10(%18: !runtime.scope):  // pred: ^bb5
      %19 = call @body_1(%18, %arg1, %arg2, %arg3, %arg4, %arg5) : (!runtime.scope, !V, !V, !V, !A, i1) -> !exec.outcome<(!R, !R)>
      %20 = "runtime.exit_scope"(%18, %19) : (!runtime.scope, !exec.outcome<(!R, !R)>) -> !exec.outcome<(!runtime.transfer<(!R, !R)>)>
      "exec.dispatch"(%20)[^bb11, ^bb2] : (!exec.outcome<(!runtime.transfer<(!R, !R)>)>) -> ()
    ^bb11(%21: !runtime.transfer<(!R, !R)>):  // pred: ^bb10
      %22 = "runtime.accept_transfer"(%arg0, %21) : (!runtime.scope, !runtime.transfer<(!R, !R)>) -> !exec.outcome<(!R, !R)>
      "exec.dispatch"(%22)[^bb12, ^bb2] : (!exec.outcome<(!R, !R)>) -> ()
    ^bb12(%23: !R, %24: !R):  // pred: ^bb11
      cf.br ^bb6(%23, %24 : !R, !R)
    }
    func.func private @body_0(%arg0: !runtime.scope, %arg1: !V, %arg2: !V, %arg3: !V, %arg4: !A, %arg5: i1) -> !exec.outcome<(!R, !R)> attributes {no_inline, runtime.region} {
      %0 = "exec.apply"(%arg0, %arg3, %arg4) <{binding = @map, parameters = [], site = "weighted"}> : (!runtime.scope, !V, !A) -> !exec.outcome<(!A)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!A)>) -> ()
    ^bb1(%1: !A):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %arg1, %1) <{binding = @reduce, parameters = [], site = "first"}> : (!runtime.scope, !V, !A) -> !exec.outcome<(!R)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(!R)>) -> ()
    ^bb2(%3: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!R, !R)>
      return %4 : !exec.outcome<(!R, !R)>
    ^bb3(%5: !R):  // pred: ^bb1
      %6 = "exec.apply"(%arg0, %arg5) <{binding = @guard, parameters = [], site = "between"}> : (!runtime.scope, i1) -> !exec.outcome<>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<>) -> ()
    ^bb4:  // pred: ^bb3
      %7 = "exec.apply"(%arg0, %arg2, %1) <{binding = @reduce, parameters = [], site = "second"}> : (!runtime.scope, !V, !A) -> !exec.outcome<(!R)>
      "exec.dispatch"(%7)[^bb5, ^bb2] : (!exec.outcome<(!R)>) -> ()
    ^bb5(%8: !R):  // pred: ^bb4
      %9 = "exec.complete"(%arg0, %5, %8) : (!runtime.scope, !R, !R) -> !exec.outcome<(!R, !R)>
      return %9 : !exec.outcome<(!R, !R)>
    }
    func.func private @body_1(%arg0: !runtime.scope, %arg1: !V, %arg2: !V, %arg3: !V, %arg4: !A, %arg5: i1) -> !exec.outcome<(!R, !R)> attributes {no_inline, runtime.region} {
      %0 = "exec.reject"(%arg0) <{reason = "abort", site = "unused"}> : (!runtime.scope) -> !exec.stop
      cf.br ^bb1(%0 : !exec.stop)
    ^bb1(%1: !exec.stop):  // pred: ^bb0
      %2 = "exec.failed"(%1) : (!exec.stop) -> !exec.outcome<(!R, !R)>
      return %2 : !exec.outcome<(!R, !R)>
    }
    "protocol.func"() <{function_type = (!V, !V, !V, !A, i1) -> (!R, !R), input_roles = [["P"], ["P"], ["P"], ["P"], ["P"]], origin = ["main", []], output_roles = [["P"], ["P"]], roles = ["P"], sym_name = "main"}> ({
    ^bb0(%arg0: !V, %arg1: !V, %arg2: !V, %arg3: !A, %arg4: i1):
      %0:2 = "protocol.local_call"(%arg0, %arg1, %arg2, %arg3, %arg4) <{callee = @Work, role = "P", site = "work"}> : (!V, !V, !V, !A, i1) -> (!R, !R)
      "protocol.return"(%0#0, %0#1) : (!R, !R) -> ()
    }) : () -> ()
  }) : () -> ()
}
