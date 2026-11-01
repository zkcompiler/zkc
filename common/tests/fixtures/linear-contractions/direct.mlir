// Authored scoped contractions: arithmetic, guard order and cleanup.
!V = !data.field_vector<"ristretto255.scalar">
!A = !data.group_vector<"ristretto255.group">
!R = !algebra.group<"ristretto255.group">
module {
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "runtime.binding"() <{arguments = ["ristretto255.group"], contract = "curve.scale_each", implementation = "", sym_name = "map",function_type=(!runtime.scope, !data.field_vector<"ristretto255.scalar">, !data.group_vector<"ristretto255.group">) -> !exec.outcome<(!data.group_vector<"ristretto255.group">)>}> : () -> ()
    "runtime.binding"() <{arguments = ["ristretto255.group"], contract = "curve.msm", implementation = "", sym_name = "reduce",function_type=(!runtime.scope, !data.field_vector<"ristretto255.scalar">, !data.group_vector<"ristretto255.group">) -> !exec.outcome<(!algebra.group<"ristretto255.group">)>}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "control.require", implementation = "", sym_name = "guard",function_type=(!runtime.scope, i1) -> !exec.outcome<>}> : () -> ()
    func.func @Work(%arg0: !runtime.scope, %arg1: !V, %arg2: !V, %arg3: !V, %arg4: !A, %arg5: i1) -> !exec.outcome<(!R, !R)> attributes {no_inline, runtime.origin = ["Work", []]} {
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
      %9 = "exec.returned"(%5, %8) : (!R, !R) -> !exec.outcome<(!R, !R)>
      return %9 : !exec.outcome<(!R, !R)>
    }
    "protocol.func"() <{function_type = (!V, !V, !V, !A, i1) -> (!R, !R), input_roles = [["P"], ["P"], ["P"], ["P"], ["P"]], origin = ["main", []], output_roles = [["P"], ["P"]], roles = ["P"], sym_name = "main"}> ({
    ^bb0(%arg0: !V, %arg1: !V, %arg2: !V, %arg3: !A, %arg4: i1):
      %0:2 = "protocol.local_call"(%arg0, %arg1, %arg2, %arg3, %arg4) <{callee = @Work, role = "P", site = "work"}> : (!V, !V, !V, !A, i1) -> (!R, !R)
      "protocol.return"(%0#0, %0#1) : (!R, !R) -> ()
    }) : () -> ()
  }) : () -> ()
}
