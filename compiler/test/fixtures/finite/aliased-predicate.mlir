!V = !data.field_vector<"bls12-381.fr">
!I = !data.indices
module {
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "runtime.binding"() <{arguments = [], contract = "index.mul", implementation = "", sym_name = "mul",function_type=(!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.add", implementation = "", sym_name = "add",function_type=(!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>}> : () -> ()
    "data.domain"() <{function_type = (!V, ui64, ui64) -> !data.domain<ui64, ui64>, sym_name = "items", sym_visibility = "private"}> ({
    ^bb0(%arg0: !V, %arg1: ui64, %arg2: ui64):
      %0 = "data.domain_indices"(%arg0) <{axis = 0 : i64}> : (!V) -> !data.domain<ui64>
      %1 = "data.domain_indices"(%arg0) <{axis = 0 : i64}> : (!V) -> !data.domain<ui64>
      %2 = "data.domain_zip"(%0, %1) : (!data.domain<ui64>, !data.domain<ui64>) -> !data.domain<ui64, ui64>
      "data.domain_yield"(%2) : (!data.domain<ui64, ui64>) -> ()
    }) : () -> ()
    "protocol.func"() <{function_type = (!V, ui64, ui64, ui64) -> !I, input_roles = [["P"], ["P"], ["P"], ["P"]], origin = ["main", []], output_roles = [["P"]], roles = ["P"], sym_name = "main"}> ({
    ^bb0(%arg0: !V, %arg1: ui64, %arg2: ui64, %arg3: ui64):
      %0 = "protocol.local_call"(%arg0, %arg1, %arg2, %arg3) <{callee = @work, role = "P", site = "work"}> : (!V, ui64, ui64, ui64) -> !I
      "protocol.return"(%0) : (!I) -> ()
    }) : () -> ()
    func.func private @body(%arg0: !runtime.scope, %arg1: ui64, %arg2: ui64, %arg3: !V, %arg4: ui64, %arg5: ui64, %arg6: ui64) -> !exec.outcome<(ui64)> attributes {no_inline, runtime.origin = ["body", []]} {
      %0 = "exec.apply"(%arg0, %arg1, %arg6) <{binding = @mul, parameters = [], site = "major"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1: ui64):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %1, %arg2) <{binding = @add, parameters = [], site = "value"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%3: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(ui64)>
      return %4 : !exec.outcome<(ui64)>
    ^bb3(%5: ui64):  // pred: ^bb1
      %6 = "exec.returned"(%5) : (ui64) -> !exec.outcome<(ui64)>
      return %6 : !exec.outcome<(ui64)>
    }
    func.func private @predicate(%arg0: !runtime.scope, %arg1: ui64, %arg2: ui64, %arg3: !V, %arg4: ui64, %arg5: ui64, %arg6: ui64) -> !exec.outcome<(i1)> attributes {no_inline, runtime.origin = ["predicate", []]} {
      %0 = "exec.boolean"(%arg0) <{site = "yes", value = true}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1: i1):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (i1) -> !exec.outcome<(i1)>
      return %2 : !exec.outcome<(i1)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(i1)>
      return %4 : !exec.outcome<(i1)>
    }
    func.func @work(%arg0: !runtime.scope, %arg1: !V, %arg2: ui64, %arg3: ui64, %arg4: ui64) -> !exec.outcome<(!I)> attributes {no_inline, runtime.origin = ["work", []]} {
      %0 = "exec.collect"(%arg0, %arg1, %arg2, %arg3, %arg4) <{body = @body, domain = @items, predicate = @predicate, site = "collect"}> : (!runtime.scope, !V, ui64, ui64, ui64) -> !exec.outcome<(!I)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!I)>) -> ()
    ^bb1(%1: !I):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!I) -> !exec.outcome<(!I)>
      return %2 : !exec.outcome<(!I)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!I)>
      return %4 : !exec.outcome<(!I)>
    }
  }) : () -> ()
}
