!F = !algebra.field<"bls12-381.fr">
!S = !data.sequence<i1>
module {
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "field.add", implementation = "", sym_name = "add"}> : () -> ()
    "data.domain"() <{function_type = (!S) -> !data.domain<i1>, sym_name = "items", sym_visibility = "private"}> ({
    ^bb0(%arg0: !S):
      %0 = "data.domain_elements"(%arg0) : (!S) -> !data.domain<i1>
      "data.domain_yield"(%0) : (!data.domain<i1>) -> ()
    }) : () -> ()
    "protocol.func"() <{function_type = (i1, i1, !F, !F) -> !F, input_roles = [["P"], ["P"], ["P"], ["P"]], origin = ["main", []], output_roles = [["P"]], roles = ["P"], sym_name = "main"}> ({
    ^bb0(%arg0: i1, %arg1: i1, %arg2: !F, %arg3: !F):
      %0 = "data.sequence_empty"() : () -> !S
      %1 = "data.sequence_append"(%0, %arg0) : (!S, i1) -> !S
      %2 = "data.sequence_append"(%1, %arg1) : (!S, i1) -> !S
      %3 = "protocol.local_call"(%2, %arg2, %arg3) <{callee = @work, role = "P", site = "work"}> : (!S, !F, !F) -> !F
      "protocol.return"(%3) : (!F) -> ()
    }) : () -> ()
    func.func private @step(%arg0: !runtime.scope, %arg1: !F, %arg2: i1, %arg3: !S, %arg4: !F) -> !exec.outcome<(!F)> attributes {no_inline, runtime.origin = ["step", []]} {
      %0 = "exec.test"(%arg0, %arg2) <{site = "take"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1: i1):  // pred: ^bb0
      cf.cond_br %1, ^bb3, ^bb4
    ^bb2(%2: !exec.stop):  // 7 preds: ^bb0, ^bb3, ^bb4, ^bb6, ^bb7, ^bb9, ^bb10
      %3 = "exec.failed"(%2) : (!exec.stop) -> !exec.outcome<(!F)>
      return %3 : !exec.outcome<(!F)>
    ^bb3:  // pred: ^bb1
      %4 = "runtime.enter_scope"(%arg0, %arg1, %arg4) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "then", site = "take"}> : (!runtime.scope, !F, !F) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%4)[^bb6, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb4:  // pred: ^bb1
      %5 = "runtime.enter_scope"(%arg0, %arg1, %arg4) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "else", site = "take"}> : (!runtime.scope, !F, !F) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%5)[^bb9, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb5(%6: !F):  // 2 preds: ^bb8, ^bb11
      %7 = "exec.returned"(%6) : (!F) -> !exec.outcome<(!F)>
      return %7 : !exec.outcome<(!F)>
    ^bb6(%8: !runtime.scope):  // pred: ^bb3
      %9 = call @control_0(%8, %arg1, %arg4) : (!runtime.scope, !F, !F) -> !exec.outcome<(!F)>
      %10 = "runtime.exit_scope"(%8, %9) : (!runtime.scope, !exec.outcome<(!F)>) -> !exec.outcome<(!runtime.transfer<(!F)>)>
      "exec.dispatch"(%10)[^bb7, ^bb2] : (!exec.outcome<(!runtime.transfer<(!F)>)>) -> ()
    ^bb7(%11: !runtime.transfer<(!F)>):  // pred: ^bb6
      %12 = "runtime.accept_transfer"(%arg0, %11) : (!runtime.scope, !runtime.transfer<(!F)>) -> !exec.outcome<(!F)>
      "exec.dispatch"(%12)[^bb8, ^bb2] : (!exec.outcome<(!F)>) -> ()
    ^bb8(%13: !F):  // pred: ^bb7
      cf.br ^bb5(%13 : !F)
    ^bb9(%14: !runtime.scope):  // pred: ^bb4
      %15 = call @control_1(%14, %arg1, %arg4) : (!runtime.scope, !F, !F) -> !exec.outcome<(!F)>
      %16 = "runtime.exit_scope"(%14, %15) : (!runtime.scope, !exec.outcome<(!F)>) -> !exec.outcome<(!runtime.transfer<(!F)>)>
      "exec.dispatch"(%16)[^bb10, ^bb2] : (!exec.outcome<(!runtime.transfer<(!F)>)>) -> ()
    ^bb10(%17: !runtime.transfer<(!F)>):  // pred: ^bb9
      %18 = "runtime.accept_transfer"(%arg0, %17) : (!runtime.scope, !runtime.transfer<(!F)>) -> !exec.outcome<(!F)>
      "exec.dispatch"(%18)[^bb11, ^bb2] : (!exec.outcome<(!F)>) -> ()
    ^bb11(%19: !F):  // pred: ^bb10
      cf.br ^bb5(%19 : !F)
    }
    func.func private @control_0(%arg0: !runtime.scope, %arg1: !F, %arg2: !F) -> !exec.outcome<(!F)> attributes {no_inline, runtime.region} {
      %0 = "exec.apply"(%arg0, %arg1, %arg2) <{binding = @add, parameters = [], site = "add"}> : (!runtime.scope, !F, !F) -> !exec.outcome<(!F)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!F)>) -> ()
    ^bb1(%1: !F):  // pred: ^bb0
      %2 = "exec.complete"(%arg0, %1) : (!runtime.scope, !F) -> !exec.outcome<(!F)>
      return %2 : !exec.outcome<(!F)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!F)>
      return %4 : !exec.outcome<(!F)>
    }
    func.func private @control_1(%arg0: !runtime.scope, %arg1: !F, %arg2: !F) -> !exec.outcome<(!F)> attributes {no_inline, runtime.region} {
      %0 = "exec.complete"(%arg0, %arg1) : (!runtime.scope, !F) -> !exec.outcome<(!F)>
      return %0 : !exec.outcome<(!F)>
    }
    func.func @work(%arg0: !runtime.scope, %arg1: !S, %arg2: !F, %arg3: !F) -> !exec.outcome<(!F)> attributes {no_inline, runtime.origin = ["work", []]} {
      %0 = "exec.fold"(%arg0, %arg1, %arg2, %arg3) <{domain = @items, site = "fold", step = @step}> : (!runtime.scope, !S, !F, !F) -> !exec.outcome<(!F)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!F)>) -> ()
    ^bb1(%1: !F):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!F) -> !exec.outcome<(!F)>
      return %2 : !exec.outcome<(!F)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!F)>
      return %4 : !exec.outcome<(!F)>
    }
  }) : () -> ()
}
