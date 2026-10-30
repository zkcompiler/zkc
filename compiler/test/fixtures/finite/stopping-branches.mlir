!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
module {
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "field.add", implementation = "", sym_name = "add",function_type=(!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>}> : () -> ()
    "data.domain"() <{function_type = (!V) -> !data.domain<!F>, sym_name = "items", sym_visibility = "private"}> ({
    ^bb0(%arg0: !V):
      %0 = "data.domain_elements"(%arg0) : (!V) -> !data.domain<!F>
      "data.domain_yield"(%0) : (!data.domain<!F>) -> ()
    }) : () -> ()
    "protocol.func"() <{function_type = (!V, !F) -> !F, input_roles = [["P"], ["P"]], origin = ["main", []], output_roles = [["P"]], roles = ["P"], sym_name = "main"}> ({
    ^bb0(%arg0: !V, %arg1: !F):
      %0 = "protocol.local_call"(%arg0, %arg1) <{callee = @work, role = "P", site = "work"}> : (!V, !F) -> !F
      "protocol.return"(%0) : (!F) -> ()
    }) : () -> ()
    func.func private @halt(%arg0: !runtime.scope, %arg1: !F) -> !exec.outcome<(!F)> attributes {no_inline, runtime.origin = ["halt", []]} {
      %0 = "exec.reject"(%arg0) <{reason = "abort", site = "halt"}> : (!runtime.scope) -> !exec.stop
      cf.br ^bb1(%0 : !exec.stop)
    ^bb1(%1: !exec.stop):  // pred: ^bb0
      %2 = "exec.failed"(%1) : (!exec.stop) -> !exec.outcome<(!F)>
      return %2 : !exec.outcome<(!F)>
    }
    func.func private @step(%arg0: !runtime.scope, %arg1: !F, %arg2: !F, %arg3: !V) -> !exec.outcome<(!F)> attributes {no_inline, runtime.origin = ["step", []]} {
      %0 = "exec.boolean"(%arg0) <{site = "yes", value = true}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1: i1):  // pred: ^bb0
      %2 = "exec.test"(%arg0, %1) <{site = "branch"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%3: !exec.stop):  // 8 preds: ^bb0, ^bb1, ^bb4, ^bb5, ^bb7, ^bb8, ^bb10, ^bb11
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!F)>
      return %4 : !exec.outcome<(!F)>
    ^bb3(%5: i1):  // pred: ^bb1
      cf.cond_br %5, ^bb4, ^bb5
    ^bb4:  // pred: ^bb3
      %6 = "runtime.enter_scope"(%arg0, %arg1) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "then", site = "branch"}> : (!runtime.scope, !F) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%6)[^bb7, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb5:  // pred: ^bb3
      %7 = "runtime.enter_scope"(%arg0, %arg1) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "else", site = "branch"}> : (!runtime.scope, !F) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%7)[^bb10, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6(%8: !F):  // 2 preds: ^bb9, ^bb12
      %9 = "exec.returned"(%8) : (!F) -> !exec.outcome<(!F)>
      return %9 : !exec.outcome<(!F)>
    ^bb7(%10: !runtime.scope):  // pred: ^bb4
      %11 = call @control_0(%10, %arg1) : (!runtime.scope, !F) -> !exec.outcome<(!F)>
      %12 = "runtime.exit_scope"(%10, %11) : (!runtime.scope, !exec.outcome<(!F)>) -> !exec.outcome<(!runtime.transfer<(!F)>)>
      "exec.dispatch"(%12)[^bb8, ^bb2] : (!exec.outcome<(!runtime.transfer<(!F)>)>) -> ()
    ^bb8(%13: !runtime.transfer<(!F)>):  // pred: ^bb7
      %14 = "runtime.accept_transfer"(%arg0, %13) : (!runtime.scope, !runtime.transfer<(!F)>) -> !exec.outcome<(!F)>
      "exec.dispatch"(%14)[^bb9, ^bb2] : (!exec.outcome<(!F)>) -> ()
    ^bb9(%15: !F):  // pred: ^bb8
      cf.br ^bb6(%15 : !F)
    ^bb10(%16: !runtime.scope):  // pred: ^bb5
      %17 = call @control_1(%16, %arg1) : (!runtime.scope, !F) -> !exec.outcome<(!F)>
      %18 = "runtime.exit_scope"(%16, %17) : (!runtime.scope, !exec.outcome<(!F)>) -> !exec.outcome<(!runtime.transfer<(!F)>)>
      "exec.dispatch"(%18)[^bb11, ^bb2] : (!exec.outcome<(!runtime.transfer<(!F)>)>) -> ()
    ^bb11(%19: !runtime.transfer<(!F)>):  // pred: ^bb10
      %20 = "runtime.accept_transfer"(%arg0, %19) : (!runtime.scope, !runtime.transfer<(!F)>) -> !exec.outcome<(!F)>
      "exec.dispatch"(%20)[^bb12, ^bb2] : (!exec.outcome<(!F)>) -> ()
    ^bb12(%21: !F):  // pred: ^bb11
      cf.br ^bb6(%21 : !F)
    }
    func.func private @control_0(%arg0: !runtime.scope, %arg1: !F) -> !exec.outcome<(!F)> attributes {no_inline, runtime.region} {
      %0 = call @halt(%arg0, %arg1) {runtime.site = "left"} : (!runtime.scope, !F) -> !exec.outcome<(!F)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!F)>) -> ()
    ^bb1(%1: !F):  // pred: ^bb0
      %2 = "exec.complete"(%arg0, %1) : (!runtime.scope, !F) -> !exec.outcome<(!F)>
      return %2 : !exec.outcome<(!F)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!F)>
      return %4 : !exec.outcome<(!F)>
    }
    func.func private @control_1(%arg0: !runtime.scope, %arg1: !F) -> !exec.outcome<(!F)> attributes {no_inline, runtime.region} {
      %0 = call @halt(%arg0, %arg1) {runtime.site = "right"} : (!runtime.scope, !F) -> !exec.outcome<(!F)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!F)>) -> ()
    ^bb1(%1: !F):  // pred: ^bb0
      %2 = "exec.complete"(%arg0, %1) : (!runtime.scope, !F) -> !exec.outcome<(!F)>
      return %2 : !exec.outcome<(!F)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!F)>
      return %4 : !exec.outcome<(!F)>
    }
    func.func @work(%arg0: !runtime.scope, %arg1: !V, %arg2: !F) -> !exec.outcome<(!F)> attributes {no_inline, runtime.origin = ["work", []]} {
      %0 = "exec.fold"(%arg0, %arg1, %arg2) <{domain = @items, site = "fold", step = @step}> : (!runtime.scope, !V, !F) -> !exec.outcome<(!F)>
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
