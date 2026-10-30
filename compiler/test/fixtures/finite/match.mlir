!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
!tag = !data.variant<#data.identity<["atom", "Choice"]>, [#data.alternative<"left">, #data.alternative<"right">]>
module {
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "field.add", implementation = "", sym_name = "add"}> : () -> ()
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
    func.func private @step(%arg0: !runtime.scope, %arg1: !F, %arg2: !F, %arg3: !V) -> !exec.outcome<(!F)> attributes {no_inline, runtime.origin = ["step", []]} {
      %0 = "exec.variant"(%arg0) <{alternative = "left", site = "choice"}> : (!runtime.scope) -> !exec.outcome<(!tag)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!tag)>) -> ()
    ^bb1(%1: !tag):  // pred: ^bb0
      "exec.match"(%arg0, %1, %arg1, %arg2)[^bb2, ^bb4, ^bb5] <{alternatives = ["left", "right"], site = "match"}> : (!runtime.scope, !tag, !F, !F) -> ()
    ^bb2(%2: !exec.stop):  // 8 preds: ^bb0, ^bb1, ^bb4, ^bb5, ^bb6, ^bb7, ^bb9, ^bb10
      %3 = "exec.failed"(%2) : (!exec.stop) -> !exec.outcome<(!F)>
      return %3 : !exec.outcome<(!F)>
    ^bb3(%4: !F):  // 2 preds: ^bb8, ^bb11
      %5 = "exec.returned"(%4) : (!F) -> !exec.outcome<(!F)>
      return %5 : !exec.outcome<(!F)>
    ^bb4(%6: !F, %7: !F):  // pred: ^bb1
      %8 = "runtime.enter_scope"(%arg0, %6, %7) <{kind = "match", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "left", site = "match"}> : (!runtime.scope, !F, !F) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%8)[^bb6, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb5(%9: !F, %10: !F):  // pred: ^bb1
      %11 = "runtime.enter_scope"(%arg0, %9, %10) <{kind = "match", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "right", site = "match"}> : (!runtime.scope, !F, !F) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%11)[^bb9, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6(%12: !runtime.scope):  // pred: ^bb4
      %13 = call @control_0(%12, %6, %7) : (!runtime.scope, !F, !F) -> !exec.outcome<(!F)>
      %14 = "runtime.exit_scope"(%12, %13) : (!runtime.scope, !exec.outcome<(!F)>) -> !exec.outcome<(!runtime.transfer<(!F)>)>
      "exec.dispatch"(%14)[^bb7, ^bb2] : (!exec.outcome<(!runtime.transfer<(!F)>)>) -> ()
    ^bb7(%15: !runtime.transfer<(!F)>):  // pred: ^bb6
      %16 = "runtime.accept_transfer"(%arg0, %15) : (!runtime.scope, !runtime.transfer<(!F)>) -> !exec.outcome<(!F)>
      "exec.dispatch"(%16)[^bb8, ^bb2] : (!exec.outcome<(!F)>) -> ()
    ^bb8(%17: !F):  // pred: ^bb7
      cf.br ^bb3(%17 : !F)
    ^bb9(%18: !runtime.scope):  // pred: ^bb5
      %19 = call @control_1(%18, %9, %10) : (!runtime.scope, !F, !F) -> !exec.outcome<(!F)>
      %20 = "runtime.exit_scope"(%18, %19) : (!runtime.scope, !exec.outcome<(!F)>) -> !exec.outcome<(!runtime.transfer<(!F)>)>
      "exec.dispatch"(%20)[^bb10, ^bb2] : (!exec.outcome<(!runtime.transfer<(!F)>)>) -> ()
    ^bb10(%21: !runtime.transfer<(!F)>):  // pred: ^bb9
      %22 = "runtime.accept_transfer"(%arg0, %21) : (!runtime.scope, !runtime.transfer<(!F)>) -> !exec.outcome<(!F)>
      "exec.dispatch"(%22)[^bb11, ^bb2] : (!exec.outcome<(!F)>) -> ()
    ^bb11(%23: !F):  // pred: ^bb10
      cf.br ^bb3(%23 : !F)
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
      %0 = "exec.reject"(%arg0) <{reason = "reject", site = "stop"}> : (!runtime.scope) -> !exec.stop
      cf.br ^bb1(%0 : !exec.stop)
    ^bb1(%1: !exec.stop):  // pred: ^bb0
      %2 = "exec.failed"(%1) : (!exec.stop) -> !exec.outcome<(!F)>
      return %2 : !exec.outcome<(!F)>
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
