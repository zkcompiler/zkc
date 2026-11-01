!F = !algebra.field<"bls12-381.fr">
!V = !data.field_vector<"bls12-381.fr">
!S = !runtime.scope
module {
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "data.domain"() <{function_type = (!V) -> !data.domain<!F>, sym_name = "items", sym_visibility = "private"}> ({
    ^bb0(%arg0: !V):
      %0 = "data.domain_elements"(%arg0) : (!V) -> !data.domain<!F>
      "data.domain_yield"(%0) : (!data.domain<!F>) -> ()
    }) : () -> ()
    "protocol.func"() <{function_type = (!V, !F, !F, i1) -> (!F, !F), input_roles = [["P"], ["P"], ["P"], ["P"]], origin = ["main", []], output_roles = [["P"], ["P"]], roles = ["P"], sym_name = "main"}> ({
    ^bb0(%arg0: !V, %arg1: !F, %arg2: !F, %arg3: i1):
      %0:2 = "protocol.local_call"(%arg0, %arg1, %arg2, %arg3) <{callee = @work, role = "P", site = "work"}> : (!V, !F, !F, i1) -> (!F, !F)
      "protocol.return"(%0#0, %0#1) : (!F, !F) -> ()
    }) : () -> ()
    func.func private @step(%arg0: !S, %arg1: !F, %arg2: !F, %arg3: !F, %arg4: !V, %arg5: i1) -> !exec.outcome<(!F, !F)> attributes {no_inline, runtime.origin = ["step", []]} {
      %0 = "exec.test"(%arg0, %arg5) <{site = "outer"}> : (!S, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1: i1):
      cf.cond_br %1, ^bb3, ^bb4
    ^bb2(%2: !exec.stop):
      %3 = "exec.failed"(%2) : (!exec.stop) -> !exec.outcome<(!F, !F)>
      return %3 : !exec.outcome<(!F, !F)>
    ^bb3:
      %4 = "runtime.enter_scope"(%arg0, %arg1, %arg2, %arg3, %arg5) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 4>, selection = "then", site = "outer"}> : (!S, !F, !F, !F, i1) -> !exec.outcome<(!S)>
      "exec.dispatch"(%4)[^bb6, ^bb2] : (!exec.outcome<(!S)>) -> ()
    ^bb4:
      %5 = "runtime.enter_scope"(%arg0, %arg1, %arg2, %arg3, %arg5) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 4>, selection = "else", site = "outer"}> : (!S, !F, !F, !F, i1) -> !exec.outcome<(!S)>
      "exec.dispatch"(%5)[^bb9, ^bb2] : (!exec.outcome<(!S)>) -> ()
    ^bb5(%6: !F, %7: !F):
      %8 = "exec.returned"(%6, %7) : (!F, !F) -> !exec.outcome<(!F, !F)>
      return %8 : !exec.outcome<(!F, !F)>
    ^bb6(%9: !S):
      %10 = call @control_0(%9, %arg1, %arg2, %arg3, %arg5) : (!S, !F, !F, !F, i1) -> !exec.outcome<(!F, !F)>
      %11 = "runtime.exit_scope"(%9, %10) : (!S, !exec.outcome<(!F, !F)>) -> !exec.outcome<(!runtime.transfer<(!F, !F)>)>
      "exec.dispatch"(%11)[^bb7, ^bb2] : (!exec.outcome<(!runtime.transfer<(!F, !F)>)>) -> ()
    ^bb7(%12: !runtime.transfer<(!F, !F)>):
      %13 = "runtime.accept_transfer"(%arg0, %12) : (!S, !runtime.transfer<(!F, !F)>) -> !exec.outcome<(!F, !F)>
      "exec.dispatch"(%13)[^bb8, ^bb2] : (!exec.outcome<(!F, !F)>) -> ()
    ^bb8(%14: !F, %15: !F):
      cf.br ^bb5(%14, %15 : !F, !F)
    ^bb9(%16: !S):
      %17 = call @control_3(%16, %arg1, %arg2, %arg3, %arg5) : (!S, !F, !F, !F, i1) -> !exec.outcome<(!F, !F)>
      %18 = "runtime.exit_scope"(%16, %17) : (!S, !exec.outcome<(!F, !F)>) -> !exec.outcome<(!runtime.transfer<(!F, !F)>)>
      "exec.dispatch"(%18)[^bb10, ^bb2] : (!exec.outcome<(!runtime.transfer<(!F, !F)>)>) -> ()
    ^bb10(%19: !runtime.transfer<(!F, !F)>):
      %20 = "runtime.accept_transfer"(%arg0, %19) : (!S, !runtime.transfer<(!F, !F)>) -> !exec.outcome<(!F, !F)>
      "exec.dispatch"(%20)[^bb11, ^bb2] : (!exec.outcome<(!F, !F)>) -> ()
    ^bb11(%21: !F, %22: !F):
      cf.br ^bb5(%21, %22 : !F, !F)
    }
    func.func private @control_0(%arg0: !S, %arg1: !F, %arg2: !F, %arg3: !F, %arg4: i1) -> !exec.outcome<(!F, !F)> attributes {no_inline, runtime.region} {
      %0 = "exec.test"(%arg0, %arg4) <{site = "inner"}> : (!S, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1: i1):
      cf.cond_br %1, ^bb3, ^bb4
    ^bb2(%2: !exec.stop):
      %3 = "exec.failed"(%2) : (!exec.stop) -> !exec.outcome<(!F, !F)>
      return %3 : !exec.outcome<(!F, !F)>
    ^bb3:
      %4 = "runtime.enter_scope"(%arg0, %arg1, %arg2, %arg3) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "then", site = "inner"}> : (!S, !F, !F, !F) -> !exec.outcome<(!S)>
      "exec.dispatch"(%4)[^bb6, ^bb2] : (!exec.outcome<(!S)>) -> ()
    ^bb4:
      %5 = "runtime.enter_scope"(%arg0, %arg1, %arg2, %arg3) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "else", site = "inner"}> : (!S, !F, !F, !F) -> !exec.outcome<(!S)>
      "exec.dispatch"(%5)[^bb9, ^bb2] : (!exec.outcome<(!S)>) -> ()
    ^bb5(%6: !F, %7: !F):
      %8 = "exec.complete"(%arg0, %6, %7) : (!S, !F, !F) -> !exec.outcome<(!F, !F)>
      return %8 : !exec.outcome<(!F, !F)>
    ^bb6(%9: !S):
      %10 = call @control_1(%9, %arg1, %arg2, %arg3) : (!S, !F, !F, !F) -> !exec.outcome<(!F, !F)>
      %11 = "runtime.exit_scope"(%9, %10) : (!S, !exec.outcome<(!F, !F)>) -> !exec.outcome<(!runtime.transfer<(!F, !F)>)>
      "exec.dispatch"(%11)[^bb7, ^bb2] : (!exec.outcome<(!runtime.transfer<(!F, !F)>)>) -> ()
    ^bb7(%12: !runtime.transfer<(!F, !F)>):
      %13 = "runtime.accept_transfer"(%arg0, %12) : (!S, !runtime.transfer<(!F, !F)>) -> !exec.outcome<(!F, !F)>
      "exec.dispatch"(%13)[^bb8, ^bb2] : (!exec.outcome<(!F, !F)>) -> ()
    ^bb8(%14: !F, %15: !F):
      cf.br ^bb5(%14, %15 : !F, !F)
    ^bb9(%16: !S):
      %17 = call @control_2(%16, %arg1, %arg2, %arg3) : (!S, !F, !F, !F) -> !exec.outcome<(!F, !F)>
      %18 = "runtime.exit_scope"(%16, %17) : (!S, !exec.outcome<(!F, !F)>) -> !exec.outcome<(!runtime.transfer<(!F, !F)>)>
      "exec.dispatch"(%18)[^bb10, ^bb2] : (!exec.outcome<(!runtime.transfer<(!F, !F)>)>) -> ()
    ^bb10(%19: !runtime.transfer<(!F, !F)>):
      %20 = "runtime.accept_transfer"(%arg0, %19) : (!S, !runtime.transfer<(!F, !F)>) -> !exec.outcome<(!F, !F)>
      "exec.dispatch"(%20)[^bb11, ^bb2] : (!exec.outcome<(!F, !F)>) -> ()
    ^bb11(%21: !F, %22: !F):
      cf.br ^bb5(%21, %22 : !F, !F)
    }
    func.func private @control_1(%arg0: !S, %arg1: !F, %arg2: !F, %arg3: !F) -> !exec.outcome<(!F, !F)> attributes {no_inline, runtime.region} {
      %0 = "exec.complete"(%arg0, %arg2, %arg3) : (!S, !F, !F) -> !exec.outcome<(!F, !F)>
      return %0 : !exec.outcome<(!F, !F)>
    }
    func.func private @control_2(%arg0: !S, %arg1: !F, %arg2: !F, %arg3: !F) -> !exec.outcome<(!F, !F)> attributes {no_inline, runtime.region} {
      %0 = "exec.complete"(%arg0, %arg1, %arg2) : (!S, !F, !F) -> !exec.outcome<(!F, !F)>
      return %0 : !exec.outcome<(!F, !F)>
    }
    func.func private @control_3(%arg0: !S, %arg1: !F, %arg2: !F, %arg3: !F, %arg4: i1) -> !exec.outcome<(!F, !F)> attributes {no_inline, runtime.region} {
      %0 = "exec.complete"(%arg0, %arg1, %arg2) : (!S, !F, !F) -> !exec.outcome<(!F, !F)>
      return %0 : !exec.outcome<(!F, !F)>
    }
    func.func @work(%arg0: !S, %arg1: !V, %arg2: !F, %arg3: !F, %arg4: i1) -> !exec.outcome<(!F, !F)> attributes {no_inline, runtime.origin = ["work", []]} {
      %0 = "exec.fold"(%arg0, %arg1, %arg2, %arg3, %arg4) <{domain = @items, site = "fold", step = @step}> : (!S, !V, !F, !F, i1) -> !exec.outcome<(!F, !F)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!F, !F)>) -> ()
    ^bb1(%1: !F, %2: !F):
      %3 = "exec.test"(%arg0, %arg4) <{site = "empty"}> : (!S, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%3)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%4: !exec.stop):
      %5 = "exec.failed"(%4) : (!exec.stop) -> !exec.outcome<(!F, !F)>
      return %5 : !exec.outcome<(!F, !F)>
    ^bb3(%6: i1):
      cf.cond_br %6, ^bb4, ^bb5
    ^bb4:
      %7 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "empty"}> : (!S) -> !exec.outcome<(!S)>
      "exec.dispatch"(%7)[^bb7, ^bb2] : (!exec.outcome<(!S)>) -> ()
    ^bb5:
      %8 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "empty"}> : (!S) -> !exec.outcome<(!S)>
      "exec.dispatch"(%8)[^bb10, ^bb2] : (!exec.outcome<(!S)>) -> ()
    ^bb6:
      %9 = "exec.returned"(%1, %2) : (!F, !F) -> !exec.outcome<(!F, !F)>
      return %9 : !exec.outcome<(!F, !F)>
    ^bb7(%10: !S):
      %11 = call @control_4(%10) : (!S) -> !exec.outcome<>
      %12 = "runtime.exit_scope"(%10, %11) : (!S, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%12)[^bb8, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb8(%13: !runtime.transfer<>):
      %14 = "runtime.accept_transfer"(%arg0, %13) : (!S, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%14)[^bb9, ^bb2] : (!exec.outcome<>) -> ()
    ^bb9:
      cf.br ^bb6
    ^bb10(%15: !S):
      %16 = call @control_5(%15) : (!S) -> !exec.outcome<>
      %17 = "runtime.exit_scope"(%15, %16) : (!S, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%17)[^bb11, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb11(%18: !runtime.transfer<>):
      %19 = "runtime.accept_transfer"(%arg0, %18) : (!S, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%19)[^bb12, ^bb2] : (!exec.outcome<>) -> ()
    ^bb12:
      cf.br ^bb6
    }
    func.func private @control_4(%arg0: !S) -> !exec.outcome<> attributes {no_inline, runtime.region} {
      %0 = "exec.complete"(%arg0) : (!S) -> !exec.outcome<>
      return %0 : !exec.outcome<>
    }
    func.func private @control_5(%arg0: !S) -> !exec.outcome<> attributes {no_inline, runtime.region} {
      %0 = "exec.reject"(%arg0) <{reason = "abort", site = "disabled"}> : (!S) -> !exec.stop
      cf.br ^bb1(%0 : !exec.stop)
    ^bb1(%1: !exec.stop):
      %2 = "exec.failed"(%1) : (!exec.stop) -> !exec.outcome<>
      return %2 : !exec.outcome<>
    }
  }) : () -> ()
}
