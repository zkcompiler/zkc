!F = !algebra.field<"bls12-381.fr">
!G = !algebra.group<"bls12-381.g1">
!V = !algebra.field_vector<"bls12-381.fr">
!GS = !algebra.group_vector<"bls12-381.g1">
module {
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "runtime.binding"() <{arguments = ["bls12-381.g1"], contract = "curve.generator", implementation = "", sym_name = "generator"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.g1"], contract = "curve.empty", implementation = "", sym_name = "empty"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.g1"], contract = "curve.append", implementation = "", sym_name = "append"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.g1"], contract = "curve.scale", implementation = "", sym_name = "scale"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.g1"], contract = "curve.add", implementation = "", sym_name = "add"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.g1"], contract = "curve.equal", implementation = "", sym_name = "equal"}> : () -> ()
    "data.domain"() <{function_type = (!GS, !V) -> !data.domain<!G, !F>, sym_name = "items", sym_visibility = "private"}> ({
    ^bb0(%arg0: !GS, %arg1: !V):
      %0 = "data.domain_elements"(%arg0) : (!GS) -> !data.domain<!G>
      %1 = "data.domain_elements"(%arg1) : (!V) -> !data.domain<!F>
      %2 = "data.domain_zip"(%0, %1) : (!data.domain<!G>, !data.domain<!F>) -> !data.domain<!G, !F>
      "data.domain_yield"(%2) : (!data.domain<!G, !F>) -> ()
    }) : () -> ()
    "protocol.func"() <{function_type = (!V, !F, !F) -> i1, input_roles = [["P"], ["P"], ["P"]], origin = ["main", []], output_roles = [["P"]], roles = ["P"], sym_name = "main"}> ({
    ^bb0(%arg0: !V, %arg1: !F, %arg2: !F):
      %0 = "protocol.local_call"(%arg0, %arg1, %arg2) <{callee = @work, role = "P", site = "work"}> : (!V, !F, !F) -> i1
      "protocol.return"(%0) : (i1) -> ()
    }) : () -> ()
    func.func private @step(%arg0: !runtime.scope, %arg1: !G, %arg2: !G, %arg3: !F, %arg4: !GS, %arg5: !V) -> !exec.outcome<(!G)> attributes {no_inline, runtime.origin = ["step", []]} {
      %0 = "exec.apply"(%arg0, %arg2, %arg3) <{binding = @scale, parameters = [], site = "term"}> : (!runtime.scope, !G, !F) -> !exec.outcome<(!G)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!G)>) -> ()
    ^bb1(%1: !G):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %arg1, %1) <{binding = @add, parameters = [], site = "add"}> : (!runtime.scope, !G, !G) -> !exec.outcome<(!G)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(!G)>) -> ()
    ^bb2(%3: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!G)>
      return %4 : !exec.outcome<(!G)>
    ^bb3(%5: !G):  // pred: ^bb1
      %6 = "exec.returned"(%5) : (!G) -> !exec.outcome<(!G)>
      return %6 : !exec.outcome<(!G)>
    }
    func.func @work(%arg0: !runtime.scope, %arg1: !V, %arg2: !F, %arg3: !F) -> !exec.outcome<(i1)> attributes {no_inline, runtime.origin = ["work", []]} {
      %0 = "exec.apply"(%arg0) <{binding = @generator, parameters = [], site = "generator"}> : (!runtime.scope) -> !exec.outcome<(!G)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!G)>) -> ()
    ^bb1(%1: !G):  // pred: ^bb0
      %2 = "exec.apply"(%arg0) <{binding = @empty, parameters = [], site = "empty"}> : (!runtime.scope) -> !exec.outcome<(!GS)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(!GS)>) -> ()
    ^bb2(%3: !exec.stop):  // 8 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb8
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(i1)>
      return %4 : !exec.outcome<(i1)>
    ^bb3(%5: !GS):  // pred: ^bb1
      %6 = "exec.apply"(%arg0, %5, %1) <{binding = @append, parameters = [], site = "one"}> : (!runtime.scope, !GS, !G) -> !exec.outcome<(!GS)>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<(!GS)>) -> ()
    ^bb4(%7: !GS):  // pred: ^bb3
      %8 = "exec.apply"(%arg0, %7, %1) <{binding = @append, parameters = [], site = "two"}> : (!runtime.scope, !GS, !G) -> !exec.outcome<(!GS)>
      "exec.dispatch"(%8)[^bb5, ^bb2] : (!exec.outcome<(!GS)>) -> ()
    ^bb5(%9: !GS):  // pred: ^bb4
      %10 = "exec.apply"(%arg0, %1, %arg2) <{binding = @scale, parameters = [], site = "init"}> : (!runtime.scope, !G, !F) -> !exec.outcome<(!G)>
      "exec.dispatch"(%10)[^bb6, ^bb2] : (!exec.outcome<(!G)>) -> ()
    ^bb6(%11: !G):  // pred: ^bb5
      %12 = "exec.fold"(%arg0, %9, %arg1, %11) <{domain = @items, site = "fold", step = @step}> : (!runtime.scope, !GS, !V, !G) -> !exec.outcome<(!G)>
      "exec.dispatch"(%12)[^bb7, ^bb2] : (!exec.outcome<(!G)>) -> ()
    ^bb7(%13: !G):  // pred: ^bb6
      %14 = "exec.apply"(%arg0, %1, %arg3) <{binding = @scale, parameters = [], site = "expected"}> : (!runtime.scope, !G, !F) -> !exec.outcome<(!G)>
      "exec.dispatch"(%14)[^bb8, ^bb2] : (!exec.outcome<(!G)>) -> ()
    ^bb8(%15: !G):  // pred: ^bb7
      %16 = "exec.apply"(%arg0, %13, %15) <{binding = @equal, parameters = [], site = "equal"}> : (!runtime.scope, !G, !G) -> !exec.outcome<(i1)>
      "exec.dispatch"(%16)[^bb9, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb9(%17: i1):  // pred: ^bb8
      %18 = "exec.returned"(%17) : (i1) -> !exec.outcome<(i1)>
      return %18 : !exec.outcome<(i1)>
    }
  }) : () -> ()
}
