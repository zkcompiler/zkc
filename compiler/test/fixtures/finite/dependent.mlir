!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
module {
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "data.domain"() <{function_type = (!V, !V, !V) -> !data.domain<!F>, sym_name = "outer", sym_visibility = "private"}> ({
    ^bb0(%arg0: !V, %arg1: !V, %arg2: !V):
      %0 = "data.domain_elements"(%arg0) : (!V) -> !data.domain<!F>
      "data.domain_yield"(%0) : (!data.domain<!F>) -> ()
    }) : () -> ()
    "data.domain"() <{function_type = (!V, !V) -> !data.domain<!F, !F>, sym_name = "inner", sym_visibility = "private"}> ({
    ^bb0(%arg0: !V, %arg1: !V):
      %0 = "data.domain_elements"(%arg0) : (!V) -> !data.domain<!F>
      %1 = "data.domain_elements"(%arg1) : (!V) -> !data.domain<!F>
      %2 = "data.domain_zip"(%0, %1) : (!data.domain<!F>, !data.domain<!F>) -> !data.domain<!F, !F>
      "data.domain_yield"(%2) : (!data.domain<!F, !F>) -> ()
    }) : () -> ()
    "protocol.func"() <{function_type = (!V, !V, !V, !F) -> !F, input_roles = [["P"], ["P"], ["P"], ["P"]], origin = ["main", []], output_roles = [["P"]], roles = ["P"], sym_name = "main"}> ({
    ^bb0(%arg0: !V, %arg1: !V, %arg2: !V, %arg3: !F):
      %0 = "protocol.local_call"(%arg0, %arg1, %arg2, %arg3) <{callee = @work, role = "P", site = "work"}> : (!V, !V, !V, !F) -> !F
      "protocol.return"(%0) : (!F) -> ()
    }) : () -> ()
    func.func private @inside(%arg0: !runtime.scope, %arg1: !F, %arg2: !F, %arg3: !F, %arg4: !V, %arg5: !V) -> !exec.outcome<(!F)> attributes {no_inline, runtime.origin = ["inside", []]} {
      %0 = "exec.returned"(%arg1) : (!F) -> !exec.outcome<(!F)>
      return %0 : !exec.outcome<(!F)>
    }
    func.func private @outside(%arg0: !runtime.scope, %arg1: !F, %arg2: !F, %arg3: !V, %arg4: !V, %arg5: !V) -> !exec.outcome<(!F)> attributes {no_inline, runtime.origin = ["outside", []]} {
      %0 = "exec.fold"(%arg0, %arg4, %arg5, %arg1) <{domain = @inner, site = "inner", step = @inside}> : (!runtime.scope, !V, !V, !F) -> !exec.outcome<(!F)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!F)>) -> ()
    ^bb1(%1: !F):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!F) -> !exec.outcome<(!F)>
      return %2 : !exec.outcome<(!F)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!F)>
      return %4 : !exec.outcome<(!F)>
    }
    func.func @work(%arg0: !runtime.scope, %arg1: !V, %arg2: !V, %arg3: !V, %arg4: !F) -> !exec.outcome<(!F)> attributes {no_inline, runtime.origin = ["work", []]} {
      %0 = "exec.fold"(%arg0, %arg1, %arg2, %arg3, %arg4) <{domain = @outer, site = "fold", step = @outside}> : (!runtime.scope, !V, !V, !V, !F) -> !exec.outcome<(!F)>
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
