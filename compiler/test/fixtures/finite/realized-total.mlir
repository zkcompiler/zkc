!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
module {
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "data.domain"() <{function_type = (!V) -> !data.domain<!F>, sym_name = "items", sym_visibility = "private"}> ({
    ^bb0(%arg0: !V):
      %0 = "data.domain_elements"(%arg0) : (!V) -> !data.domain<!F>
      "data.domain_yield"(%0) : (!data.domain<!F>) -> ()
    }) : () -> ()
    func.func private @inside(%arg0: !F, %arg1: !F, %arg2: !V) -> !F {
      %0 = algebra.field_add %arg0, %arg1 : (!F, !F) -> !F
      return %0 : !F
    }
    func.func private @outside(%arg0: !F, %arg1: !F, %arg2: !V) -> !F {
      %0 = "algebra.finite_fold"(%arg2, %arg0) <{domain = @items, step = @inside}> : (!V, !F) -> !F
      return %0 : !F
    }
    func.func private @total(%arg0: !V, %arg1: !F) -> !F {
      %0 = "algebra.finite_fold"(%arg0, %arg1) <{domain = @items, step = @outside}> : (!V, !F) -> !F
      return %0 : !F
    }
    "protocol.func"() <{function_type = (!V, !F) -> !F, input_roles = [["P"], ["P"]], origin = ["main", []], output_roles = [["P"]], roles = ["P"], sym_name = "main"}> ({
    ^bb0(%arg0: !V, %arg1: !F):
      %0 = "protocol.local_call"(%arg0, %arg1) <{callee = @work, role = "P", site = "work"}> : (!V, !F) -> !F
      "protocol.return"(%0) : (!F) -> ()
    }) : () -> ()
    func.func @work(%arg0: !runtime.scope, %arg1: !V, %arg2: !F) -> !exec.outcome<(!F)> attributes {no_inline, runtime.origin = ["work", []]} {
      %0 = "exec.compute"(%arg0, %arg1, %arg2) <{callee = @total, site = "realized"}> : (!runtime.scope, !V, !F) -> !exec.outcome<(!F)>
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
