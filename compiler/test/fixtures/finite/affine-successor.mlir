!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
!R = !runtime.capability<rng, "bls12-381.fr">
module {
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "random.draw", implementation = "", sym_name = "random"}> : () -> ()
    "data.domain"() <{function_type = (!V) -> !data.domain<!F>, sym_name = "items", sym_visibility = "private"}> ({
    ^bb0(%arg0: !V):
      %0 = "data.domain_elements"(%arg0) : (!V) -> !data.domain<!F>
      "data.domain_yield"(%0) : (!data.domain<!F>) -> ()
    }) : () -> ()
    "protocol.func"() <{function_type = (!V, !R, !R) -> (!R, !R), input_roles = [["P"], ["P"], ["P"]], origin = ["main", []], output_roles = [["P"], ["P"]], roles = ["P"], sym_name = "main"}> ({
    ^bb0(%arg0: !V, %arg1: !R, %arg2: !R):
      %0:2 = "protocol.local_call"(%arg0, %arg1, %arg2) <{callee = @work, role = "P", site = "work"}> : (!V, !R, !R) -> (!R, !R)
      "protocol.return"(%0#0, %0#1) : (!R, !R) -> ()
    }) : () -> ()
    func.func private @step(%arg0: !runtime.scope, %arg1: !R, %arg2: !R, %arg3: !F, %arg4: !V) -> !exec.outcome<(!R, !R)> attributes {no_inline, runtime.origin = ["step", []]} {
      %0 = "exec.apply"(%arg0, %arg1) <{binding = @random, parameters = [], site = "sample"}> : (!runtime.scope, !R) -> !exec.outcome<(!F, !R)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!F, !R)>) -> ()
    ^bb1(%1: !F, %2: !R):  // pred: ^bb0
      %3 = "exec.returned"(%2, %arg2) : (!R, !R) -> !exec.outcome<(!R, !R)>
      return %3 : !exec.outcome<(!R, !R)>
    ^bb2(%4: !exec.stop):  // pred: ^bb0
      %5 = "exec.failed"(%4) : (!exec.stop) -> !exec.outcome<(!R, !R)>
      return %5 : !exec.outcome<(!R, !R)>
    }
    func.func @work(%arg0: !runtime.scope, %arg1: !V, %arg2: !R, %arg3: !R) -> !exec.outcome<(!R, !R)> attributes {no_inline, runtime.origin = ["work", []]} {
      %0 = "exec.fold"(%arg0, %arg1, %arg2, %arg3) <{domain = @items, site = "fold", step = @step}> : (!runtime.scope, !V, !R, !R) -> !exec.outcome<(!R, !R)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!R, !R)>) -> ()
    ^bb1(%1: !R, %2: !R):  // pred: ^bb0
      %3 = "exec.returned"(%1, %2) : (!R, !R) -> !exec.outcome<(!R, !R)>
      return %3 : !exec.outcome<(!R, !R)>
    ^bb2(%4: !exec.stop):  // pred: ^bb0
      %5 = "exec.failed"(%4) : (!exec.stop) -> !exec.outcome<(!R, !R)>
      return %5 : !exec.outcome<(!R, !R)>
    }
  }) : () -> ()
}
