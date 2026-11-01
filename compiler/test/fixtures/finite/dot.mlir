!F = !algebra.field<"bls12-381.fr">
!V = !data.field_vector<"bls12-381.fr">
module {
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "field.add", implementation = "", sym_name = "add",function_type=(!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "field.mul", implementation = "", sym_name = "mul",function_type=(!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>}> : () -> ()
    "data.domain"() <{function_type = (!V, !V, !V) -> !data.domain<!F, !F, !F>, sym_name = "items", sym_visibility = "private"}> ({
    ^bb0(%arg0: !V, %arg1: !V, %arg2: !V):
      %0 = "data.domain_elements"(%arg0) : (!V) -> !data.domain<!F>
      %1 = "data.domain_elements"(%arg1) : (!V) -> !data.domain<!F>
      %2 = "data.domain_elements"(%arg2) : (!V) -> !data.domain<!F>
      %3 = "data.domain_zip"(%0, %1, %2) : (!data.domain<!F>, !data.domain<!F>, !data.domain<!F>) -> !data.domain<!F, !F, !F>
      "data.domain_yield"(%3) : (!data.domain<!F, !F, !F>) -> ()
    }) : () -> ()
    "protocol.func"() <{function_type = (!V, !V, !V, !F) -> !F, input_roles = [["P"], ["P"], ["P"], ["P"]], origin = ["main", []], output_roles = [["P"]], roles = ["P"], sym_name = "main"}> ({
    ^bb0(%arg0: !V, %arg1: !V, %arg2: !V, %arg3: !F):
      %0 = "protocol.local_call"(%arg0, %arg1, %arg2, %arg3) <{callee = @work, role = "P", site = "work"}> : (!V, !V, !V, !F) -> !F
      "protocol.return"(%0) : (!F) -> ()
    }) : () -> ()
    func.func private @step(%arg0: !runtime.scope, %arg1: !F, %arg2: !F, %arg3: !F, %arg4: !F, %arg5: !V, %arg6: !V, %arg7: !V) -> !exec.outcome<(!F)> attributes {no_inline, runtime.origin = ["step", []]} {
      %0 = "exec.apply"(%arg0, %arg2, %arg3) <{binding = @mul, parameters = [], site = "term"}> : (!runtime.scope, !F, !F) -> !exec.outcome<(!F)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!F)>) -> ()
    ^bb1(%1: !F):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %arg1, %1) <{binding = @add, parameters = [], site = "add"}> : (!runtime.scope, !F, !F) -> !exec.outcome<(!F)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(!F)>) -> ()
    ^bb2(%3: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!F)>
      return %4 : !exec.outcome<(!F)>
    ^bb3(%5: !F):  // pred: ^bb1
      %6 = "exec.returned"(%5) : (!F) -> !exec.outcome<(!F)>
      return %6 : !exec.outcome<(!F)>
    }
    func.func @work(%arg0: !runtime.scope, %arg1: !V, %arg2: !V, %arg3: !V, %arg4: !F) -> !exec.outcome<(!F)> attributes {no_inline, runtime.origin = ["work", []]} {
      %0 = "exec.fold"(%arg0, %arg1, %arg2, %arg3, %arg4) <{domain = @items, site = "fold", step = @step}> : (!runtime.scope, !V, !V, !V, !F) -> !exec.outcome<(!F)>
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
