!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
!M = !algebra.field_matrix<"bls12-381.fr">
module {
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "field.add", implementation = "", sym_name = "add",function_type=(!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "field.mul", implementation = "", sym_name = "mul",function_type=(!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "field.constant", implementation = "", sym_name = "constant",function_type=(!runtime.scope) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>}> : () -> ()
    "data.domain"() <{function_type = (!M, ui64, !V, !V) -> !data.domain<!F, !F, !F>, sym_name = "inner_domain", sym_visibility = "private"}> ({
    ^bb0(%arg0: !M, %arg1: ui64, %arg2: !V, %arg3: !V):
      %0 = "data.domain_matrix_row"(%arg0, %arg1) : (!M, ui64) -> !data.domain<!F>
      %1 = "data.domain_elements"(%arg2) : (!V) -> !data.domain<!F>
      %2 = "data.domain_elements"(%arg3) : (!V) -> !data.domain<!F>
      %3 = "data.domain_zip"(%0, %1, %2) : (!data.domain<!F>, !data.domain<!F>, !data.domain<!F>) -> !data.domain<!F, !F, !F>
      "data.domain_yield"(%3) : (!data.domain<!F, !F, !F>) -> ()
    }) : () -> ()
    "data.domain"() <{function_type = (!M, !V, !V, !M, !V, !F, !F) -> !data.domain<ui64>, sym_name = "outer_domain", sym_visibility = "private"}> ({
    ^bb0(%arg0: !M, %arg1: !V, %arg2: !V, %arg3: !M, %arg4: !V, %arg5: !F, %arg6: !F):
      %0 = "data.domain_indices"(%arg0) <{axis = 0 : i64}> : (!M) -> !data.domain<ui64>
      "data.domain_yield"(%0) : (!data.domain<ui64>) -> ()
    }) : () -> ()
    "protocol.func"() <{function_type = (!M, !V, !V, !M, !V, !F, !F) -> !V, input_roles = [["P"], ["P"], ["P"], ["P"], ["P"], ["P"], ["P"]], origin = ["main", []], output_roles = [["P"]], roles = ["P"], sym_name = "main"}> ({
    ^bb0(%arg0: !M, %arg1: !V, %arg2: !V, %arg3: !M, %arg4: !V, %arg5: !F, %arg6: !F):
      %0 = "protocol.local_call"(%arg0, %arg1, %arg2, %arg3, %arg4, %arg5, %arg6) <{callee = @work, role = "P", site = "work"}> : (!M, !V, !V, !M, !V, !F, !F) -> !V
      "protocol.return"(%0) : (!V) -> ()
    }) : () -> ()
    func.func private @step(%arg0: !runtime.scope, %arg1: !F, %arg2: !F, %arg3: !F, %arg4: !F, %arg5: !M, %arg6: ui64, %arg7: !V, %arg8: !V) -> !exec.outcome<(!F)> attributes {no_inline, runtime.origin = ["step", []]} {
      %0 = "exec.apply"(%arg0, %arg2, %arg3) <{binding = @mul, parameters = [], site = "product"}> : (!runtime.scope, !F, !F) -> !exec.outcome<(!F)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!F)>) -> ()
    ^bb1(%1: !F):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %arg1, %1) <{binding = @add, parameters = [], site = "sum"}> : (!runtime.scope, !F, !F) -> !exec.outcome<(!F)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(!F)>) -> ()
    ^bb2(%3: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!F)>
      return %4 : !exec.outcome<(!F)>
    ^bb3(%5: !F):  // pred: ^bb1
      %6 = "exec.returned"(%5) : (!F) -> !exec.outcome<(!F)>
      return %6 : !exec.outcome<(!F)>
    }
    func.func private @body(%arg0: !runtime.scope, %arg1: ui64, %arg2: !M, %arg3: !V, %arg4: !V, %arg5: !M, %arg6: !V, %arg7: !F, %arg8: !F) -> !exec.outcome<(!F)> attributes {no_inline, runtime.origin = ["body", []]} {
      %0 = "exec.fold"(%arg0, %arg2, %arg1, %arg3, %arg4, %arg7) <{domain = @inner_domain, site = "inner", step = @step}> : (!runtime.scope, !M, ui64, !V, !V, !F) -> !exec.outcome<(!F)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!F)>) -> ()
    ^bb1(%1: !F):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!F) -> !exec.outcome<(!F)>
      return %2 : !exec.outcome<(!F)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!F)>
      return %4 : !exec.outcome<(!F)>
    }
    func.func @work(%arg0: !runtime.scope, %arg1: !M, %arg2: !V, %arg3: !V, %arg4: !M, %arg5: !V, %arg6: !F, %arg7: !F) -> !exec.outcome<(!V)> attributes {no_inline, runtime.origin = ["work", []]} {
      %0 = "exec.collect"(%arg0, %arg1, %arg2, %arg3, %arg4, %arg5, %arg6, %arg7) <{body = @body, domain = @outer_domain, site = "collect"}> : (!runtime.scope, !M, !V, !V, !M, !V, !F, !F) -> !exec.outcome<(!V)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!V)>) -> ()
    ^bb1(%1: !V):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!V) -> !exec.outcome<(!V)>
      return %2 : !exec.outcome<(!V)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!V)>
      return %4 : !exec.outcome<(!V)>
    }
  }) : () -> ()
}
