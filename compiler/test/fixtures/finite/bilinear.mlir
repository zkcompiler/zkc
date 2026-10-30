!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
!M = !algebra.field_matrix<"bls12-381.fr">
module {
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "matrix.get", implementation = "", sym_name = "get",function_type=(!runtime.scope, !algebra.field_matrix<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "field.add", implementation = "", sym_name = "add",function_type=(!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "field.mul", implementation = "", sym_name = "mul",function_type=(!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>}> : () -> ()
    "data.domain"() <{function_type = (!M, !V, !V) -> !data.domain<ui64, !F, ui64, !F>, sym_name = "items", sym_visibility = "private"}> ({
    ^bb0(%arg0: !M, %arg1: !V, %arg2: !V):
      %0 = "data.domain_indices"(%arg0) <{axis = 0 : i64}> : (!M) -> !data.domain<ui64>
      %1 = "data.domain_indices"(%arg0) <{axis = 1 : i64}> : (!M) -> !data.domain<ui64>
      %2 = "data.domain_elements"(%arg1) : (!V) -> !data.domain<!F>
      %3 = "data.domain_elements"(%arg2) : (!V) -> !data.domain<!F>
      %4 = "data.domain_zip"(%0, %2) : (!data.domain<ui64>, !data.domain<!F>) -> !data.domain<ui64, !F>
      %5 = "data.domain_zip"(%1, %3) : (!data.domain<ui64>, !data.domain<!F>) -> !data.domain<ui64, !F>
      %6 = "data.domain_product"(%4, %5) : (!data.domain<ui64, !F>, !data.domain<ui64, !F>) -> !data.domain<ui64, !F, ui64, !F>
      "data.domain_yield"(%6) : (!data.domain<ui64, !F, ui64, !F>) -> ()
    }) : () -> ()
    "protocol.func"() <{function_type = (!M, !V, !V, !F) -> !F, input_roles = [["P"], ["P"], ["P"], ["P"]], origin = ["main", []], output_roles = [["P"]], roles = ["P"], sym_name = "main"}> ({
    ^bb0(%arg0: !M, %arg1: !V, %arg2: !V, %arg3: !F):
      %0 = "protocol.local_call"(%arg0, %arg1, %arg2, %arg3) <{callee = @work, role = "P", site = "work"}> : (!M, !V, !V, !F) -> !F
      "protocol.return"(%0) : (!F) -> ()
    }) : () -> ()
    func.func private @step(%arg0: !runtime.scope, %arg1: !F, %arg2: ui64, %arg3: !F, %arg4: ui64, %arg5: !F, %arg6: !M, %arg7: !V, %arg8: !V) -> !exec.outcome<(!F)> attributes {no_inline, runtime.origin = ["step", []]} {
      %0 = "exec.apply"(%arg0, %arg6, %arg2, %arg4) <{binding = @get, parameters = [], site = "get"}> : (!runtime.scope, !M, ui64, ui64) -> !exec.outcome<(!F)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!F)>) -> ()
    ^bb1(%1: !F):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %arg3, %1) <{binding = @mul, parameters = [], site = "left"}> : (!runtime.scope, !F, !F) -> !exec.outcome<(!F)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(!F)>) -> ()
    ^bb2(%3: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!F)>
      return %4 : !exec.outcome<(!F)>
    ^bb3(%5: !F):  // pred: ^bb1
      %6 = "exec.apply"(%arg0, %5, %arg5) <{binding = @mul, parameters = [], site = "right"}> : (!runtime.scope, !F, !F) -> !exec.outcome<(!F)>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<(!F)>) -> ()
    ^bb4(%7: !F):  // pred: ^bb3
      %8 = "exec.apply"(%arg0, %arg1, %7) <{binding = @add, parameters = [], site = "add"}> : (!runtime.scope, !F, !F) -> !exec.outcome<(!F)>
      "exec.dispatch"(%8)[^bb5, ^bb2] : (!exec.outcome<(!F)>) -> ()
    ^bb5(%9: !F):  // pred: ^bb4
      %10 = "exec.returned"(%9) : (!F) -> !exec.outcome<(!F)>
      return %10 : !exec.outcome<(!F)>
    }
    func.func @work(%arg0: !runtime.scope, %arg1: !M, %arg2: !V, %arg3: !V, %arg4: !F) -> !exec.outcome<(!F)> attributes {no_inline, runtime.origin = ["work", []]} {
      %0 = "exec.fold"(%arg0, %arg1, %arg2, %arg3, %arg4) <{domain = @items, site = "fold", step = @step}> : (!runtime.scope, !M, !V, !V, !F) -> !exec.outcome<(!F)>
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
