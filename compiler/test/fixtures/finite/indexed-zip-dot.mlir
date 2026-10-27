module {
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.get", implementation = "", sym_name = "get"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "field.add", implementation = "", sym_name = "add"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "field.mul", implementation = "", sym_name = "mul"}> : () -> ()
    "data.domain"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !data.domain<ui64, ui64>, sym_name = "items", sym_visibility = "private"}> ({
    ^bb0(%arg0: !algebra.field_vector<"bls12-381.fr">, %arg1: !algebra.field_vector<"bls12-381.fr">):
      %0 = "data.domain_indices"(%arg0) <{axis = 0 : i64}> : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<ui64>
      %1 = "data.domain_indices"(%arg1) <{axis = 0 : i64}> : (!algebra.field_vector<"bls12-381.fr">) -> !data.domain<ui64>
      %2 = "data.domain_zip"(%0, %1) : (!data.domain<ui64>, !data.domain<ui64>) -> !data.domain<ui64, ui64>
      "data.domain_yield"(%2) : (!data.domain<ui64, ui64>) -> ()
    }) : () -> ()
    "protocol.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, input_roles = [["P"], ["P"], ["P"]], origin = ["main", []], output_roles = [["P"]], roles = ["P"], sym_name = "main"}> ({
    ^bb0(%arg0: !algebra.field_vector<"bls12-381.fr">, %arg1: !algebra.field_vector<"bls12-381.fr">, %arg2: !algebra.field<"bls12-381.fr">):
      %0 = "protocol.local_call"(%arg0, %arg1, %arg2) <{callee = @work, role = "P", site = "work"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "protocol.return"(%0) : (!algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    func.func private @step(%arg0: !runtime.scope, %arg1: !algebra.field<"bls12-381.fr">, %arg2: ui64, %arg3: ui64, %arg4: !algebra.field_vector<"bls12-381.fr">, %arg5: !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)> attributes {no_inline, runtime.origin = ["step", []]} {
      %0 = "exec.apply"(%arg0, %arg4, %arg2) <{binding = @get, parameters = [], site = "x"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%1: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %arg5, %arg2) <{binding = @get, parameters = [], site = "y"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb2(%3: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      return %4 : !exec.outcome<(!algebra.field<"bls12-381.fr">)>
    ^bb3(%5: !algebra.field<"bls12-381.fr">):  // pred: ^bb1
      %6 = "exec.apply"(%arg0, %1, %5) <{binding = @mul, parameters = [], site = "p"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb4(%7: !algebra.field<"bls12-381.fr">):  // pred: ^bb3
      %8 = "exec.apply"(%arg0, %7, %arg1) <{binding = @add, parameters = [], site = "r"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%8)[^bb5, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb5(%9: !algebra.field<"bls12-381.fr">):  // pred: ^bb4
      %10 = "exec.returned"(%9) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      return %10 : !exec.outcome<(!algebra.field<"bls12-381.fr">)>
    }
    func.func @work(%arg0: !runtime.scope, %arg1: !algebra.field_vector<"bls12-381.fr">, %arg2: !algebra.field_vector<"bls12-381.fr">, %arg3: !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)> attributes {no_inline, runtime.origin = ["work", []]} {
      %0 = "exec.fold"(%arg0, %arg1, %arg2, %arg3) <{domain = @items, site = "fold", step = @step}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%1: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      return %2 : !exec.outcome<(!algebra.field<"bls12-381.fr">)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      return %4 : !exec.outcome<(!algebra.field<"bls12-381.fr">)>
    }
  }) : () -> ()
}
