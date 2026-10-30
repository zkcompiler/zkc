!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
!M = !algebra.field_matrix<"bls12-381.fr">
module {
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "matrix.get", implementation = "", sym_name = "get",function_type=(!runtime.scope, !algebra.field_matrix<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>}> : () -> ()
    "data.domain"() <{function_type = (!M) -> !data.domain<ui64, ui64>, sym_name = "items", sym_visibility = "private"}> ({
    ^bb0(%arg0: !M):
      %0 = "data.domain_matrix_coordinates"(%arg0) <{order = "row_major"}> : (!M) -> !data.domain<ui64, ui64>
      "data.domain_yield"(%0) : (!data.domain<ui64, ui64>) -> ()
    }) : () -> ()
    "protocol.func"() <{function_type = (!M) -> !V, input_roles = [["P"]], origin = ["main", []], output_roles = [["P"]], roles = ["P"], sym_name = "main"}> ({
    ^bb0(%arg0: !M):
      %0 = "protocol.local_call"(%arg0) <{callee = @work, role = "P", site = "work"}> : (!M) -> !V
      "protocol.return"(%0) : (!V) -> ()
    }) : () -> ()
    func.func private @body(%arg0: !runtime.scope, %arg1: ui64, %arg2: ui64, %arg3: !M) -> !exec.outcome<(!F)> attributes {no_inline, runtime.origin = ["body", []]} {
      %0 = "exec.apply"(%arg0, %arg3, %arg1, %arg2) <{binding = @get, parameters = [], site = "get"}> : (!runtime.scope, !M, ui64, ui64) -> !exec.outcome<(!F)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!F)>) -> ()
    ^bb1(%1: !F):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!F) -> !exec.outcome<(!F)>
      return %2 : !exec.outcome<(!F)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!F)>
      return %4 : !exec.outcome<(!F)>
    }
    func.func @work(%arg0: !runtime.scope, %arg1: !M) -> !exec.outcome<(!V)> attributes {no_inline, runtime.origin = ["work", []]} {
      %0 = "exec.collect"(%arg0, %arg1) <{body = @body, domain = @items, site = "collect"}> : (!runtime.scope, !M) -> !exec.outcome<(!V)>
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
