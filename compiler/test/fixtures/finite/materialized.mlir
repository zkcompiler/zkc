!F = !algebra.field<"bls12-381.fr">
!V = !data.field_vector<"bls12-381.fr">
module {
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "field.add", implementation = "", sym_name = "add",function_type=(!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>}> : () -> ()
    "data.domain"() <{function_type = (!V) -> !data.domain<!F>, sym_name = "items", sym_visibility = "private"}> ({
    ^bb0(%arg0: !V):
      %0 = "data.domain_elements"(%arg0) : (!V) -> !data.domain<!F>
      "data.domain_yield"(%0) : (!data.domain<!F>) -> ()
    }) : () -> ()
    "protocol.func"() <{function_type = (!V, !F) -> !F, input_roles = [["P"], ["P"]], origin = ["main", []], output_roles = [["P"]], roles = ["P"], sym_name = "main"}> ({
    ^bb0(%arg0: !V, %arg1: !F):
      %0 = "protocol.local_call"(%arg0, %arg1) <{callee = @work, role = "P", site = "work"}> : (!V, !F) -> !F
      "protocol.return"(%0) : (!F) -> ()
    }) : () -> ()
    func.func private @body(%arg0: !runtime.scope, %arg1: !F, %arg2: !V) -> !exec.outcome<(!F)> attributes {no_inline, runtime.origin = ["body", []]} {
      %0 = "exec.reject"(%arg0) <{reason = "abort", site = "body"}> : (!runtime.scope) -> !exec.stop
      cf.br ^bb1(%0 : !exec.stop)
    ^bb1(%1: !exec.stop):  // pred: ^bb0
      %2 = "exec.failed"(%1) : (!exec.stop) -> !exec.outcome<(!F)>
      return %2 : !exec.outcome<(!F)>
    }
    func.func private @reduce(%arg0: !runtime.scope, %arg1: !V, %arg2: !F) -> !exec.outcome<(!F)> attributes {no_inline, runtime.origin = ["reduce", []]} {
      %0 = "exec.reject"(%arg0) <{reason = "reject", site = "reducer"}> : (!runtime.scope) -> !exec.stop
      cf.br ^bb1(%0 : !exec.stop)
    ^bb1(%1: !exec.stop):  // pred: ^bb0
      %2 = "exec.failed"(%1) : (!exec.stop) -> !exec.outcome<(!F)>
      return %2 : !exec.outcome<(!F)>
    }
    func.func @work(%arg0: !runtime.scope, %arg1: !V, %arg2: !F) -> !exec.outcome<(!F)> attributes {no_inline, runtime.origin = ["work", []]} {
      %0 = "exec.collect"(%arg0, %arg1) <{body = @body, domain = @items, site = "collect"}> : (!runtime.scope, !V) -> !exec.outcome<(!V)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!V)>) -> ()
    ^bb1(%1: !V):  // pred: ^bb0
      %2 = call @reduce(%arg0, %1, %arg2) {runtime.site = "reduce"} : (!runtime.scope, !V, !F) -> !exec.outcome<(!F)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(!F)>) -> ()
    ^bb2(%3: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!F)>
      return %4 : !exec.outcome<(!F)>
    ^bb3(%5: !F):  // pred: ^bb1
      %6 = "exec.returned"(%5) : (!F) -> !exec.outcome<(!F)>
      return %6 : !exec.outcome<(!F)>
    }
  }) : () -> ()
}
