!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
module {
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "field.mul", implementation = "", sym_name = "mul"}> : () -> ()
    "data.domain"() <{function_type = (!V) -> !data.domain<!F>, sym_name = "items", sym_visibility = "private"}> ({
    ^bb0(%arg0: !V):
      %0 = "data.domain_elements"(%arg0) : (!V) -> !data.domain<!F>
      "data.domain_yield"(%0) : (!data.domain<!F>) -> ()
    }) : () -> ()
    "protocol.func"() <{function_type = (!V) -> !V, input_roles = [["P"]], origin = ["main", []], output_roles = [["P"]], roles = ["P"], sym_name = "main"}> ({
    ^bb0(%arg0: !V):
      %0 = "protocol.local_call"(%arg0) <{callee = @work, role = "P", site = "work"}> : (!V) -> !V
      "protocol.return"(%0) : (!V) -> ()
    }) : () -> ()
    func.func private @square(%arg0: !runtime.scope, %arg1: !F, %arg2: !V) -> !exec.outcome<(!F)> attributes {no_inline, runtime.origin = ["square", []]} {
      %0 = "exec.apply"(%arg0, %arg1, %arg1) <{binding = @mul, parameters = [], site = "square"}> : (!runtime.scope, !F, !F) -> !exec.outcome<(!F)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!F)>) -> ()
    ^bb1(%1: !F):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!F) -> !exec.outcome<(!F)>
      return %2 : !exec.outcome<(!F)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!F)>
      return %4 : !exec.outcome<(!F)>
    }
    func.func @work(%arg0: !runtime.scope, %arg1: !V) -> !exec.outcome<(!V)> attributes {no_inline, runtime.origin = ["work", []]} {
      %0 = "exec.collect"(%arg0, %arg1) <{body = @square, domain = @items, site = "collect"}> : (!runtime.scope, !V) -> !exec.outcome<(!V)>
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
