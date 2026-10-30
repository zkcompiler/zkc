!S = !runtime.scope
!F = !algebra.field<"koala-bear">
!O = !exec.outcome<(!F)>
module {
  "runtime.binding"() {sym_name = "add", contract = "field.add", arguments = ["koala-bear"], implementation = "",function_type=(!runtime.scope, !algebra.field<"koala-bear">, !algebra.field<"koala-bear">) -> !exec.outcome<(!algebra.field<"koala-bear">)>} : () -> ()
  "runtime.binding"() {sym_name = "subtract", contract = "field.sub", arguments = ["koala-bear"], implementation = "",function_type=(!runtime.scope, !algebra.field<"koala-bear">, !algebra.field<"koala-bear">) -> !exec.outcome<(!algebra.field<"koala-bear">)>} : () -> ()
  func.func @caller(%scope: !S, %a: !F, %b: !F) -> !O attributes {no_inline, runtime.origin = ["caller", []]} {
    %call = func.call @sum(%scope, %a, %b) {runtime.site = "sum_site"} : (!S, !F, !F) -> !O
    "exec.dispatch"(%call)[^next, ^failed] : (!O) -> ()
  ^next(%sum: !F):
    %identity = func.call @identity(%scope, %sum) {runtime.site = "identity_site"} : (!S, !F) -> !O
    "exec.dispatch"(%identity)[^done, ^failed] : (!O) -> ()
  ^done(%value: !F):
    %result = "exec.returned"(%value) : (!F) -> !O
    return %result : !O
  ^failed(%cause: !exec.stop):
    %failure = "exec.failed"(%cause) : (!exec.stop) -> !O
    return %failure : !O
  }
  func.func @sum(%scope: !S, %a: !F, %b: !F) -> !O attributes {no_inline, runtime.origin = ["sum", []]} {
    %add = "exec.apply"(%scope, %a, %b) {binding = @add, parameters = [], site = "add_site"} : (!S, !F, !F) -> !O
    "exec.dispatch"(%add)[^done, ^failed] : (!O) -> ()
  ^done(%sum: !F):
    %result = "exec.returned"(%sum) : (!F) -> !O
    return %result : !O
  ^failed(%cause: !exec.stop):
    %failure = "exec.failed"(%cause) : (!exec.stop) -> !O
    return %failure : !O
  }
  func.func @difference(%scope: !S, %a: !F, %b: !F) -> !O attributes {no_inline, runtime.origin = ["difference", []]} {
    %sub = "exec.apply"(%scope, %a, %b) {binding = @subtract, parameters = [], site = "sub_site"} : (!S, !F, !F) -> !O
    "exec.dispatch"(%sub)[^done, ^failed] : (!O) -> ()
  ^done(%difference: !F):
    %result = "exec.returned"(%difference) : (!F) -> !O
    return %result : !O
  ^failed(%cause: !exec.stop):
    %failure = "exec.failed"(%cause) : (!exec.stop) -> !O
    return %failure : !O
  }
  func.func @identity(%scope: !S, %value: !F) -> !O attributes {no_inline, runtime.origin = ["identity", []]} {
    %result = "exec.returned"(%value) : (!F) -> !O
    return %result : !O
  }
}
