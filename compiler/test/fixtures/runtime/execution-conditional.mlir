!S = !runtime.scope
!F = !algebra.field<"koala-bear">
!R = !exec.outcome<(!F)>
!D = !exec.outcome<(i1)>
!E = !exec.outcome<(!S)>
!T = !runtime.transfer<(!F)>
!H = !exec.outcome<(!T)>
module {
  "local.binding"() {sym_name="add", contract="field.add", arguments=["koala-bear"], implementation=""} : () -> ()
  "local.binding"() {sym_name="multiply", contract="field.mul", arguments=["koala-bear"], implementation=""} : () -> ()
  func.func private @yes(%scope: !S, %x: !F, %y: !F) -> !R attributes {no_inline, runtime.region} {
    %applied = "exec.apply"(%scope, %x, %y) {binding=@add, parameters=[], site="sum"} : (!S, !F, !F) -> !R
    "exec.dispatch"(%applied)[^success, ^failed] : (!R) -> ()
  ^success(%sum: !F):
    %complete = "exec.complete"(%scope, %sum) : (!S, !F) -> !R
    func.return %complete : !R
  ^failed(%cause: !exec.stop):
    %failure = "exec.failed"(%cause) : (!exec.stop) -> !R
    func.return %failure : !R
  }
  func.func private @no(%scope: !S, %x: !F, %y: !F) -> !R attributes {no_inline, runtime.region} {
    %rejected = "exec.reject"(%scope) {reason="refused", site="reject"} : (!S) -> !exec.stop
    cf.br ^failed(%rejected : !exec.stop)
  ^failed(%cause: !exec.stop):
    %failure = "exec.failed"(%cause) : (!exec.stop) -> !R
    func.return %failure : !R
  }
  func.func @work(%scope: !S, %condition: i1, %x: !F, %y: !F) -> !R attributes {no_inline, runtime.origin=["work", []]} {
    %tested = "exec.test"(%scope, %condition) {site="choose"} : (!S, i1) -> !D
    "exec.dispatch"(%tested)[^decide, ^failed] : (!D) -> ()
  ^decide(%decision: i1):
    cf.cond_br %decision, ^yes, ^no
  ^yes:
    %entered_yes = "runtime.enter_scope"(%scope, %x, %y) <{operandSegmentSizes=array<i32: 1, 0, 2>, kind="conditional", site="choose", selection="then"}> : (!S, !F, !F) -> !E
    "exec.dispatch"(%entered_yes)[^body_yes, ^failed] : (!E) -> ()
  ^body_yes(%child_yes: !S):
    %result_yes = func.call @yes(%child_yes, %x, %y) : (!S, !F, !F) -> !R
    %left_yes = "runtime.exit_scope"(%child_yes, %result_yes) : (!S, !R) -> !H
    "exec.dispatch"(%left_yes)[^accept_yes, ^failed] : (!H) -> ()
  ^accept_yes(%held_yes: !T):
    %accepted_yes = "runtime.accept_transfer"(%scope, %held_yes) : (!S, !T) -> !R
    "exec.dispatch"(%accepted_yes)[^next_yes, ^failed] : (!R) -> ()
  ^next_yes(%yes_value: !F):
    cf.br ^join(%yes_value : !F)
  ^no:
    %entered_no = "runtime.enter_scope"(%scope, %x, %y) <{operandSegmentSizes=array<i32: 1, 0, 2>, kind="conditional", site="choose", selection="else"}> : (!S, !F, !F) -> !E
    "exec.dispatch"(%entered_no)[^body_no, ^failed] : (!E) -> ()
  ^body_no(%child_no: !S):
    %result_no = func.call @no(%child_no, %x, %y) : (!S, !F, !F) -> !R
    %left_no = "runtime.exit_scope"(%child_no, %result_no) : (!S, !R) -> !H
    "exec.dispatch"(%left_no)[^accept_no, ^failed] : (!H) -> ()
  ^accept_no(%held_no: !T):
    %accepted_no = "runtime.accept_transfer"(%scope, %held_no) : (!S, !T) -> !R
    "exec.dispatch"(%accepted_no)[^next_no, ^failed] : (!R) -> ()
  ^next_no(%no_value: !F):
    cf.br ^join(%no_value : !F)
  ^join(%value: !F):
    %complete = "exec.complete"(%scope, %value) : (!S, !F) -> !R
    func.return %complete : !R
  ^failed(%cause: !exec.stop):
    %failure = "exec.failed"(%cause) : (!exec.stop) -> !R
    func.return %failure : !R
  }
}
