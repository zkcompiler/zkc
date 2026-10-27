!S = !runtime.scope
!T = !runtime.transfer<(i1)>
!R = !exec.outcome<(i1)>
!E = !exec.outcome<(!S)>
!H = !exec.outcome<(!T)>
module {
  func.func private @body(%context: !S, %value: i1) -> !R attributes {no_inline} {
    %returned = "exec.returned"(%value) : (i1) -> !R
    func.return %returned : !R
  }
  func.func @work(%parent: !S, %value: i1) -> !R attributes {no_inline} {
    %entered = "runtime.enter_scope"(%parent, %value) <{operandSegmentSizes=array<i32: 1, 0, 1>, kind="function", site="helper", callee=@body}> : (!S, i1) -> !E
    "exec.dispatch"(%entered)[^body, ^failed] : (!E) -> ()
  ^body(%child: !S):
    %result = func.call @body(%child, %value) : (!S, i1) -> !R
    %left = "runtime.exit_scope"(%child, %result) : (!S, !R) -> !H
    "exec.dispatch"(%left)[^accept, ^failed] : (!H) -> ()
  ^accept(%held: !T):
    %output = "runtime.accept_transfer"(%parent, %held) : (!S, !T) -> !R
    func.return %output : !R
  ^failed(%cause: !exec.stop):
    %stopped = "exec.failed"(%cause) : (!exec.stop) -> !R
    func.return %stopped : !R
  }
}
