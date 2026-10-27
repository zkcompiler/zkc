!S = !runtime.scope
!F = !algebra.field<"koala-bear">
!V = !data.variant<"variant:5b227a6b632e76617269616e742f30222c5b22457865637574696f6e5061796c6f6164222c22736f6d65222c226669656c643a6b6f616c612d62656172222c5b2232225d2c5b2231222c2233225d2c5b2234225d2c5b2230222c2235225d5d5d">
!R = !exec.outcome<(!F)>
!E = !exec.outcome<(!S)>
!T = !runtime.transfer<(!F)>
!H = !exec.outcome<(!T)>
module {
  func.func private @payload(%scope: !S, %value: !F, %capture: !F) -> !R attributes {no_inline, runtime.region} {
    %returned = "exec.complete"(%scope, %value) : (!S, !F) -> !R
    func.return %returned : !R
  }
  func.func @select(%scope: !S, %input: !V, %capture: !F) -> !R attributes {no_inline, runtime.origin=["select", []]} {
    "exec.match"(%scope, %input, %capture)[^failed, ^some] {alternatives=["some"], site="select"} : (!S, !V, !F) -> ()
  ^some(%value: !F, %captured: !F):
    %entered = "runtime.enter_scope"(%scope, %value, %captured) <{operandSegmentSizes=array<i32: 1, 0, 2>, kind="match", site="select", selection="some"}> : (!S, !F, !F) -> !E
    "exec.dispatch"(%entered)[^body, ^failed] : (!E) -> ()
  ^body(%child: !S):
    %result = func.call @payload(%child, %value, %captured) : (!S, !F, !F) -> !R
    %left = "runtime.exit_scope"(%child, %result) : (!S, !R) -> !H
    "exec.dispatch"(%left)[^accept, ^failed] : (!H) -> ()
  ^accept(%held: !T):
    %accepted = "runtime.accept_transfer"(%scope, %held) : (!S, !T) -> !R
    "exec.dispatch"(%accepted)[^next, ^failed] : (!R) -> ()
  ^next(%selected: !F):
    cf.br ^join(%selected : !F)
  ^join(%joined: !F):
    %returned = "exec.complete"(%scope, %joined) : (!S, !F) -> !R
    func.return %returned : !R
  ^failed(%cause: !exec.stop):
    %failure = "exec.failed"(%cause) : (!exec.stop) -> !R
    func.return %failure : !R
  }
}
