// Ownership fixture only: bound/range admission belongs to the full profile.
!S = !runtime.scope
!F = !algebra.field<"koala-bear">
!T = !runtime.transfer<(!F)>
!C = !runtime.transfer<(i1, !F)>
!R = !exec.outcome<(!F)>
!B = !exec.outcome<(i1, !F)>
!E = !exec.outcome<(!S)>
!H = !exec.outcome<(!C)>
!D = !exec.outcome<(i1, !T)>
module {
  func.func private @step(%context: !S, %value: !F, %again: i1) -> !B attributes {no_inline} {
    %returned = "exec.returned"(%again, %value) : (i1, !F) -> !B
    func.return %returned : !B
  }
  func.func @loop(%parent: !S, %seed: !F, %lower: i64, %upper: i64, %again: i1) -> !R attributes {no_inline} {
    %initial = "runtime.borrow_transfer"(%parent, %seed) : (!S, !F) -> !T
    cf.br ^header(%lower, %initial : i64, !T)
  ^header(%i: i64, %previous: !T):
    %inside = arith.cmpi ult, %i, %upper : i64
    cf.cond_br %inside, ^enter, ^finish(%previous : !T)
  ^enter:
    %value = "runtime.transfer_values"(%previous) : (!T) -> !F
    %entered = "runtime.enter_scope"(%parent, %i, %value, %again) <{operandSegmentSizes=array<i32: 1, 1, 2>, kind="iteration", site="loop"}> : (!S, i64, !F, i1) -> !E
    "exec.dispatch"(%entered)[^body, ^release_failure] : (!E) -> ()
  ^body(%child: !S):
    %result = func.call @step(%child, %value, %again) : (!S, !F, i1) -> !B
    %left = "runtime.exit_scope"(%child, %result) : (!S, !B) -> !H
    "exec.dispatch"(%left)[^replace, ^release_failure] : (!H) -> ()
  ^replace(%returned: !C):
    "runtime.release_transfer"(%previous) : (!T) -> ()
    %test = "runtime.take_condition"(%returned) : (!C) -> !D
    "exec.dispatch"(%test)[^latch, ^failed] : (!D) -> ()
  ^latch(%continue: i1, %carried: !T):
    cf.cond_br %continue, ^increment(%carried : !T), ^finish(%carried : !T)
  ^increment(%advanced: !T):
    %one = arith.constant 1 : i64
    %next = arith.addi %i, %one : i64
    cf.br ^header(%next, %advanced : i64, !T)
  ^finish(%final: !T):
    %accepted = "runtime.accept_transfer"(%parent, %final) : (!S, !T) -> !R
    func.return %accepted : !R
  ^release_failure(%failure: !exec.stop):
    "runtime.release_transfer"(%previous) : (!T) -> ()
    %released = "exec.failed"(%failure) : (!exec.stop) -> !R
    func.return %released : !R
  ^failed(%cause: !exec.stop):
    %stopped = "exec.failed"(%cause) : (!exec.stop) -> !R
    func.return %stopped : !R
  }
}
