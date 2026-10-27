!S = !runtime.scope
!F = !algebra.field<"koala-bear">
!T = !runtime.transfer<(!F)>
!C = !runtime.transfer<(i1, !F)>
!R = !exec.outcome<(!F)>
!B = !exec.outcome<(i1, !F)>
!E = !exec.outcome<(!S)>
!H = !exec.outcome<(!C)>
!D = !exec.outcome<(i1, !T)>
!A = !exec.outcome<(i64, i64)>
!I = !exec.outcome<(ui64)>
module {
  func.func private @step(%scope: !S, %i: ui64, %value: !F, %again: i1) -> !B attributes {no_inline, runtime.region} {
    %returned = "exec.complete"(%scope, %again, %value) : (!S, i1, !F) -> !B
    func.return %returned : !B
  }
  func.func @loop(%scope: !S, %lower: ui64, %upper: ui64, %seed: !F, %again: i1) -> !R attributes {no_inline, runtime.origin=["loop", []]} {
    %range = "exec.range"(%scope, %lower, %upper) {site="iterate"} : (!S, ui64, ui64) -> !A
    "exec.dispatch"(%range)[^admitted, ^failed] : (!A) -> ()
  ^admitted(%low: i64, %high: i64):
    %initial = "runtime.borrow_transfer"(%scope, %seed) : (!S, !F) -> !T
    cf.br ^header(%low, %initial : i64, !T)
  ^header(%i: i64, %previous: !T):
    %inside = arith.cmpi ult, %i, %high : i64
    cf.cond_br %inside, ^iteration, ^finish(%previous : !T)
  ^iteration:
    %allocated = "runtime.iteration"(%scope, %i) {site="iterate"} : (!S, i64) -> !I
    "exec.dispatch"(%allocated)[^enter, ^release_failure] : (!I) -> ()
  ^enter(%index: ui64):
    %value = "runtime.transfer_values"(%previous) : (!T) -> !F
    %entered = "runtime.enter_scope"(%scope, %i, %index, %value, %again) <{operandSegmentSizes=array<i32: 1, 1, 3>, kind="iteration", site="iterate"}> : (!S, i64, ui64, !F, i1) -> !E
    "exec.dispatch"(%entered)[^body, ^release_failure] : (!E) -> ()
  ^body(%child: !S):
    %result = func.call @step(%child, %index, %value, %again) : (!S, ui64, !F, i1) -> !B
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
    %accepted = "runtime.accept_transfer"(%scope, %final) : (!S, !T) -> !R
    "exec.dispatch"(%accepted)[^done, ^failed] : (!R) -> ()
  ^done(%final_value: !F):
    %complete = "exec.complete"(%scope, %final_value) : (!S, !F) -> !R
    func.return %complete : !R
  ^release_failure(%failure: !exec.stop):
    "runtime.release_transfer"(%previous) : (!T) -> ()
    cf.br ^failed(%failure : !exec.stop)
  ^failed(%cause: !exec.stop):
    %stopped = "exec.failed"(%cause) : (!exec.stop) -> !R
    func.return %stopped : !R
  }
}
