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
!P = !exec.outcome<(!T)>
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
    %packaged = "exec.returned"(%initial) : (!T) -> !P
    %true = arith.constant true
    %coordinate, %continuation, %final = scf.while (%i = %low, %running = %true, %state = %packaged) : (i64, i1, !P) -> (i64, i1, !P) {
      %inside = arith.cmpi ult, %i, %high : i64
      %proceed = arith.andi %running, %inside : i1
      scf.condition(%proceed) %i, %running, %state : i64, i1, !P
    } do {
    ^bb0(%i: i64, %running: i1, %state: !P):
      %continue, %updated = scf.execute_region -> (i1, !P) no_inline {
        "exec.dispatch"(%state)[^iteration, ^stopped] : (!P) -> ()
      ^iteration(%previous: !T):
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
        "exec.dispatch"(%test)[^latch, ^stopped] : (!D) -> ()
      ^latch(%decision: i1, %carried: !T):
        %next = "exec.returned"(%carried) : (!T) -> !P
        scf.yield %decision, %next : i1, !P
      ^release_failure(%failure: !exec.stop):
        "runtime.release_transfer"(%previous) : (!T) -> ()
        cf.br ^stopped(%failure : !exec.stop)
      ^stopped(%cause: !exec.stop):
        %stop = "exec.failed"(%cause) : (!exec.stop) -> !P
        %false = arith.constant false
        scf.yield %false, %stop : i1, !P
      }
      %one = arith.constant 1 : i64
      %next = arith.addi %i, %one : i64
      scf.yield %next, %continue, %updated : i64, i1, !P
    }
    "exec.dispatch"(%final)[^accept, ^failed] : (!P) -> ()
  ^accept(%held: !T):
    %accepted = "runtime.accept_transfer"(%scope, %held) : (!S, !T) -> !R
    "exec.dispatch"(%accepted)[^done, ^failed] : (!R) -> ()
  ^done(%final_value: !F):
    %complete = "exec.complete"(%scope, %final_value) : (!S, !F) -> !R
    func.return %complete : !R
  ^failed(%cause: !exec.stop):
    %stopped = "exec.failed"(%cause) : (!exec.stop) -> !R
    func.return %stopped : !R
  }
}
