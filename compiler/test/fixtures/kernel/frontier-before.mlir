!F = !algebra.field<"bls12-381.fr">
module { "protocol.module"() ({
  module @first_unit attributes {exec.computation} {
    func.func @evaluate(%a: !F, %b: !F, %ok: i1, %other: i1) -> (!F, !F, !F) {
      %g = algebra.field_multiply %a, %b : (!F, !F) -> !F
      %h = algebra.field_multiply %b, %a : (!F, !F) -> !F
      %c0 = algebra.field_subtract %a, %b : (!F, !F) -> !F
      %c1 = algebra.field_subtract %a, %b : (!F, !F) -> !F
      %dead = algebra.field_subtract %a, %b : (!F, !F) -> !F
      %v = algebra.field_add %g, %c0 : (!F, !F) -> !F
      %u = algebra.field_add %h, %c1 : (!F, !F) -> !F
      func.return %v, %u, %c1 : !F, !F, !F
    }
  }
  module @second_unit attributes {exec.computation} {
    func.func @evaluate(%a: !F, %b: !F, %ok: i1, %other: i1) -> (!F, !F, !F) {
      %g = algebra.field_multiply %a, %b : (!F, !F) -> !F
      %identical = algebra.field_multiply %a, %b : (!F, !F) -> !F
      %c0 = algebra.field_subtract %a, %b : (!F, !F) -> !F
      %c1 = algebra.field_subtract %a, %b : (!F, !F) -> !F
      %v = algebra.field_add %g, %c0 : (!F, !F) -> !F
      func.return %v, %c0, %c1 : !F, !F, !F
    }
  }
  func.func private @first_yes(%scope: !runtime.scope) -> !exec.outcome<> attributes {no_inline, runtime.region} {
    %r = "exec.complete"(%scope) : (!runtime.scope) -> !exec.outcome<>
    return %r : !exec.outcome<>
  }
  func.func private @first_no(%scope: !runtime.scope) -> !exec.outcome<> attributes {no_inline, runtime.region} {
    %stop = "exec.reject"(%scope) {reason="reject", site="first_rejection"} : (!runtime.scope) -> !exec.stop
    cf.br ^failure(%stop : !exec.stop)
  ^failure(%stopped: !exec.stop):
    %failed = "exec.failed"(%stopped) : (!exec.stop) -> !exec.outcome<>
    return %failed : !exec.outcome<>
  }
  func.func @first(%scope: !runtime.scope, %a: !F, %b: !F, %ok: i1, %other: i1) -> !exec.outcome<(!F, !F, !F)> attributes {no_inline, runtime.origin=["first", []]} {
    %r = "exec.compute"(%scope, %a, %b, %ok, %other) {callee=@first_unit::@evaluate, site="first_math"} : (!runtime.scope, !F, !F, i1, i1) -> !exec.outcome<(!F, !F, !F)>
    "exec.dispatch"(%r)[^success, ^failure] : (!exec.outcome<(!F, !F, !F)>) -> ()
  ^success(%v0: !F, %v1: !F, %v2: !F):
    %test = "exec.test"(%scope, %ok) {site="inner_guard"} : (!runtime.scope, i1) -> !exec.outcome<(i1)>
    "exec.dispatch"(%test)[^decision, ^failure] : (!exec.outcome<(i1)>) -> ()
  ^decision(%condition: i1):
    cf.cond_br %condition, ^yes, ^no
  ^yes:
    %ys = "runtime.enter_scope"(%scope) {kind="conditional", selection="then", site="inner_guard", operandSegmentSizes=array<i32: 1, 0, 0>} : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
    "exec.dispatch"(%ys)[^yes_call, ^failure] : (!exec.outcome<(!runtime.scope)>) -> ()
  ^yes_call(%yes_scope: !runtime.scope):
    %yr = call @first_yes(%yes_scope) : (!runtime.scope) -> !exec.outcome<>
    %yx = "runtime.exit_scope"(%yes_scope, %yr) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
    "exec.dispatch"(%yx)[^yes_exit, ^failure] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
  ^yes_exit(%yt: !runtime.transfer<>):
    %ya = "runtime.accept_transfer"(%scope, %yt) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
    "exec.dispatch"(%ya)[^yes_done, ^failure] : (!exec.outcome<>) -> ()
  ^yes_done:
    cf.br ^done
  ^no:
    %ns = "runtime.enter_scope"(%scope) {kind="conditional", selection="else", site="inner_guard", operandSegmentSizes=array<i32: 1, 0, 0>} : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
    "exec.dispatch"(%ns)[^no_call, ^failure] : (!exec.outcome<(!runtime.scope)>) -> ()
  ^no_call(%no_scope: !runtime.scope):
    %nr = call @first_no(%no_scope) : (!runtime.scope) -> !exec.outcome<>
    %nx = "runtime.exit_scope"(%no_scope, %nr) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
    "exec.dispatch"(%nx)[^no_exit, ^failure] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
  ^no_exit(%nt: !runtime.transfer<>):
    %na = "runtime.accept_transfer"(%scope, %nt) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
    "exec.dispatch"(%na)[^no_done, ^failure] : (!exec.outcome<>) -> ()
  ^no_done:
    cf.br ^done
  ^done:
    %returned = "exec.returned"(%v0, %v1, %v2) : (!F, !F, !F) -> !exec.outcome<(!F, !F, !F)>
    return %returned : !exec.outcome<(!F, !F, !F)>
  ^failure(%stopped: !exec.stop):
    %failed = "exec.failed"(%stopped) : (!exec.stop) -> !exec.outcome<(!F, !F, !F)>
    return %failed : !exec.outcome<(!F, !F, !F)>
  }
  func.func @second(%scope: !runtime.scope, %a: !F, %b: !F, %ok: i1, %other: i1) -> !exec.outcome<(!F, !F, !F)> attributes {no_inline, runtime.origin=["second", []]} {
    %r = "exec.compute"(%scope, %a, %b, %ok, %other) {callee=@second_unit::@evaluate, site="second_math"} : (!runtime.scope, !F, !F, i1, i1) -> !exec.outcome<(!F, !F, !F)>
    "exec.dispatch"(%r)[^success, ^failure] : (!exec.outcome<(!F, !F, !F)>) -> ()
  ^success(%v0: !F, %v1: !F, %v2: !F):
    %returned = "exec.returned"(%v0, %v1, %v2) : (!F, !F, !F) -> !exec.outcome<(!F, !F, !F)>
    return %returned : !exec.outcome<(!F, !F, !F)>
  ^failure(%stopped: !exec.stop):
    %failed = "exec.failed"(%stopped) : (!exec.stop) -> !exec.outcome<(!F, !F, !F)>
    return %failed : !exec.outcome<(!F, !F, !F)>
  }
  func.func private @authored_raw(%a: !F, %b: !F) -> !F {
    %v = algebra.field_subtract %a, %b : (!F, !F) -> !F
    return %v : !F
  }
  func.func @authored(%scope: !runtime.scope, %a: !F, %b: !F) -> !exec.outcome<(!F)> attributes {no_inline, runtime.origin=["authored", []]} {
    %r = "exec.compute"(%scope, %a, %b) {callee=@authored_raw, site="authored_math"} : (!runtime.scope, !F, !F) -> !exec.outcome<(!F)>
    "exec.dispatch"(%r)[^success, ^failure] : (!exec.outcome<(!F)>) -> ()
  ^success(%v: !F):
    %returned = "exec.returned"(%v) : (!F) -> !exec.outcome<(!F)>
    return %returned : !exec.outcome<(!F)>
  ^failure(%stopped: !exec.stop):
    %failed = "exec.failed"(%stopped) : (!exec.stop) -> !exec.outcome<(!F)>
    return %failed : !exec.outcome<(!F)>
  }
  func.func private @gate_yes(%scope: !runtime.scope) -> !exec.outcome<> attributes {no_inline, runtime.region} {
    %r = "exec.complete"(%scope) : (!runtime.scope) -> !exec.outcome<>
    return %r : !exec.outcome<>
  }
  func.func private @gate_no(%scope: !runtime.scope) -> !exec.outcome<> attributes {no_inline, runtime.region} {
    %stop = "exec.reject"(%scope) {reason="reject", site="gate_rejection"} : (!runtime.scope) -> !exec.stop
    cf.br ^failure(%stop : !exec.stop)
  ^failure(%stopped: !exec.stop):
    %failed = "exec.failed"(%stopped) : (!exec.stop) -> !exec.outcome<>
    return %failed : !exec.outcome<>
  }
  func.func @gate(%scope: !runtime.scope, %ok: i1) -> !exec.outcome<> attributes {no_inline, runtime.origin=["gate", []]} {
    %test = "exec.test"(%scope, %ok) {site="outer_guard"} : (!runtime.scope, i1) -> !exec.outcome<(i1)>
    "exec.dispatch"(%test)[^decision, ^failure] : (!exec.outcome<(i1)>) -> ()
  ^decision(%condition: i1):
    cf.cond_br %condition, ^yes, ^no
  ^yes:
    %ys = "runtime.enter_scope"(%scope) {kind="conditional", selection="then", site="outer_guard", operandSegmentSizes=array<i32: 1, 0, 0>} : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
    "exec.dispatch"(%ys)[^yes_call, ^failure] : (!exec.outcome<(!runtime.scope)>) -> ()
  ^yes_call(%yes_scope: !runtime.scope):
    %yr = call @gate_yes(%yes_scope) : (!runtime.scope) -> !exec.outcome<>
    %yx = "runtime.exit_scope"(%yes_scope, %yr) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
    "exec.dispatch"(%yx)[^yes_exit, ^failure] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
  ^yes_exit(%yt: !runtime.transfer<>):
    %ya = "runtime.accept_transfer"(%scope, %yt) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
    "exec.dispatch"(%ya)[^yes_done, ^failure] : (!exec.outcome<>) -> ()
  ^yes_done:
    cf.br ^done
  ^no:
    %ns = "runtime.enter_scope"(%scope) {kind="conditional", selection="else", site="outer_guard", operandSegmentSizes=array<i32: 1, 0, 0>} : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
    "exec.dispatch"(%ns)[^no_call, ^failure] : (!exec.outcome<(!runtime.scope)>) -> ()
  ^no_call(%no_scope: !runtime.scope):
    %nr = call @gate_no(%no_scope) : (!runtime.scope) -> !exec.outcome<>
    %nx = "runtime.exit_scope"(%no_scope, %nr) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
    "exec.dispatch"(%nx)[^no_exit, ^failure] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
  ^no_exit(%nt: !runtime.transfer<>):
    %na = "runtime.accept_transfer"(%scope, %nt) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
    "exec.dispatch"(%na)[^no_done, ^failure] : (!exec.outcome<>) -> ()
  ^no_done:
    cf.br ^done
  ^done:
    %returned = "exec.returned"() : () -> !exec.outcome<>
    return %returned : !exec.outcome<>
  ^failure(%stopped: !exec.stop):
    %failed = "exec.failed"(%stopped) : (!exec.stop) -> !exec.outcome<>
    return %failed : !exec.outcome<>
  }
  "protocol.participant"() ({ ^entry(%a: !F, %b: !F, %ok: i1, %other: i1):
    %first:3 = "protocol.local_call"(%a, %b, %ok, %other) {callee=@first, site="first_cut", role="P"} : (!F, !F, i1, i1) -> (!F, !F, !F)
    "protocol.local_call"(%ok) {callee=@gate, site="outer_guard", role="P"} : (i1) -> ()
    %second:3 = "protocol.local_call"(%a, %b, %ok, %other) {callee=@second, site="second_cut", role="P"} : (!F, !F, i1, i1) -> (!F, !F, !F)
    "protocol.finish"(%second#0, %second#1, %second#2) : (!F, !F, !F) -> ()
  }) {sym_name="participant", function_type=(!F, !F, i1, i1)->(!F, !F, !F), instance="main", role="P"} : () -> ()
  "protocol.projection"() {interfaces=[], calculations=[
    {participant=@participant, callee=@first, site="first_cut"},
    {participant=@participant, callee=@second, site="second_cut"}
  ]} : () -> ()
}) {profile=#protocol.profile<exec>} : () -> () }
