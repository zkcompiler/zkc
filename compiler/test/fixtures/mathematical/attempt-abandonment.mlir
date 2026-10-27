!f = !algebra.field<"bls12-381.fr">
!r = !runtime.capability<"rng:bls12-381.fr">
!s = !protocol.service_ref<"random.bls12-381.fr/0">
module { "protocol.module"() ({
 "runtime.binding"() {sym_name="random",contract="random.draw",arguments=["bls12-381.fr"],implementation=""} : ()->()
    func.func @draw(%arg0: !runtime.scope, %arg1: !r) -> !exec.outcome<(!f, !r)> attributes {no_inline, runtime.origin = ["draw", []]} {
      %0 = "exec.apply"(%arg0, %arg1) <{binding = @random, parameters = [], site = "sample"}> : (!runtime.scope, !r) -> !exec.outcome<(!f, !r)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!f, !r)>) -> ()
    ^bb1(%1: !f, %2: !r):  // pred: ^bb0
      %3 = "exec.returned"(%1, %2) : (!f, !r) -> !exec.outcome<(!f, !r)>
      return %3 : !exec.outcome<(!f, !r)>
    ^bb2(%4: !exec.stop):  // pred: ^bb0
      %5 = "exec.failed"(%4) : (!exec.stop) -> !exec.outcome<(!f, !r)>
      return %5 : !exec.outcome<(!f, !r)>
    }
    func.func @prepare(%arg0: !runtime.scope, %arg1: i1, %arg2: !f, %arg3: !r) -> !exec.outcome<(!f, !r)> attributes {no_inline, runtime.origin = ["prepare", []]} {
      %0 = "exec.test"(%arg0, %arg1) <{site = "partial_inverse"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1: i1):  // pred: ^bb0
      cf.cond_br %1, ^bb3, ^bb4
    ^bb2(%2: !exec.stop):  // 7 preds: ^bb0, ^bb3, ^bb4, ^bb6, ^bb7, ^bb9, ^bb10
      %3 = "exec.failed"(%2) : (!exec.stop) -> !exec.outcome<(!f, !r)>
      return %3 : !exec.outcome<(!f, !r)>
    ^bb3:  // pred: ^bb1
      %4 = "runtime.enter_scope"(%arg0, %arg2, %arg3) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "then", site = "partial_inverse"}> : (!runtime.scope, !f, !r) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%4)[^bb6, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb4:  // pred: ^bb1
      %5 = "runtime.enter_scope"(%arg0, %arg2, %arg3) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "else", site = "partial_inverse"}> : (!runtime.scope, !f, !r) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%5)[^bb9, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb5(%6: !f, %7: !r):  // 2 preds: ^bb8, ^bb11
      %8 = "exec.returned"(%6, %7) : (!f, !r) -> !exec.outcome<(!f, !r)>
      return %8 : !exec.outcome<(!f, !r)>
    ^bb6(%9: !runtime.scope):  // pred: ^bb3
      %10 = call @control_0(%9, %arg2, %arg3) : (!runtime.scope, !f, !r) -> !exec.outcome<(!f, !r)>
      %11 = "runtime.exit_scope"(%9, %10) : (!runtime.scope, !exec.outcome<(!f, !r)>) -> !exec.outcome<(!runtime.transfer<(!f, !r)>)>
      "exec.dispatch"(%11)[^bb7, ^bb2] : (!exec.outcome<(!runtime.transfer<(!f, !r)>)>) -> ()
    ^bb7(%12: !runtime.transfer<(!f, !r)>):  // pred: ^bb6
      %13 = "runtime.accept_transfer"(%arg0, %12) : (!runtime.scope, !runtime.transfer<(!f, !r)>) -> !exec.outcome<(!f, !r)>
      "exec.dispatch"(%13)[^bb8, ^bb2] : (!exec.outcome<(!f, !r)>) -> ()
    ^bb8(%14: !f, %15: !r):  // pred: ^bb7
      cf.br ^bb5(%14, %15 : !f, !r)
    ^bb9(%16: !runtime.scope):  // pred: ^bb4
      %17 = call @control_1(%16, %arg2, %arg3) : (!runtime.scope, !f, !r) -> !exec.outcome<(!f, !r)>
      %18 = "runtime.exit_scope"(%16, %17) : (!runtime.scope, !exec.outcome<(!f, !r)>) -> !exec.outcome<(!runtime.transfer<(!f, !r)>)>
      "exec.dispatch"(%18)[^bb10, ^bb2] : (!exec.outcome<(!runtime.transfer<(!f, !r)>)>) -> ()
    ^bb10(%19: !runtime.transfer<(!f, !r)>):  // pred: ^bb9
      %20 = "runtime.accept_transfer"(%arg0, %19) : (!runtime.scope, !runtime.transfer<(!f, !r)>) -> !exec.outcome<(!f, !r)>
      "exec.dispatch"(%20)[^bb11, ^bb2] : (!exec.outcome<(!f, !r)>) -> ()
    ^bb11(%21: !f, %22: !r):  // pred: ^bb10
      cf.br ^bb5(%21, %22 : !f, !r)
    }
    func.func private @control_0(%arg0: !runtime.scope, %arg1: !f, %arg2: !r) -> !exec.outcome<(!f, !r)> attributes {no_inline, runtime.region} {
      %0 = "exec.complete"(%arg0, %arg1, %arg2) : (!runtime.scope, !f, !r) -> !exec.outcome<(!f, !r)>
      return %0 : !exec.outcome<(!f, !r)>
    }
    func.func private @control_1(%arg0: !runtime.scope, %arg1: !f, %arg2: !r) -> !exec.outcome<(!f, !r)> attributes {no_inline, runtime.region} {
      %0 = "exec.apply"(%arg0, %arg1) <{binding = @inverse, parameters = [], site = "inverse"}> : (!runtime.scope, !f) -> !exec.outcome<(!f)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb1(%1: !f):  // pred: ^bb0
      %2 = "exec.complete"(%arg0, %1, %arg2) : (!runtime.scope, !f, !r) -> !exec.outcome<(!f, !r)>
      return %2 : !exec.outcome<(!f, !r)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!f, !r)>
      return %4 : !exec.outcome<(!f, !r)>
    }

 "runtime.binding"() {sym_name="inverse",contract="field.inverse",arguments=["bls12-381.fr"],implementation=""} : ()->()

 "protocol.func"() ({ ^entry(%a:!f,%b:!f,%rng:!r,%coins:!s):
   %sample:2 = "protocol.local_call"(%rng) {callee=@draw,role="P",site="salt"} : (!r)->(!f,!r)
   %zero = algebra.field_subtract %a,%a : (!f,!f)->!f
   %iszero = algebra.field_equal %sample#0,%zero : (!f,!f)->i1
   %yes = arith.constant true
   %complete = arith.xori %iszero,%yes : i1
   %prepared:2 = "protocol.local_call"(%iszero,%sample#0,%sample#1) {callee=@prepare,role="P",site="prepare"} : (i1,!f,!r)->(!f,!r)
   %salt = protocol.exchange %prepared#0 {sender="P",receiver="V",site="salt_message"} : !f
   %n = "data.index"() {value="2"} : ()->ui64
   %fold:3 = "protocol.repeat"(%n,%a,%a,%prepared#1,%b,%coins,%iszero,%complete) ({
   ^round(%i:ui64,%left:!f,%right:!f,%state:!r,%step:!f,%random:!s,%abandon:i1,%done:i1):
     %message = protocol.exchange %left {sender="P",receiver="V",site="coefficient"} : !f
     %same = algebra.field_equal %message,%right : (!f,!f)->i1
     protocol.guard %same {owner="V",site="coefficient_check"}
     %c = "protocol.query"(%random) {method="draw",owner="V",site="draw"} : (!s)->!f
     %challenge = protocol.exchange %c {sender="V",receiver="P",site="challenge"} : !f
     %next_rng = "protocol.finish_if"(%abandon,%done,%state) {owner="P",site="abandon"} : (i1,i1,!r)->!r
     %extra:2 = "protocol.local_call"(%next_rng) {callee=@draw,role="P",site="suffix_draw"} : (!r)->(!f,!r)
     %p = algebra.field_multiply %challenge,%step : (!f,!f)->!f
     %v = algebra.field_multiply %c,%step : (!f,!f)->!f
     %nextP = algebra.field_add %left,%p : (!f,!f)->!f
     %nextV = algebra.field_add %right,%v : (!f,!f)->!f
     "protocol.yield"(%nextP,%nextV,%extra#1) : (!f,!f,!r)->()
   }) {site="fold",carried=3:i64,maximum=2:i64,roles=["P","V"],carried_roles=[["P"],["V"],["P"]]} : (ui64,!f,!f,!r,!f,!s,i1,i1)->(!f,!f,!r)
   %final = protocol.exchange %fold#0 {sender="P",receiver="V",site="result"} : !f
   %accepted = algebra.field_equal %final,%fold#1 : (!f,!f)->i1
   "protocol.return"(%accepted,%complete,%fold#2) : (i1,i1,!r)->()
 }) {sym_name="main",function_type=(!f,!f,!r,!s)->(i1,i1,!r),roles=["P","V"],input_roles=[["P","V"],["P","V"],["P"],["V"]],output_roles=[["V"],["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
