!f = !algebra.field<"bls12-381.fr">
!v = !algebra.field_vector<"bls12-381.fr">
!rng = !protocol.service_ref<"random.bls12-381.fr/0">
module { "protocol.module"() ({
 "runtime.binding"() {sym_name="split",contract="vector.split",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>} : ()->()
 "runtime.binding"() {sym_name="dot",contract="vector.dot",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>} : ()->()
 "runtime.binding"() {sym_name="scale",contract="vector.scale",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>} : ()->()
 "runtime.binding"() {sym_name="add",contract="vector.add",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>} : ()->()
 "runtime.binding"() {sym_name="inverse",contract="field.inverse",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>} : ()->()
 "runtime.binding"() {sym_name="length",contract="vector.length_check",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(i1)>} : ()->()
 "runtime.binding"() {sym_name="at",contract="vector.at",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>} : ()->()
 "runtime.binding"() {sym_name="require",contract="control.require",arguments=[],implementation="",function_type=(!runtime.scope, i1) -> !exec.outcome<>} : ()->()

    func.func @cross_terms(%arg0: !runtime.scope, %arg1: !v, %arg2: !v) -> !exec.outcome<(!f, !f)> attributes {no_inline, runtime.origin = ["cross_terms", []]} {
      %0 = "exec.apply"(%arg0, %arg1) <{binding = @split, parameters = [], site = "splitA"}> : (!runtime.scope, !v) -> !exec.outcome<(!v, !v)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!v, !v)>) -> ()
    ^bb1(%1: !v, %2: !v):  // pred: ^bb0
      %3 = "exec.apply"(%arg0, %arg2) <{binding = @split, parameters = [], site = "splitB"}> : (!runtime.scope, !v) -> !exec.outcome<(!v, !v)>
      "exec.dispatch"(%3)[^bb3, ^bb2] : (!exec.outcome<(!v, !v)>) -> ()
    ^bb2(%4: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %5 = "exec.failed"(%4) : (!exec.stop) -> !exec.outcome<(!f, !f)>
      return %5 : !exec.outcome<(!f, !f)>
    ^bb3(%6: !v, %7: !v):  // pred: ^bb1
      %8 = "exec.apply"(%arg0, %1, %7) <{binding = @dot, parameters = [], site = "left"}> : (!runtime.scope, !v, !v) -> !exec.outcome<(!f)>
      "exec.dispatch"(%8)[^bb4, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb4(%9: !f):  // pred: ^bb3
      %10 = "exec.apply"(%arg0, %2, %6) <{binding = @dot, parameters = [], site = "right"}> : (!runtime.scope, !v, !v) -> !exec.outcome<(!f)>
      "exec.dispatch"(%10)[^bb5, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb5(%11: !f):  // pred: ^bb4
      %12 = "exec.returned"(%9, %11) : (!f, !f) -> !exec.outcome<(!f, !f)>
      return %12 : !exec.outcome<(!f, !f)>
    }
    func.func @invert(%arg0: !runtime.scope, %arg1: !f) -> !exec.outcome<(!f)> attributes {no_inline, runtime.origin = ["invert", []]} {
      %0 = "exec.apply"(%arg0, %arg1) <{binding = @inverse, parameters = [], site = "nonzero"}> : (!runtime.scope, !f) -> !exec.outcome<(!f)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb1(%1: !f):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!f) -> !exec.outcome<(!f)>
      return %2 : !exec.outcome<(!f)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!f)>
      return %4 : !exec.outcome<(!f)>
    }
    func.func @weighted_fold(%arg0: !runtime.scope, %arg1: !v, %arg2: !v, %arg3: !f) -> !exec.outcome<(!v, !v)> attributes {no_inline, runtime.origin = ["weighted_fold", []]} {
      %0 = "exec.apply"(%arg0, %arg3) <{binding = @inverse, parameters = [], site = "nonzero"}> : (!runtime.scope, !f) -> !exec.outcome<(!f)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb1(%1: !f):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %arg1) <{binding = @split, parameters = [], site = "splitA"}> : (!runtime.scope, !v) -> !exec.outcome<(!v, !v)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(!v, !v)>) -> ()
    ^bb2(%3: !exec.stop):  // 9 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!v, !v)>
      return %4 : !exec.outcome<(!v, !v)>
    ^bb3(%5: !v, %6: !v):  // pred: ^bb1
      %7 = "exec.apply"(%arg0, %arg2) <{binding = @split, parameters = [], site = "splitB"}> : (!runtime.scope, !v) -> !exec.outcome<(!v, !v)>
      "exec.dispatch"(%7)[^bb4, ^bb2] : (!exec.outcome<(!v, !v)>) -> ()
    ^bb4(%8: !v, %9: !v):  // pred: ^bb3
      %10 = "exec.apply"(%arg0, %5, %arg3) <{binding = @scale, parameters = [], site = "scaleAL"}> : (!runtime.scope, !v, !f) -> !exec.outcome<(!v)>
      "exec.dispatch"(%10)[^bb5, ^bb2] : (!exec.outcome<(!v)>) -> ()
    ^bb5(%11: !v):  // pred: ^bb4
      %12 = "exec.apply"(%arg0, %6, %1) <{binding = @scale, parameters = [], site = "scaleAR"}> : (!runtime.scope, !v, !f) -> !exec.outcome<(!v)>
      "exec.dispatch"(%12)[^bb6, ^bb2] : (!exec.outcome<(!v)>) -> ()
    ^bb6(%13: !v):  // pred: ^bb5
      %14 = "exec.apply"(%arg0, %8, %1) <{binding = @scale, parameters = [], site = "scaleBL"}> : (!runtime.scope, !v, !f) -> !exec.outcome<(!v)>
      "exec.dispatch"(%14)[^bb7, ^bb2] : (!exec.outcome<(!v)>) -> ()
    ^bb7(%15: !v):  // pred: ^bb6
      %16 = "exec.apply"(%arg0, %9, %arg3) <{binding = @scale, parameters = [], site = "scaleBR"}> : (!runtime.scope, !v, !f) -> !exec.outcome<(!v)>
      "exec.dispatch"(%16)[^bb8, ^bb2] : (!exec.outcome<(!v)>) -> ()
    ^bb8(%17: !v):  // pred: ^bb7
      %18 = "exec.apply"(%arg0, %11, %13) <{binding = @add, parameters = [], site = "addA"}> : (!runtime.scope, !v, !v) -> !exec.outcome<(!v)>
      "exec.dispatch"(%18)[^bb9, ^bb2] : (!exec.outcome<(!v)>) -> ()
    ^bb9(%19: !v):  // pred: ^bb8
      %20 = "exec.apply"(%arg0, %15, %17) <{binding = @add, parameters = [], site = "addB"}> : (!runtime.scope, !v, !v) -> !exec.outcome<(!v)>
      "exec.dispatch"(%20)[^bb10, ^bb2] : (!exec.outcome<(!v)>) -> ()
    ^bb10(%21: !v):  // pred: ^bb9
      %22 = "exec.returned"(%19, %21) : (!v, !v) -> !exec.outcome<(!v, !v)>
      return %22 : !exec.outcome<(!v, !v)>
    }
    func.func @terminal_values(%arg0: !runtime.scope, %arg1: !v, %arg2: !v) -> !exec.outcome<(!f, !f)> attributes {no_inline, runtime.origin = ["terminal_values", []]} {
      %0 = "exec.apply"(%arg0, %arg1) <{binding = @length, parameters = ["1"], site = "lengthA"}> : (!runtime.scope, !v) -> !exec.outcome<(i1)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1: i1):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %1) <{binding = @require, parameters = [], site = "shapeA"}> : (!runtime.scope, i1) -> !exec.outcome<>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<>) -> ()
    ^bb2(%3: !exec.stop):  // 6 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!f, !f)>
      return %4 : !exec.outcome<(!f, !f)>
    ^bb3:  // pred: ^bb1
      %5 = "exec.apply"(%arg0, %arg2) <{binding = @length, parameters = ["1"], site = "lengthB"}> : (!runtime.scope, !v) -> !exec.outcome<(i1)>
      "exec.dispatch"(%5)[^bb4, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb4(%6: i1):  // pred: ^bb3
      %7 = "exec.apply"(%arg0, %6) <{binding = @require, parameters = [], site = "shapeB"}> : (!runtime.scope, i1) -> !exec.outcome<>
      "exec.dispatch"(%7)[^bb5, ^bb2] : (!exec.outcome<>) -> ()
    ^bb5:  // pred: ^bb4
      %8 = "exec.apply"(%arg0, %arg1) <{binding = @at, parameters = ["0"], site = "valueA"}> : (!runtime.scope, !v) -> !exec.outcome<(!f)>
      "exec.dispatch"(%8)[^bb6, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb6(%9: !f):  // pred: ^bb5
      %10 = "exec.apply"(%arg0, %arg2) <{binding = @at, parameters = ["0"], site = "valueB"}> : (!runtime.scope, !v) -> !exec.outcome<(!f)>
      "exec.dispatch"(%10)[^bb7, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb7(%11: !f):  // pred: ^bb6
      %12 = "exec.returned"(%9, %11) : (!f, !f) -> !exec.outcome<(!f, !f)>
      return %12 : !exec.outcome<(!f, !f)>
    }




 "protocol.func"() ({ ^entry(%n:ui64,%a:!v,%b:!v,%claim:!f,%coins:!rng):
   %done:3 = "protocol.repeat"(%n,%a,%b,%claim,%coins) ({
   ^round(%i:ui64,%av:!v,%bv:!v,%current:!f,%random:!rng):
     %cross:2 = "protocol.local_call"(%av,%bv) {callee=@cross_terms,role="P",site="cross_terms"} : (!v,!v)->(!f,!f)
     %L = protocol.exchange %cross#0 {sender="P",receiver="V",site="left"} : !f
     %R = protocol.exchange %cross#1 {sender="P",receiver="V",site="right"} : !f
     %x = "protocol.query"(%random) {method="draw",owner="V",site="draw"} : (!rng)->!f
     %ix = "protocol.local_call"(%x) {callee=@invert,role="V",site="verifier_inverse"} : (!f)->!f
     %xP = protocol.exchange %x {sender="V",receiver="P",site="challenge"} : !f
     %folded:2 = "protocol.local_call"(%av,%bv,%xP) {callee=@weighted_fold,role="P",site="fold"} : (!v,!v,!f)->(!v,!v)
     %xx = algebra.field_multiply %x,%x : (!f,!f)->!f
     %ii = algebra.field_multiply %ix,%ix : (!f,!f)->!f
     %weightedL = algebra.field_multiply %xx,%L : (!f,!f)->!f
     %weightedR = algebra.field_multiply %ii,%R : (!f,!f)->!f
     %cross_sum = algebra.field_add %weightedL,%weightedR : (!f,!f)->!f
     %next = algebra.field_add %current,%cross_sum : (!f,!f)->!f
     "protocol.yield"(%folded#0,%folded#1,%next) : (!v,!v,!f)->()
   }) {site="rounds",carried=3:i64,maximum=8:i64,roles=["P","V"],carried_roles=[["P"],["P"],["V"]]} : (ui64,!v,!v,!f,!rng)->(!v,!v,!f)
   %terminal:2 = "protocol.local_call"(%done#0,%done#1) {callee=@terminal_values,role="P",site="terminal"} : (!v,!v)->(!f,!f)
   %aV = protocol.exchange %terminal#0 {sender="P",receiver="V",site="terminalA"} : !f
   %bV = protocol.exchange %terminal#1 {sender="P",receiver="V",site="terminalB"} : !f
   %product = algebra.field_multiply %aV,%bV : (!f,!f)->!f
   %accepted = algebra.field_equal %product,%done#2 : (!f,!f)->i1
   "protocol.return"(%accepted,%terminal#0,%terminal#1) : (i1,!f,!f)->()
 }) {sym_name="main",function_type=(ui64,!v,!v,!f,!rng)->(i1,!f,!f),roles=["P","V"],input_roles=[["P","V"],["P"],["P"],["V"],["V"]],output_roles=[["V"],["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
