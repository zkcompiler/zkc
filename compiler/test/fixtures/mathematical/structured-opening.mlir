!message = !data.variant<#data.identity<["atom", "Opening"]>, [#data.alternative<"none">, #data.alternative<"some", [!algebra.field<"bls12-381.fr">, !commitment.polynomial<"multilinear.kzg.bls12-381/0", "proof">]>]>
!pk = !commitment.polynomial<"multilinear.kzg.bls12-381/0", "prover_key">
!vk = !commitment.polynomial<"multilinear.kzg.bls12-381/0", "verifier_key">
!c = !commitment.polynomial<"multilinear.kzg.bls12-381/0", "commitment">
!o = !commitment.polynomial<"multilinear.kzg.bls12-381/0", "opening_state">
!proof = !commitment.polynomial<"multilinear.kzg.bls12-381/0", "proof">
!f = !algebra.field<"bls12-381.fr">
!t = !poly.multilinear<"bls12-381.fr">
!p = !poly.point<"bls12-381.fr">
module { "protocol.module"() ({
 "runtime.binding"() {sym_name="empty",contract="poly.empty_point",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope) -> !exec.outcome<(!poly.point<"bls12-381.fr">)>} : ()->()
 "runtime.binding"() {sym_name="append",contract="poly.append_point",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope, !poly.point<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!poly.point<"bls12-381.fr">)>} : ()->()
    func.func @empty_point(%arg0: !runtime.scope) -> !exec.outcome<(!p)> attributes {no_inline, runtime.origin = ["empty_point", []]} {
      %0 = "exec.apply"(%arg0) <{binding = @empty, parameters = [], site = "empty"}> : (!runtime.scope) -> !exec.outcome<(!p)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!p)>) -> ()
    ^bb1(%1: !p):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!p) -> !exec.outcome<(!p)>
      return %2 : !exec.outcome<(!p)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!p)>
      return %4 : !exec.outcome<(!p)>
    }
    func.func @append_point(%arg0: !runtime.scope, %arg1: !p, %arg2: !f) -> !exec.outcome<(!p)> attributes {no_inline, runtime.origin = ["append_point", []]} {
      %0 = "exec.apply"(%arg0, %arg1, %arg2) <{binding = @append, parameters = [], site = "append"}> : (!runtime.scope, !p, !f) -> !exec.outcome<(!p)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!p)>) -> ()
    ^bb1(%1: !p):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!p) -> !exec.outcome<(!p)>
      return %2 : !exec.outcome<(!p)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!p)>
      return %4 : !exec.outcome<(!p)>
    }
    func.func @commit(%arg0: !runtime.scope, %arg1: !pk, %arg2: !t) -> !exec.outcome<(!c, !o)> attributes {no_inline, runtime.origin = ["commit", []]} {
      %0 = "exec.apply"(%arg0, %arg1, %arg2) <{binding = @commit_kernel, parameters = [], site = "commit"}> : (!runtime.scope, !pk, !t) -> !exec.outcome<(!c, !o)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!c, !o)>) -> ()
    ^bb1(%1: !c, %2: !o):  // pred: ^bb0
      %3 = "exec.returned"(%1, %2) : (!c, !o) -> !exec.outcome<(!c, !o)>
      return %3 : !exec.outcome<(!c, !o)>
    ^bb2(%4: !exec.stop):  // pred: ^bb0
      %5 = "exec.failed"(%4) : (!exec.stop) -> !exec.outcome<(!c, !o)>
      return %5 : !exec.outcome<(!c, !o)>
    }
    func.func @open(%arg0: !runtime.scope, %arg1: !o, %arg2: !p) -> !exec.outcome<(!f, !proof)> attributes {no_inline, runtime.origin = ["open", []]} {
      %0 = "exec.apply"(%arg0, %arg1, %arg2) <{binding = @open_kernel, parameters = [], site = "open"}> : (!runtime.scope, !o, !p) -> !exec.outcome<(!f, !proof)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!f, !proof)>) -> ()
    ^bb1(%1: !f, %2: !proof):  // pred: ^bb0
      %3 = "exec.returned"(%1, %2) : (!f, !proof) -> !exec.outcome<(!f, !proof)>
      return %3 : !exec.outcome<(!f, !proof)>
    ^bb2(%4: !exec.stop):  // pred: ^bb0
      %5 = "exec.failed"(%4) : (!exec.stop) -> !exec.outcome<(!f, !proof)>
      return %5 : !exec.outcome<(!f, !proof)>
    }
    func.func @check(%arg0: !runtime.scope, %arg1: !vk, %arg2: !c, %arg3: !p, %arg4: !f, %arg5: !proof) -> !exec.outcome<(i1)> attributes {no_inline, runtime.origin = ["check", []]} {
      %0 = "exec.apply"(%arg0, %arg1, %arg2, %arg3, %arg4, %arg5) <{binding = @check_kernel, parameters = [], site = "check"}> : (!runtime.scope, !vk, !c, !p, !f, !proof) -> !exec.outcome<(i1)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1: i1):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (i1) -> !exec.outcome<(i1)>
      return %2 : !exec.outcome<(i1)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(i1)>
      return %4 : !exec.outcome<(i1)>
    }
    func.func @same_root(%arg0: !runtime.scope, %arg1: !c, %arg2: !c) -> !exec.outcome<(i1)> attributes {no_inline, runtime.origin = ["same_root", []]} {
      %0 = "exec.apply"(%arg0, %arg1, %arg2) <{binding = @equal_kernel, parameters = [], site = "equal"}> : (!runtime.scope, !c, !c) -> !exec.outcome<(i1)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1: i1):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (i1) -> !exec.outcome<(i1)>
      return %2 : !exec.outcome<(i1)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(i1)>
      return %4 : !exec.outcome<(i1)>
    }
    func.func @pack_opening(%arg0: !runtime.scope, %arg1: !f, %arg2: !proof) -> !exec.outcome<(!message)> attributes {no_inline, runtime.origin = ["pack_opening", []]} {
      %0 = "exec.variant"(%arg0, %arg1, %arg2) <{alternative = "some", site = "present"}> : (!runtime.scope, !f, !proof) -> !exec.outcome<(!message)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!message)>) -> ()
    ^bb1(%1: !message):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!message) -> !exec.outcome<(!message)>
      return %2 : !exec.outcome<(!message)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!message)>
      return %4 : !exec.outcome<(!message)>
    }
    func.func @check_message(%arg0: !runtime.scope, %arg1: !message, %arg2: !vk, %arg3: !c, %arg4: !p) -> !exec.outcome<(!f, i1)> attributes {no_inline, runtime.origin = ["check_message", []]} {
      "exec.match"(%arg0, %arg1, %arg2, %arg3, %arg4)[^bb2, ^bb3, ^bb4] <{alternatives = ["none", "some"], site = "presence"}> : (!runtime.scope, !message, !vk, !c, !p) -> ()
    ^bb1(%0: !f, %1: i1):  // 2 preds: ^bb7, ^bb10
      %2 = "exec.returned"(%0, %1) : (!f, i1) -> !exec.outcome<(!f, i1)>
      return %2 : !exec.outcome<(!f, i1)>
    ^bb2(%3: !exec.stop):  // 7 preds: ^bb0, ^bb3, ^bb4, ^bb5, ^bb6, ^bb8, ^bb9
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!f, i1)>
      return %4 : !exec.outcome<(!f, i1)>
    ^bb3(%5: !vk, %6: !c, %7: !p):  // pred: ^bb0
      %8 = "runtime.enter_scope"(%arg0, %5, %6, %7) <{kind = "match", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "none", site = "presence"}> : (!runtime.scope, !vk, !c, !p) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%8)[^bb5, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb4(%9: !f, %10: !proof, %11: !vk, %12: !c, %13: !p):  // pred: ^bb0
      %14 = "runtime.enter_scope"(%arg0, %9, %10, %11, %12, %13) <{kind = "match", operandSegmentSizes = array<i32: 1, 0, 5>, selection = "some", site = "presence"}> : (!runtime.scope, !f, !proof, !vk, !c, !p) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%14)[^bb8, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb5(%15: !runtime.scope):  // pred: ^bb3
      %16 = call @control_0(%15, %5, %6, %7) : (!runtime.scope, !vk, !c, !p) -> !exec.outcome<(!f, i1)>
      %17 = "runtime.exit_scope"(%15, %16) : (!runtime.scope, !exec.outcome<(!f, i1)>) -> !exec.outcome<(!runtime.transfer<(!f, i1)>)>
      "exec.dispatch"(%17)[^bb6, ^bb2] : (!exec.outcome<(!runtime.transfer<(!f, i1)>)>) -> ()
    ^bb6(%18: !runtime.transfer<(!f, i1)>):  // pred: ^bb5
      %19 = "runtime.accept_transfer"(%arg0, %18) : (!runtime.scope, !runtime.transfer<(!f, i1)>) -> !exec.outcome<(!f, i1)>
      "exec.dispatch"(%19)[^bb7, ^bb2] : (!exec.outcome<(!f, i1)>) -> ()
    ^bb7(%20: !f, %21: i1):  // pred: ^bb6
      cf.br ^bb1(%20, %21 : !f, i1)
    ^bb8(%22: !runtime.scope):  // pred: ^bb4
      %23 = call @control_1(%22, %9, %10, %11, %12, %13) : (!runtime.scope, !f, !proof, !vk, !c, !p) -> !exec.outcome<(!f, i1)>
      %24 = "runtime.exit_scope"(%22, %23) : (!runtime.scope, !exec.outcome<(!f, i1)>) -> !exec.outcome<(!runtime.transfer<(!f, i1)>)>
      "exec.dispatch"(%24)[^bb9, ^bb2] : (!exec.outcome<(!runtime.transfer<(!f, i1)>)>) -> ()
    ^bb9(%25: !runtime.transfer<(!f, i1)>):  // pred: ^bb8
      %26 = "runtime.accept_transfer"(%arg0, %25) : (!runtime.scope, !runtime.transfer<(!f, i1)>) -> !exec.outcome<(!f, i1)>
      "exec.dispatch"(%26)[^bb10, ^bb2] : (!exec.outcome<(!f, i1)>) -> ()
    ^bb10(%27: !f, %28: i1):  // pred: ^bb9
      cf.br ^bb1(%27, %28 : !f, i1)
    }
    func.func private @control_0(%arg0: !runtime.scope, %arg1: !vk, %arg2: !c, %arg3: !p) -> !exec.outcome<(!f, i1)> attributes {no_inline, runtime.region} {
      %0 = "exec.apply"(%arg0) <{binding = @constant, parameters = ["0"], site = "zero"}> : (!runtime.scope) -> !exec.outcome<(!f)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb1(%1: !f):  // pred: ^bb0
      %2 = "exec.boolean"(%arg0) <{site = "absent", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%3: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!f, i1)>
      return %4 : !exec.outcome<(!f, i1)>
    ^bb3(%5: i1):  // pred: ^bb1
      %6 = "exec.complete"(%arg0, %1, %5) : (!runtime.scope, !f, i1) -> !exec.outcome<(!f, i1)>
      return %6 : !exec.outcome<(!f, i1)>
    }
    func.func private @control_1(%arg0: !runtime.scope, %arg1: !f, %arg2: !proof, %arg3: !vk, %arg4: !c, %arg5: !p) -> !exec.outcome<(!f, i1)> attributes {no_inline, runtime.region} {
      %0 = "exec.apply"(%arg0, %arg3, %arg4, %arg5, %arg1, %arg2) <{binding = @check_kernel, parameters = [], site = "opening"}> : (!runtime.scope, !vk, !c, !p, !f, !proof) -> !exec.outcome<(i1)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1: i1):  // pred: ^bb0
      %2 = "exec.complete"(%arg0, %arg1, %1) : (!runtime.scope, !f, i1) -> !exec.outcome<(!f, i1)>
      return %2 : !exec.outcome<(!f, i1)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!f, i1)>
      return %4 : !exec.outcome<(!f, i1)>
    }



 "runtime.binding"() {sym_name="commit_kernel",contract="pcs.commit",arguments=["multilinear.kzg.bls12-381/0"],implementation="",function_type=(!runtime.scope, !commitment.polynomial<"multilinear.kzg.bls12-381/0", "prover_key">, !poly.multilinear<"bls12-381.fr">) -> !exec.outcome<(!commitment.polynomial<"multilinear.kzg.bls12-381/0", "commitment">, !commitment.polynomial<"multilinear.kzg.bls12-381/0", "opening_state">)>} : ()->()
 "runtime.binding"() {sym_name="open_kernel",contract="pcs.open",arguments=["multilinear.kzg.bls12-381/0"],implementation="",function_type=(!runtime.scope, !commitment.polynomial<"multilinear.kzg.bls12-381/0", "opening_state">, !poly.point<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !commitment.polynomial<"multilinear.kzg.bls12-381/0", "proof">)>} : ()->()
 "runtime.binding"() {sym_name="check_kernel",contract="pcs.check",arguments=["multilinear.kzg.bls12-381/0"],implementation="",function_type=(!runtime.scope, !commitment.polynomial<"multilinear.kzg.bls12-381/0", "verifier_key">, !commitment.polynomial<"multilinear.kzg.bls12-381/0", "commitment">, !poly.point<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !commitment.polynomial<"multilinear.kzg.bls12-381/0", "proof">) -> !exec.outcome<(i1)>} : ()->()
 "runtime.binding"() {sym_name="equal_kernel",contract="pcs.equal",arguments=["multilinear.kzg.bls12-381/0"],implementation="",function_type=(!runtime.scope, !commitment.polynomial<"multilinear.kzg.bls12-381/0", "commitment">, !commitment.polynomial<"multilinear.kzg.bls12-381/0", "commitment">) -> !exec.outcome<(i1)>} : ()->()




 "runtime.binding"() {sym_name="constant",contract="field.constant",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>} : ()->()


 "protocol.func"() ({ ^entry(%state:!o,%pointP:!p,%pointV:!p,%key:!vk,%root:!c):
   %opened:2 = "protocol.local_call"(%state,%pointP) {callee=@open,role="P",site="open"} : (!o,!p)->(!f,!proof)
   %message = "protocol.local_call"(%opened#0,%opened#1) {callee=@pack_opening,role="P",site="pack"} : (!f,!proof)->!message
   %received = protocol.exchange %message {sender="P",receiver="V",site="opening_message"} : !message
   %checked:2 = "protocol.local_call"(%received,%key,%root,%pointV) {callee=@check_message,role="V",site="check"} : (!message,!vk,!c,!p)->(!f,i1)
   protocol.guard %checked#1 {owner="V",site="opening_check"}
   "protocol.return"(%checked#0) : (!f)->()
 }) {sym_name="opening",function_type=(!o,!p,!p,!vk,!c)->!f,roles=["P","V"],input_roles=[["P"],["P"],["V"],["V"],["V"]],output_roles=[["V"]]} : ()->()

 "protocol.func"() ({ ^entry(%T:!t,%pk:!pk,%vk:!vk,%root:!c,%r:!f,%claim:!f):
   %committed:2 = "protocol.local_call"(%pk,%T) {callee=@commit,role="P",site="commit"} : (!pk,!t)->(!c,!o)
   %emptyP = "protocol.local_call"() {callee=@empty_point,role="P",site="empty_P"} : ()->!p
   %emptyV = "protocol.local_call"() {callee=@empty_point,role="V",site="empty_V"} : ()->!p
   %pointP = "protocol.local_call"(%emptyP,%r) {callee=@append_point,role="P",site="point_P"} : (!p,!f)->!p
   %pointV = "protocol.local_call"(%emptyV,%r) {callee=@append_point,role="V",site="point_V"} : (!p,!f)->!p
   %value = "protocol.apply"(%committed#1,%pointP,%pointV,%vk,%root) {callee=@opening,roles=["P","V"],site="evaluation"} : (!o,!p,!p,!vk,!c)->!f
   %again = "protocol.apply"(%committed#1,%pointP,%pointV,%vk,%root) {callee=@opening,roles=["P","V"],site="repeated"} : (!o,!p,!p,!vk,!c)->!f
   %first_ok = algebra.field_equal %value,%claim : (!f,!f)->i1
   %second_ok = algebra.field_equal %again,%claim : (!f,!f)->i1
   %accepted = arith.andi %first_ok,%second_ok : i1
   "protocol.return"(%accepted) : (i1)->()
 }) {sym_name="main",function_type=(!t,!pk,!vk,!c,!f,!f)->i1,roles=["P","V"],input_roles=[["P"],["P"],["V"],["V"],["P","V"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
