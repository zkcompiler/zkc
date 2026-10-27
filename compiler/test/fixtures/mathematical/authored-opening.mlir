!pk = !commitment.polynomial<"multilinear.kzg.bls12-381/0", "prover_key">
!vk = !commitment.polynomial<"multilinear.kzg.bls12-381/0", "verifier_key">
!c = !commitment.polynomial<"multilinear.kzg.bls12-381/0", "commitment">
!o = !commitment.polynomial<"multilinear.kzg.bls12-381/0", "opening_state">
!proof = !commitment.polynomial<"multilinear.kzg.bls12-381/0", "proof">
!f = !algebra.field<"bls12-381.fr">
!t = !poly.multilinear<"bls12-381.fr">
!p = !poly.point<"bls12-381.fr">
module { "protocol.module"() ({
 "runtime.binding"() {sym_name="empty",contract="poly.empty_point",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "runtime.binding"() {sym_name="append",contract="poly.append_point",arguments=["bls12-381.fr"],implementation=""} : ()->()
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



 "runtime.binding"() {sym_name="commit_kernel",contract="pcs.commit",arguments=["multilinear.kzg.bls12-381/0"],implementation=""} : ()->()
 "runtime.binding"() {sym_name="open_kernel",contract="pcs.open",arguments=["multilinear.kzg.bls12-381/0"],implementation=""} : ()->()
 "runtime.binding"() {sym_name="check_kernel",contract="pcs.check",arguments=["multilinear.kzg.bls12-381/0"],implementation=""} : ()->()
 "runtime.binding"() {sym_name="equal_kernel",contract="pcs.equal",arguments=["multilinear.kzg.bls12-381/0"],implementation=""} : ()->()




 "protocol.func"() ({ ^entry(%state:!o,%pointP:!p,%pointV:!p,%key:!vk,%root:!c):
   %opened:2 = "protocol.local_call"(%state,%pointP) {callee=@open,role="P",site="open"} : (!o,!p)->(!f,!proof)
   %value = protocol.exchange %opened#0 {sender="P",receiver="V",site="value"} : !f
   %proof = protocol.exchange %opened#1 {sender="P",receiver="V",site="proof"} : !proof
   %valid = "protocol.local_call"(%key,%root,%pointV,%value,%proof) {callee=@check,role="V",site="check"} : (!vk,!c,!p,!f,!proof)->i1
   protocol.guard %valid {owner="V",site="opening_check"}
   "protocol.return"(%value) : (!f)->()
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
