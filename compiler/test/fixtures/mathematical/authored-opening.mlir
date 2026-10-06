!pk = !pcs.object<"multilinear.kzg.bls12-381/1", "prover_key">
!vk = !pcs.object<"multilinear.kzg.bls12-381/1", "verifier_key">
!c = !pcs.object<"multilinear.kzg.bls12-381/1", "commitment">
!o = !pcs.object<"multilinear.kzg.bls12-381/1", "opening_state">
!proof = !pcs.object<"multilinear.kzg.bls12-381/1", "proof">
!f = !algebra.field<"bls12-381.fr">
!t = !poly.multilinear<"bls12-381.fr">
!p = !poly.point<"bls12-381.fr">
module { "protocol.module"() ({
 "local.binding"() {sym_name="empty",contract="poly.empty_point",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="append",contract="poly.append_point",arguments=["bls12-381.fr"],implementation=""} : ()->()
 local.func @empty_point() -> !p attributes {logical_origin=["empty_point",[]]} {
   %p = "poly.exec.empty_point"() {binding=@empty,parameters=[],site="empty"} : ()->!p
   local.return %p : !p
 }
 local.func @append_point(%p:!p,%r:!f) -> !p attributes {logical_origin=["append_point",[]]} {
   %out = "poly.exec.append_point"(%p,%r) {binding=@append,parameters=[],site="append"} : (!p,!f)->!p
   local.return %out : !p
 }

 "local.binding"() {sym_name="commit_kernel",contract="pcs.commit",arguments=["multilinear.kzg.bls12-381/1"],implementation=""} : ()->()
 "local.binding"() {sym_name="open_kernel",contract="pcs.open",arguments=["multilinear.kzg.bls12-381/1"],implementation=""} : ()->()
 "local.binding"() {sym_name="check_kernel",contract="pcs.check",arguments=["multilinear.kzg.bls12-381/1"],implementation=""} : ()->()
 "local.binding"() {sym_name="equal_kernel",contract="pcs.equal",arguments=["multilinear.kzg.bls12-381/1"],implementation=""} : ()->()
 local.func @commit(%k:!pk,%t:!t) -> (!c,!o) attributes {logical_origin=["commit",[]]} {
   %r:2 = "pcs.exec.commit"(%k,%t) {binding=@commit_kernel,parameters=[],site="commit"} : (!pk,!t)->(!c,!o)
   local.return %r#0,%r#1 : !c,!o
 }
 local.func @open(%s:!o,%p:!p) -> (!f,!proof) attributes {logical_origin=["open",[]]} {
   %r:2 = "pcs.exec.open"(%s,%p) {binding=@open_kernel,parameters=[],site="open"} : (!o,!p)->(!f,!proof)
   local.return %r#0,%r#1 : !f,!proof
 }
 local.func @check(%k:!vk,%c:!c,%p:!p,%v:!f,%proof:!proof) -> i1 attributes {logical_origin=["check",[]]} {
   %ok = "pcs.exec.check"(%k,%c,%p,%v,%proof) {binding=@check_kernel,parameters=[],site="check"} : (!vk,!c,!p,!f,!proof)->i1
   local.return %ok : i1
 }
 local.func @same_root(%a:!c,%b:!c) -> i1 attributes {logical_origin=["same_root",[]]} {
   %ok = "pcs.exec.equal"(%a,%b) {binding=@equal_kernel,parameters=[],site="equal"} : (!c,!c)->i1
   local.return %ok : i1
 }
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
