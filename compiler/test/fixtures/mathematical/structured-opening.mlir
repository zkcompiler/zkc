!message = !local.variant<"variant:5b227a6b632e76617269616e74222c5b224f70656e696e67222c226e6f6e65222c5b5d2c5b2231222c2232225d2c22736f6d65222c226669656c643a626c7331322d3338312e6672222c2270726f6f663a6d756c74696c696e6561722e6b7a672e626c7331322d3338312f31222c5b2235222c2236225d2c5b2234222c2237225d2c5b2233222c2238225d2c5b2230222c2239225d5d5d">
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
 "local.binding"() {sym_name="constant",contract="field.constant",arguments=["bls12-381.fr"],implementation=""} : ()->()
 local.func @pack_opening(%v:!f,%proof:!proof) -> !message attributes {logical_origin=["pack_opening",[]]} {
   %message = "local.variant_inject"(%v,%proof) {alternative="some",site="present"} : (!f,!proof)->!message
   local.return %message : !message
 }
 local.func @check_message(%message:!message,%k:!vk,%c:!c,%p:!p) -> (!f,i1) attributes {logical_origin=["check_message",[]]} {
   %result:2 = "local.match"(%message,%k,%c,%p) ({ ^none(%key:!vk,%root:!c,%point:!p):
     %zero = "algebra.exec.field_constant"() {binding=@constant,parameters=["0"],site="zero"} : ()->!f
     %false = "local.bool_constant"() {value=false,site="absent"} : ()->i1
     "local.yield"(%zero,%false) : (!f,i1)->()
   }, { ^some(%v:!f,%proof:!proof,%key:!vk,%root:!c,%point:!p):
     %ok = "pcs.exec.check"(%key,%root,%point,%v,%proof) {binding=@check_kernel,parameters=[],site="opening"} : (!vk,!c,!p,!f,!proof)->i1
     "local.yield"(%v,%ok) : (!f,i1)->()
   }) {alternatives=["none","some"],site="presence"} : (!message,!vk,!c,!p)->(!f,i1)
   local.return %result#0,%result#1 : !f,i1
 }
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
