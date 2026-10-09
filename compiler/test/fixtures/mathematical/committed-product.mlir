!pk = !pcs.object<"multilinear.kzg.bls12-381/0", "prover_key">
!vk = !pcs.object<"multilinear.kzg.bls12-381/0", "verifier_key">
!c = !pcs.object<"multilinear.kzg.bls12-381/0", "commitment">
!o = !pcs.object<"multilinear.kzg.bls12-381/0", "opening_state">
!proof = !pcs.object<"multilinear.kzg.bls12-381/0", "proof">
!f = !algebra.field<"bls12-381.fr">
!t = !poly.multilinear<"bls12-381.fr">
!p = !poly.point<"bls12-381.fr">
!a = tensor<3x!f>
!q = !poly.polynomial<"bls12-381.fr", 1>
!rng = !protocol.service_ref<"random.bls12-381.fr/0">
!state = !local.variant<"variant:5b227a6b632e76617269616e742f30222c5b22706f6c792e726573696475616c2e70726f64756374222c227374617465222c22706f696e743a626c7331322d3338312e6672222c227461626c653a626c7331322d3338312e6672222c5b2232222c2233222c2233225d2c5b2231222c2234225d2c5b2235225d2c5b2230222c2236225d5d5d">
module { "protocol.module"() ({
 "poly.recipe"() ({ ^slots(%a:!f,%b:!f):
   %p = algebra.field_multiply %a, %b : (!f,!f)->!f
   "poly.recipe_yield"(%p) : (!f)->()
 }) {sym_name="product",degree=2:i64} : ()->()
 "poly.realize"() {sym_name="init",recipe=@product,kind="init",function_type=(ui64,!t,!t)->!state} : ()->()
 "poly.realize"() {sym_name="bind",recipe=@product,kind="bind",function_type=(!state,!f)->!state} : ()->()
 "poly.realize"() {sym_name="round",recipe=@product,kind="round",function_type=(!state)->!a} : ()->()
 "poly.realize"() {sym_name="finish",recipe=@product,kind="finish",function_type=(!state)->(!p,!f)} : ()->()
 "poly.realize"() {sym_name="evaluate",recipe=@product,kind="evaluate",function_type=(!p,!t,!t)->!f} : ()->()
 "local.binding"() {sym_name="arity_kernel",contract="poly.table_arity",arguments=["bls12-381.fr"],implementation=""} : ()->()
 local.func @table_arity(%t:!t) -> ui64 attributes {logical_origin=["table_arity",[]]} {
   %n = "poly.exec.table_arity"(%t) {binding=@arity_kernel,parameters=[],site="arity"} : (!t)->ui64
   local.return %n : ui64
 }
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

 "local.binding"() {sym_name="commit_kernel",contract="pcs.commit",arguments=["multilinear.kzg.bls12-381/0"],implementation=""} : ()->()
 "local.binding"() {sym_name="open_kernel",contract="pcs.open",arguments=["multilinear.kzg.bls12-381/0"],implementation=""} : ()->()
 "local.binding"() {sym_name="check_kernel",contract="pcs.check",arguments=["multilinear.kzg.bls12-381/0"],implementation=""} : ()->()
 "local.binding"() {sym_name="equal_kernel",contract="pcs.equal",arguments=["multilinear.kzg.bls12-381/0"],implementation=""} : ()->()
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
 "protocol.func"() ({ ^entry(%n:ui64,%T:!t,%U:!t,%claim:!f,%coins:!rng,%pk:!pk,%vk:!vk,%expectedT:!c,%expectedU:!c):
   %committedT:2 = "protocol.local_call"(%pk,%T) {callee=@commit,role="P",site="commit_T"} : (!pk,!t)->(!c,!o)
   %committedU:2 = "protocol.local_call"(%pk,%U) {callee=@commit,role="P",site="commit_U"} : (!pk,!t)->(!c,!o)
   %rootT = protocol.exchange %committedT#0 {sender="P",receiver="V",site="root_T"} : !c
   %rootU = protocol.exchange %committedU#0 {sender="P",receiver="V",site="root_U"} : !c
   %matchesT = "protocol.local_call"(%rootT,%expectedT) {callee=@same_root,role="V",site="expected_T"} : (!c,!c)->i1
   protocol.guard %matchesT {owner="V",site="root_T_check"}
   %matchesU = "protocol.local_call"(%rootU,%expectedU) {callee=@same_root,role="V",site="expected_U"} : (!c,!c)->i1
   protocol.guard %matchesU {owner="V",site="root_U_check"}
   %count = protocol.exchange %n {sender="P",receiver="V",site="arity"} : ui64
   %initial = "protocol.local_call"(%n,%T,%U) {callee=@init,role="P",site="initialize"} : (ui64,!t,!t)->!state
   %count_ok = "data.index_equal"(%count,%n) : (ui64,ui64)->i1
   protocol.guard %count_ok {owner="V",site="arity_check"}
   %empty = "protocol.local_call"() {callee=@empty_point,role="V",site="empty_point"} : ()->!p
   %done:3 = "protocol.repeat"(%count,%initial,%empty,%claim,%coins) ({
   ^body(%i:ui64,%state:!state,%point:!p,%current:!f,%random:!rng):
     %coeffs = "protocol.local_call"(%state) {callee=@round,role="P",site="round_coefficients"} : (!state)->!a
     %received = protocol.exchange %coeffs {sender="P",receiver="V",site="round_message"} : !a
     %q = "poly.from_coefficients"(%received) : (!a)->!q
     %zero = "algebra.constant"() {value="0"} : ()->!f
     %one = "algebra.constant"() {value="1"} : ()->!f
     %q0 = "poly.evaluate"(%q,%zero) : (!q,!f)->!f
     %q1 = "poly.evaluate"(%q,%one) : (!q,!f)->!f
     %sum = algebra.field_add %q0,%q1 : (!f,!f)->!f
     %ok = algebra.field_equal %sum,%current : (!f,!f)->i1
     protocol.guard %ok {owner="V",site="boundary"}
     %r = "protocol.query"(%random) {method="draw",owner="V",site="draw"} : (!rng)->!f
     %rP = protocol.exchange %r {sender="V",receiver="P",site="challenge"} : !f
     %next_state = "protocol.local_call"(%state,%rP) {callee=@bind,role="P",site="bind"} : (!state,!f)->!state
     %next_point = "protocol.local_call"(%point,%r) {callee=@append_point,role="V",site="append_point"} : (!p,!f)->!p
     %next_claim = "poly.evaluate"(%q,%r) : (!q,!f)->!f
     "protocol.yield"(%next_state,%next_point,%next_claim) : (!state,!p,!f)->()
   }) {site="rounds",carried=3:i64,maximum=8:i64,roles=["P","V"],carried_roles=[["P"],["V"],["V"]]} : (ui64,!state,!p,!f,!rng)->(!state,!p,!f)
   %finished:2 = "protocol.local_call"(%done#0) {callee=@finish,role="P",site="finish"} : (!state)->(!p,!f)
   %valueT = "protocol.apply"(%committedT#1,%finished#0,%done#1,%vk,%expectedT) {callee=@opening,roles=["P","V"],site="open_T"} : (!o,!p,!p,!vk,!c)->!f
   %valueU = "protocol.apply"(%committedU#1,%finished#0,%done#1,%vk,%expectedU) {callee=@opening,roles=["P","V"],site="open_U"} : (!o,!p,!p,!vk,!c)->!f
   %actual = algebra.field_multiply %valueT,%valueU : (!f,!f)->!f
   %accepted = algebra.field_equal %actual,%done#2 : (!f,!f)->i1
   "protocol.return"(%accepted,%finished#0,%finished#1) : (i1,!p,!f)->()
 }) {sym_name="main",function_type=(ui64,!t,!t,!f,!rng,!pk,!vk,!c,!c)->(i1,!p,!f),roles=["P","V"],input_roles=[["P","V"],["P"],["P"],["V"],["V"],["P"],["V"],["V"],["V"]],output_roles=[["V"],["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
