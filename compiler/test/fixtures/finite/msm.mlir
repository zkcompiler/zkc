!F = !algebra.field<"bls12-381.fr">
!G = !algebra.group<"bls12-381.g1">
!V = !algebra.field_vector<"bls12-381.fr">
!GS = !algebra.group_vector<"bls12-381.g1">
module { "protocol.module"() ({
 "local.binding"() {sym_name="generator",contract="curve.generator",arguments=["bls12-381.g1"],implementation=""} : ()->()
 "local.binding"() {sym_name="empty",contract="curve.empty",arguments=["bls12-381.g1"],implementation=""} : ()->()
 "local.binding"() {sym_name="append",contract="curve.append",arguments=["bls12-381.g1"],implementation=""} : ()->()
 "local.binding"() {sym_name="scale",contract="curve.scale",arguments=["bls12-381.g1"],implementation=""} : ()->()
 "local.binding"() {sym_name="add",contract="curve.add",arguments=["bls12-381.g1"],implementation=""} : ()->()
 "local.binding"() {sym_name="equal",contract="curve.equal",arguments=["bls12-381.g1"],implementation=""} : ()->()
 "data.domain"() ({ ^entry(%points:!GS,%scalars:!V):
   %p = "data.domain_elements"(%points) : (!GS)->!data.domain<!G>
   %s = "data.domain_elements"(%scalars) : (!V)->!data.domain<!F>
   %d = "data.domain_zip"(%p,%s) : (!data.domain<!G>,!data.domain<!F>)->!data.domain<!G,!F>
   "data.domain_yield"(%d) : (!data.domain<!G,!F>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!GS,!V)->!data.domain<!G,!F>} : ()->()
 local.func private @step(%state:!G,%point:!G,%scalar:!F,%points:!GS,%scalars:!V) -> !G attributes {logical_origin=["step",[]]} {
   %term = "algebra.exec.group_scale"(%point,%scalar) {binding=@scale,parameters=[],site="term"} : (!G,!F)->!G
   %next = "algebra.exec.group_add"(%state,%term) {binding=@add,parameters=[],site="add"} : (!G,!G)->!G
   local.return %next : !G
 }
 "local.finite_fold"() {sym_name="fold",function_type=(!GS,!V,!G)->!G,domain=@items,step=@step} : ()->()
 local.func @work(%scalars:!V,%init:!F,%expected:!F) -> i1 attributes {logical_origin=["work",[]]} {
   %g = "algebra.exec.group_generator"() {binding=@generator,parameters=[],site="generator"} : ()->!G
   %e = "algebra.exec.group_empty"() {binding=@empty,parameters=[],site="empty"} : ()->!GS
   %one = "algebra.exec.group_append"(%e,%g) {binding=@append,parameters=[],site="one"} : (!GS,!G)->!GS
   %two = "algebra.exec.group_append"(%one,%g) {binding=@append,parameters=[],site="two"} : (!GS,!G)->!GS
   %initial = "algebra.exec.group_scale"(%g,%init) {binding=@scale,parameters=[],site="init"} : (!G,!F)->!G
   %r = local.apply @fold(%two,%scalars,%initial) {site="fold"} : (!GS,!V,!G)->!G
   %wanted = "algebra.exec.group_scale"(%g,%expected) {binding=@scale,parameters=[],site="expected"} : (!G,!F)->!G
   %ok = "algebra.exec.group_equal"(%r,%wanted) {binding=@equal,parameters=[],site="equal"} : (!G,!G)->i1
   local.return %ok : i1
 }
 "protocol.func"() ({ ^entry(%scalars:!V,%init:!F,%expected:!F):
   %r = "protocol.local_call"(%scalars,%init,%expected) {callee=@work,role="P",site="work"} : (!V,!F,!F)->i1
   "protocol.return"(%r) : (i1)->()
 }) {sym_name="main",function_type=(!V,!F,!F)->i1,roles=["P"],input_roles=[["P"],["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
