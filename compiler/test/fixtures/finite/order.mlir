!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
!I = !algebra.indices
module { "protocol.module"() ({
 "local.binding"() {sym_name="mul",contract="index.mul",arguments=[],implementation=""} : ()->()
 "local.binding"() {sym_name="add",contract="index.add",arguments=[],implementation=""} : ()->()
 "data.domain"() ({ ^entry(%xs:!V,%lo:ui64,%hi:ui64):
   %i = "data.domain_indices"(%xs) {axis=0:i64} : (!V)->!data.domain<ui64>
   %j = "data.domain_range"(%lo,%hi) : (ui64,ui64)->!data.domain<ui64>
   %d = "data.domain_product"(%i,%j) : (!data.domain<ui64>,!data.domain<ui64>)->!data.domain<ui64,ui64>
   "data.domain_yield"(%d) : (!data.domain<ui64,ui64>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V,ui64,ui64)->!data.domain<ui64,ui64>} : ()->()
 local.func private @body(%i:ui64,%j:ui64,%xs:!V,%lo:ui64,%hi:ui64,%base:ui64) -> ui64 attributes {logical_origin=["body",[]]} {
   %major = "algebra.exec.index_mul"(%i,%base) {binding=@mul,parameters=[],site="major"} : (ui64,ui64)->ui64
   %value = "algebra.exec.index_add"(%major,%j) {binding=@add,parameters=[],site="value"} : (ui64,ui64)->ui64
   local.return %value : ui64
 }
 "local.finite_collect"() {sym_name="collect",function_type=(!V,ui64,ui64,ui64)->!I,domain=@items,body=@body} : ()->()
 local.func @work(%xs:!V,%lo:ui64,%hi:ui64,%base:ui64) -> !I attributes {logical_origin=["work",[]]} {
   %r = local.apply @collect(%xs,%lo,%hi,%base) {site="collect"} : (!V,ui64,ui64,ui64)->!I
   local.return %r : !I
 }
 "protocol.func"() ({ ^entry(%xs:!V,%lo:ui64,%hi:ui64,%base:ui64):
   %r = "protocol.local_call"(%xs,%lo,%hi,%base) {callee=@work,role="P",site="work"} : (!V,ui64,ui64,ui64)->!I
   "protocol.return"(%r) : (!I)->()
 }) {sym_name="main",function_type=(!V,ui64,ui64,ui64)->!I,roles=["P"],input_roles=[["P"],["P"],["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
