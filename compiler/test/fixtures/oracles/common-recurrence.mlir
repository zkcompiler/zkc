#K = #protocol.oracle_kind<"table", [ui64, 4 : ui64]>
!H = !protocol.oracle<#K>
!D = !algebra.indices
#B = #protocol.oracle_kind<"table", [ui64, 4 : ui64]>
!B = !protocol.oracle<#B>
!BD = !algebra.indices
module { "protocol.module"() ({
 relation.declare @admissible {kind="external",key="test/controller",revision="0",
  signature=(!D,!BD,ui64)->i1,purposes=["witness","witness","parameter"]}
 "protocol.oracle"() ({
  ^bb0(%a:!H,%b:!B,%mapped:ui64,%position:ui64):
   %answer = "protocol.oracle_query"(%a,%position) {site="left"} : (!H,ui64)->ui64
   %unused = "protocol.oracle_query"(%b,%mapped) {site="right"} : (!B,ui64)->ui64
   "protocol.oracle_yield"(%answer) : (ui64)->()
 }) {sym_name="combine",function_type=(!H,!B,ui64,ui64)->ui64,kind=#K,
     shape_arguments={},shape_bounds={},admissibility=@admissible} : ()->()
 "protocol.func"() ({
  ^bb0(%left:!D,%right:!BD,%mapped:ui64,%position:ui64,%trips:ui64):
   %rows = "data.index"() {value=4 : ui64} : ()->ui64
   %a = "protocol.oracle_send"(%left,%rows) {shape_names=["rows"],shape_bounds={},
     sender="P",receivers=["V"],site="left"} : (!D,ui64)->!H
   %b = "protocol.oracle_send"(%right,%rows) {shape_names=["rows"],shape_bounds={},
     sender="P",receivers=["V"],site="right"} : (!BD,ui64)->!B
   %last = "protocol.repeat"(%trips,%a,%b,%mapped) ({
    ^bb0(%iteration:ui64,%previous:!H,%other:!B,%map:ui64):
     %next = "protocol.oracle_virtual"(%previous,%other,%map) {callee=@combine,holder="P",receivers=["V"]} : (!H,!B,ui64)->!H
     "protocol.yield"(%next) : (!H)->()
   }) {site="chain",carried=1:i64,maximum=3:i64,roles=["P","V"],carried_roles=[["P","V"]]} : (ui64,!H,!B,ui64)->!H
   %answer = "protocol.oracle_query"(%last,%position) {owner="V",site="query"} : (!H,ui64)->ui64
   "protocol.return"(%answer) : (ui64)->()
 }) {sym_name="main",function_type=(!D,!BD,ui64,ui64,ui64)->ui64,roles=["P","V"],
     input_roles=[["P"],["P"],["P","V"],["V"],["P","V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
