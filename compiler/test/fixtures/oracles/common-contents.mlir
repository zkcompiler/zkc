#K = #protocol.oracle_kind<"table", [ui64]>
!H = !protocol.oracle<#K>
!D = !algebra.indices
module { "protocol.module"() ({
 relation.declare @admissible {kind="external",key="test/holder-contents",revision="0",
  signature=(!D,!D,ui64,ui64)->i1,purposes=["witness","witness","parameter","parameter"]}
 "protocol.oracle"() ({
  ^bb0(%a:!H,%b:!H,%mapped:ui64,%extent:ui64,%position:ui64):
   %answer = "protocol.oracle_query"(%a,%position) {site="left"} : (!H,ui64)->ui64
   %unused = "protocol.oracle_query"(%b,%mapped) {site="right"} : (!H,ui64)->ui64
   "protocol.oracle_yield"(%answer) : (ui64)->()
 }) {sym_name="combine",function_type=(!H,!H,ui64,ui64,ui64)->ui64,kind=#K,
     shape_arguments={rows=3:ui64},shape_bounds={rows=4:ui64},admissibility=@admissible} : ()->()
 "protocol.func"() ({
  ^bb0(%left:!D,%right:!D,%unrelated:!D,%mapped:ui64,%extent:ui64,%position:ui64,%trips:ui64):
   %rows = "data.index"() {value="4"} : ()->ui64
   %a = "protocol.oracle_send"(%left,%rows) {shape_names=["rows"],shape_bounds={rows=4:ui64},
     sender="P",receivers=["V"],site="left"} : (!D,ui64)->!H
   %b = "protocol.oracle_send"(%right,%rows) {shape_names=["rows"],shape_bounds={rows=4:ui64},
     sender="P",receivers=["V"],site="right"} : (!D,ui64)->!H
   %received = "protocol.oracle_send"(%unrelated,%rows) {shape_names=["rows"],shape_bounds={rows=4:ui64},
     sender="Q",receivers=["P"],site="unrelated"} : (!D,ui64)->!H
   %last = "protocol.repeat"(%trips,%a,%b,%mapped,%extent) ({
    ^bb0(%iteration:ui64,%previous:!H,%other:!H,%map:ui64,%size:ui64):
     %next = "protocol.oracle_virtual"(%previous,%other,%map,%size) {callee=@combine,holder="P",receivers=["V"]} : (!H,!H,ui64,ui64)->!H
     "protocol.yield"(%next) : (!H)->()
   }) {site="chain",carried=1:i64,maximum=3:i64,roles=["P","V"],carried_roles=[["P","V"]]} : (ui64,!H,!H,ui64,ui64)->!H
   %contents = "protocol.oracle_contents"(%last) {owner="P"} : (!H)->!D
   %actual = "protocol.oracle_shape"(%last) {dimension="rows"} : (!H)->ui64
   %answer = "protocol.oracle_query"(%a,%position) {owner="V",site="query"} : (!H,ui64)->ui64
   "protocol.return"(%answer,%contents,%actual) : (ui64,!D,ui64)->()
 }) {sym_name="main",function_type=(!D,!D,!D,ui64,ui64,ui64,ui64)->(ui64,!D,ui64),roles=["P","Q","V"],
     input_roles=[["P"],["P"],["Q"],["P","V"],["P","V"],["V"],["P","V"]],output_roles=[["V"],["P"],["P","V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
