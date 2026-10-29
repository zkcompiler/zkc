#K = #protocol.oracle_kind<"table", [ui64,4:ui64]>
!H = !protocol.oracle<#K>
!D = !algebra.indices
module { "protocol.module"() ({
 relation.declare @claim {kind="external",key="test/oracle-claim",revision="0",signature=(!D)->i1,purposes=["statement"]}
 "protocol.func"() ({
 ^entry(%data:!D,%anchor:!H,%position:ui64):
  %handle = "protocol.oracle_input"(%data,%anchor) {holder="P",receivers=["V"],shape_bounds={}} : (!D,!H)->!H
  "protocol.statement"(%anchor) {relation=@claim,selectors=["anchor"],target="selected",acceptance=3:i64} : (!H)->()
  %answer = "protocol.oracle_query"(%handle,%position) {owner="V",site="read"} : (!H,ui64)->ui64
  %accepted = "data.index_equal"(%answer,%position) : (ui64,ui64)->i1
  %parts:2 = "protocol.oracle_components"(%handle) {holder="P",receivers=["V"]} : (!H)->(!D,!H)
  "protocol.return"(%parts#0,%parts#1,%answer,%accepted) : (!D,!H,ui64,i1)->()
 }) {sym_name="main",function_type=(!D,!H,ui64)->(!D,!H,ui64,i1),roles=["P","V"],input_roles=[["P"],["V"],["V"]],output_roles=[["P"],["V"],["V"],["V"]],contracts=[
   ["input","premise",[@claim,[["anchor","input",1:i64]]],unit,unit],
   ["output","result",[@claim,[["anchor","output",1:i64]]],unit,unit],
   ["continuation","reduction",[@claim,[["anchor","input",1:i64]]],[@claim,[["anchor","output",1:i64]]],["output",3:i64,"V"]],
   ["target","decoy",[@claim,[["anchor","input",1:i64]]],unit,["output",3:i64,"V"]],
   ["target","selected",[@claim,[["anchor","input",1:i64]]],unit,["output",3:i64,"V"]]
 ]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
