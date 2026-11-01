#K = #protocol.oracle_kind<"table", [ui64,4:ui64]>
!H = !protocol.oracle<#K>
!D = !data.indices
module { "protocol.module"() ({
 relation.declare @position {kind="external",key="test/oracle-position",revision="0",signature=(ui64)->i1,purposes=["statement"]}
 "protocol.func"() ({
 ^entry(%data:!D,%anchor:!H,%position:ui64):
  %handle = "protocol.oracle_input"(%data,%anchor) {holder="P",receivers=["V"],shape_bounds={}} : (!D,!H)->!H
  %answer = "protocol.oracle_query"(%handle,%position) {owner="V",site="read"} : (!H,ui64)->ui64
  "protocol.return"(%answer) : (ui64)->()
 }) {sym_name="main",function_type=(!D,!H,ui64)->ui64,roles=["P","V"],input_roles=[["P"],["V"],["V"]],output_roles=[["V"]],contracts=[
   ["input","position",[@position,[["input",2:i64,"V"]]],unit,unit],
   ["output","answer",[@position,[["output",0:i64,"V"]]],unit,unit],
   ["continuation","reduction",[@position,[["input",2:i64,"V"]]],[@position,[["output",0:i64,"V"]]],unit]
 ]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
