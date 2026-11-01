#K = #protocol.oracle_kind<"table", [ui64]>
!H = !protocol.oracle<#K>
!D = !data.indices
module { "protocol.module"() ({
 "protocol.func"() ({
 ^entry(%data:!D,%rows:ui64,%position:ui64):
  %handle = "protocol.oracle_send"(%data,%rows) {sender="P",receivers=["V"],shape_names=["rows"],shape_bounds={rows=8:ui64},site="word"} : (!D,ui64)->!H
  %answer = "protocol.oracle_query"(%handle,%position) {owner="V",site="read"} : (!H,ui64)->ui64
  "protocol.return"(%answer) : (ui64)->()
 }) {sym_name="main",function_type=(!D,ui64,ui64)->ui64,roles=["P","V"],input_roles=[["P"],["P","V"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
