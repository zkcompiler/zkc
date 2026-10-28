#K = #protocol.oracle_kind<"table", [ui64,4:ui64]>
!H = !protocol.oracle<#K>
!D = !algebra.indices
module { "protocol.module"() ({
 "protocol.func"() ({
 ^entry(%data:!D,%anchor:!H,%position:ui64):
  %handle = "protocol.oracle_input"(%data,%anchor) {holder="P",receivers=["V"],shape_bounds={}} : (!D,!H)->!H
  %answer = "protocol.oracle_query"(%handle,%position) {owner="V",site="read"} : (!H,ui64)->ui64
  "protocol.return"(%answer) : (ui64)->()
 }) {sym_name="main",function_type=(!D,!H,ui64)->ui64,roles=["P","V"],input_roles=[["P"],["V"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
