
#K = #protocol.oracle_kind<"table", [ui64,4:ui64]>
!H = !protocol.oracle<#K>
!S = !protocol.oracle_sequence<#K,2>
!D = !algebra.indices
module { "protocol.module"() ({
 "protocol.func"() ({
 ^entry(%left:!D,%right:!D,%which:ui64,%position:ui64):
  %rows = "data.index"() {value=4 : ui64} : ()->ui64
  %a = "protocol.oracle_send"(%left,%rows) {shape_names=["rows"],shape_bounds={},sender="Alice",receivers=["V"],site="left"} : (!D,ui64)->!H
  %b = "protocol.oracle_send"(%right,%rows) {shape_names=["rows"],shape_bounds={},sender="Bob",receivers=["V"],site="right"} : (!D,ui64)->!H
  %empty = "protocol.oracle_sequence_empty"() : ()->!S
  %one = "protocol.oracle_sequence_append"(%empty,%a) {roles=["V"],site="first"} : (!S,!H)->!S
  %two = "protocol.oracle_sequence_append"(%one,%b) {roles=["V"],site="second"} : (!S,!H)->!S
  %chosen = "protocol.oracle_sequence_at"(%two,%which) {roles=["V"],site="select"} : (!S,ui64)->!H
  %answer = "protocol.oracle_query"(%chosen,%position) {owner="V",site="read"} : (!H,ui64)->ui64
  "protocol.return"(%answer) : (ui64)->()
 }) {sym_name="main",function_type=(!D,!D,ui64,ui64)->ui64,roles=["Alice","Bob","V"],input_roles=[["Alice"],["Bob"],["V"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
