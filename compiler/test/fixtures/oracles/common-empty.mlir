#K = #protocol.oracle_kind<"table", [ui64]>
!H = !protocol.oracle<#K>
!S = !protocol.oracle_sequence<#K,2>
module { "protocol.module"() ({
 "protocol.func"() ({
 ^entry(%marker:ui64):
  %empty = "protocol.oracle_sequence_empty"() : ()->!S
  %length = "protocol.oracle_sequence_length"(%empty) : (!S)->ui64
  "protocol.return"(%length) : (ui64)->()
 }) {sym_name="main",function_type=(ui64)->ui64,roles=["P","V"],input_roles=[["P","V"]],output_roles=[["V"]]} : ()->()
 "protocol.func"() ({
 ^entry(%marker:ui64,%index:ui64):
  %sent = "protocol.exchange"(%marker) {sender="P",receiver="V",site="before_deliver"} : (ui64)->ui64
  %empty = "protocol.oracle_sequence_empty"() : ()->!S
  %never = "protocol.oracle_sequence_at"(%empty,%index) {roles=["V"],site="select"} : (!S,ui64)->!H
  "protocol.return"(%sent) : (ui64)->()
 }) {sym_name="at",function_type=(ui64,ui64)->ui64,roles=["P","V"],input_roles=[["P"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
