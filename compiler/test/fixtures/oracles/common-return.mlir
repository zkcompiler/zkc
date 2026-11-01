#K = #protocol.oracle_kind<"table", [ui64,4:ui64]>
!H = !protocol.oracle<#K>
!D = !data.indices
module { "protocol.module"() ({
 relation.declare @admissible {kind="external",key="test/return-view",revision="0",signature=(!D)->i1,purposes=["witness"]}
 "protocol.oracle"() ({
 ^entry(%handle:!H,%position:ui64):
  %answer = "protocol.oracle_query"(%handle,%position) {site="child"} : (!H,ui64)->ui64
  "protocol.oracle_yield"(%answer) : (ui64)->()
 }) {sym_name="view",function_type=(!H,ui64)->ui64,kind=#K,shape_arguments={},shape_bounds={},admissibility=@admissible} : ()->()
 "protocol.func"() ({
 ^entry(%data:!D,%anchor:!H,%position:ui64):
  %handle = "protocol.oracle_input"(%data,%anchor) {shape_bounds={},holder="A",receivers=["B"]} : (!D,!H)->!H
  %parts:2 = "protocol.oracle_components"(%handle) {holder="A",receivers=["B"]} : (!H)->(!D,!H)
  %answer = "protocol.oracle_query"(%handle,%position) {owner="B",site="query"} : (!H,ui64)->ui64
  "protocol.return"(%parts#0,%parts#1,%answer) : (!D,!H,ui64)->()
 }) {sym_name="reader",function_type=(!D,!H,ui64)->(!D,!H,ui64),roles=["A","B"],input_roles=[["A"],["B"],["B"]],output_roles=[["A"],["B"],["B"]]} : ()->()
 "protocol.func"() ({
 ^entry(%data:!D,%anchor:!H,%position:ui64):
  %handle = "protocol.oracle_input"(%data,%anchor) {shape_bounds={},holder="P",receivers=["V"]} : (!D,!H)->!H
  %parts:2 = "protocol.oracle_components"(%handle) {holder="P",receivers=["V"]} : (!H)->(!D,!H)
  %returned:3 = "protocol.apply"(%parts#0,%parts#1,%position) {callee=@reader,roles=["P","V"],site="inner"} : (!D,!H,ui64)->(!D,!H,ui64)
  "protocol.return"(%returned#0,%returned#1,%returned#2) : (!D,!H,ui64)->()
 }) {sym_name="wrapper",function_type=(!D,!H,ui64)->(!D,!H,ui64),roles=["P","V"],input_roles=[["P"],["V"],["V"]],output_roles=[["P"],["V"],["V"]]} : ()->()
 "protocol.func"() ({
 ^entry(%data:!D,%trips:ui64,%position:ui64):
  %rows = "data.index"() {value=4 : ui64} : ()->ui64
  %a = "protocol.oracle_send"(%data,%rows) {shape_names=["rows"],shape_bounds={},sender="P",receivers=["V"],site="first"} : (!D,ui64)->!H
  %b = "protocol.oracle_send"(%data,%rows) {shape_names=["rows"],shape_bounds={},sender="P",receivers=["V"],site="equal_data"} : (!D,ui64)->!H
  %last = "protocol.repeat"(%trips,%a) ({
   ^body(%iteration:ui64,%previous:!H):
    %next = "protocol.oracle_virtual"(%previous) {callee=@view,holder="P",receivers=["V"]} : (!H)->!H
    "protocol.yield"(%next) : (!H)->()
  }) {site="chain",carried=1:i64,maximum=3:i64,roles=["P","V"],carried_roles=[["P","V"]]} : (ui64,!H)->!H
  %parts:2 = "protocol.oracle_components"(%last) {holder="P",receivers=["V"]} : (!H)->(!D,!H)
  %returned:3 = "protocol.apply"(%parts#0,%parts#1,%position) {callee=@wrapper,roles=["P","V"],site="outer"} : (!D,!H,ui64)->(!D,!H,ui64)
  %rebound = "protocol.oracle_input"(%returned#0,%returned#1) {shape_bounds={},holder="P",receivers=["V"]} : (!D,!H)->!H
  %view:2 = "protocol.oracle_components"(%rebound) {holder="P",receivers=["V"]} : (!H)->(!D,!H)
  %other:2 = "protocol.oracle_components"(%b) {holder="P",receivers=["V"]} : (!H)->(!D,!H)
  "protocol.return"(%view#0,%view#1,%view#0,%view#1,%other#0,%other#1,%returned#2) : (!D,!H,!D,!H,!D,!H,ui64)->()
 }) {sym_name="main",function_type=(!D,ui64,ui64)->(!D,!H,!D,!H,!D,!H,ui64),roles=["P","V"],input_roles=[["P"],["P","V"],["V"]],output_roles=[["P"],["V"],["P"],["V"],["P"],["V"],["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
