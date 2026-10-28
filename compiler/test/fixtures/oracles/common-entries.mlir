#K = #protocol.oracle_kind<"table", [ui64,4:ui64]>
!H = !protocol.oracle<#K>
!D = !algebra.indices
module { "protocol.module"() ({
 relation.declare @admissible {kind="external",key="test/view",revision="0",signature=(!D)->i1,purposes=["witness"]}
 relation.declare @_oracle_common_local_0_0 {kind="external",key="test/local-name",revision="0",signature=(ui64)->i1,purposes=["witness"]}
 relation.declare @_oracle_allocate_0_0 {kind="external",key="test/allocator-name",revision="0",signature=(ui64)->i1,purposes=["witness"]}
 "protocol.oracle"() ({
 ^entry(%handle:!H,%position:ui64):
  %answer = "protocol.oracle_query"(%handle,%position) {site="child"} : (!H,ui64)->ui64
  "protocol.oracle_yield"(%answer) : (ui64)->()
 }) {sym_name="view",function_type=(!H,ui64)->ui64,kind=#K,shape_arguments={},shape_bounds={},admissibility=@admissible} : ()->()
 "protocol.func"() ({
 ^entry(%data:!D,%position:ui64):
  %rows = "data.index"() {value="4"} : ()->ui64
  %base = "protocol.oracle_send"(%data,%rows) {shape_names=["rows"],shape_bounds={},sender="P",receivers=["V"],site="base"} : (!D,ui64)->!H
  %virtual = "protocol.oracle_virtual"(%base) {callee=@view,holder="P",receivers=["V"]} : (!H)->!H
  %answer = "protocol.oracle_query"(%virtual,%position) {owner="V",site="query"} : (!H,ui64)->ui64
  "protocol.return"(%answer) : (ui64)->()
 }) {sym_name="main",function_type=(!D,ui64)->ui64,roles=["P","V"],input_roles=[["P"],["V"]],output_roles=[["V"]]} : ()->()
 "protocol.func"() ({
 ^entry(%data:!D,%position:ui64):
  %rows = "data.index"() {value="4"} : ()->ui64
  %base = "protocol.oracle_send"(%data,%rows) {shape_names=["rows"],shape_bounds={},sender="P",receivers=["V"],site="base"} : (!D,ui64)->!H
  %virtual = "protocol.oracle_virtual"(%base) {callee=@view,holder="P",receivers=["V"]} : (!H)->!H
  %answer = "protocol.oracle_query"(%virtual,%position) {owner="V",site="query"} : (!H,ui64)->ui64
  "protocol.return"(%answer) : (ui64)->()
 }) {sym_name="companion",function_type=(!D,ui64)->ui64,roles=["P","V"],input_roles=[["P"],["V"]],output_roles=[["V"]]} : ()->()
 "protocol.func"() ({
 ^entry(%first:ui64,%second:ui64):
  "protocol.return"(%first) : (ui64)->()
 }) {sym_name="ordinary",function_type=(ui64,ui64)->ui64,roles=["P","V"],input_roles=[["V"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
