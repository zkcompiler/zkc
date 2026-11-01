#K = #protocol.oracle_kind<"table", [!algebra.field<"koala-bear.ext4-binomial3">,8:ui64]>
!F = !algebra.field<"koala-bear.ext4-binomial3">
!D = !data.field_vector<"koala-bear.ext4-binomial3">
!H = !protocol.oracle<#K>
module { "protocol.module"() ({
 "protocol.func"() ({
 ^entry(%data:!D,%other:!D,%position:ui64,%allow:i1):
  %rows = "data.index"() {value=8 : ui64} : ()->ui64
  %zero = "data.index"() {value=0 : ui64} : ()->ui64
  %one = "data.index"() {value=1 : ui64} : ()->ui64
  %four = "data.index"() {value=4 : ui64} : ()->ui64
  %a = "protocol.oracle_send"(%data,%rows) {shape_names=["rows"],shape_bounds={},sender="P",receivers=["V"],site="left"} : (!D,ui64)->!H
  %b = "protocol.oracle_send"(%other,%rows) {shape_names=["rows"],shape_bounds={},sender="P",receivers=["V"],site="right"} : (!D,ui64)->!H
  %x = "protocol.oracle_query"(%a,%zero) {owner="V",site="first"} : (!H,ui64)->!F
  %y = "protocol.oracle_query"(%a,%four) {owner="V",site="second"} : (!H,ui64)->!F
  %z = "protocol.oracle_query"(%a,%zero) {owner="V",site="duplicate"} : (!H,ui64)->!F
  %w = "protocol.oracle_query"(%b,%zero) {owner="V",site="distinct_anchor"} : (!H,ui64)->!F
  "protocol.guard"(%allow) {owner="V",site="barrier"} : (i1)->()
  %later = "protocol.oracle_query"(%a,%one) {owner="V",site="later"} : (!H,ui64)->!F
  "protocol.return"(%x,%y,%z,%w,%later) : (!F,!F,!F,!F,!F)->()
 }) {sym_name="main",function_type=(!D,!D,ui64,i1)->(!F,!F,!F,!F,!F),roles=["P","V"],input_roles=[["P"],["P"],["V"],["V"]],output_roles=[["V"],["V"],["V"],["V"],["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
