#K = #protocol.oracle_kind<"table", [ui64, 2 : ui64]>
!H = !protocol.oracle<#K>
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%choice:i1,%data:!data.indices,%position:ui64):
   %handle = "protocol.branch"(%choice,%data) ({
   ^then(%rows:!data.indices):
     %two = "data.index"() {value=2:ui64} : ()->ui64
     %first = "protocol.oracle_send"(%rows,%two) {shape_names=["rows"],shape_bounds={},sender="P",receivers=["V"],site="first"} : (!data.indices,ui64)->!H
     "protocol.yield"(%first) : (!H)->()
   }, {
   ^else(%rows:!data.indices):
     %two = "data.index"() {value=2:ui64} : ()->ui64
     %second = "protocol.oracle_send"(%rows,%two) {shape_names=["rows"],shape_bounds={},sender="P",receivers=["V"],site="second"} : (!data.indices,ui64)->!H
     "protocol.yield"(%second) : (!H)->()
   }) {site="choose",roles=["P","V"],output_roles=[["P","V"]],alternatives=["then","else"]} : (i1,!data.indices)->!H
   %answer = "protocol.oracle_query"(%handle,%position) {site="read",owner="V"} : (!H,ui64)->ui64
   "protocol.return"(%answer) : (ui64)->()
 }) {sym_name="main",function_type=(i1,!data.indices,ui64)->ui64,roles=["P","V"],input_roles=[["P","V"],["P"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
