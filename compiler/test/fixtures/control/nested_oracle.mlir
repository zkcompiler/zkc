#K = #protocol.oracle_kind<"table", [ui64, 2 : ui64]>
!H = !protocol.oracle<#K>
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%n:ui64,%choice:i1,%data:!data.indices):
   "protocol.repeat"(%n,%choice,%data) ({
   ^loop(%i:ui64,%enabled:i1,%rows:!data.indices):
     "protocol.branch"(%enabled,%rows) ({
     ^then(%captured:!data.indices):
       %two = "data.index"() {value=2:ui64} : ()->ui64
       %first = "protocol.oracle_send"(%captured,%two) {shape_names=["rows"],shape_bounds={},sender="P",receivers=["V"],site="first"} : (!data.indices,ui64)->!H
       "protocol.yield"() : ()->()
     }, {
     ^else(%captured:!data.indices):
       %two = "data.index"() {value=2:ui64} : ()->ui64
       %second = "protocol.oracle_send"(%captured,%two) {shape_names=["rows"],shape_bounds={},sender="P",receivers=["V"],site="second"} : (!data.indices,ui64)->!H
       "protocol.yield"() : ()->()
     }) {site="choose",roles=["P","V"],output_roles=[],alternatives=["then","else"]} : (i1,!data.indices)->()
     "protocol.yield"() : ()->()
   }) {site="rounds",carried=0:i64,maximum=3:i64,roles=["P","V"],carried_roles=[]} : (ui64,i1,!data.indices)->()
   "protocol.return"() : ()->()
 }) {sym_name="main",function_type=(ui64,i1,!data.indices)->(),roles=["P","V"],input_roles=[["P","V"],["P","V"],["P"]],output_roles=[]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
