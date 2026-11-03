#K = #protocol.oracle_kind<"table", [ui64, 2 : ui64]>
!H = !protocol.oracle<#K>
!S = !protocol.service_ref<"random.bls12-381.fr/0">
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%choice:i1,%data:!data.indices,%position:ui64,%coins:!S):
   %two = "data.index"() {value=2:ui64} : ()->ui64
   %handle = "protocol.oracle_send"(%data,%two) {shape_names=["rows"],shape_bounds={},sender="P",receivers=["V"],site="table"} : (!data.indices,ui64)->!H
   "protocol.branch"(%choice,%handle,%position,%coins) ({
   ^then(%word:!H,%index:ui64,%service:!S):
     %answer = "protocol.oracle_query"(%word,%index) {site="read",owner="V"} : (!H,ui64)->ui64
     "protocol.yield"() : ()->()
   }, {
   ^else(%word:!H,%index:ui64,%service:!S):
     %random = "protocol.query"(%service) {site="alternative_draw",owner="V",method="draw"} : (!S)->!algebra.field<"bls12-381.fr">
     "protocol.yield"() : ()->()
   }) {site="choose",roles=["P","V"],output_roles=[],alternatives=["then","else"]} : (i1,!H,ui64,!S)->()
   "protocol.return"() : ()->()
 }) {sym_name="main",function_type=(i1,!data.indices,ui64,!S)->(),roles=["P","V"],input_roles=[["P","V"],["P"],["V"],["V"]],output_roles=[]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
