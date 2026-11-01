!Choice = !data.variant<#data.identity<["atom", "ControlChoice"]>, [#data.alternative<"none">, #data.alternative<"some", [ui64]>]>
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%choice:!Choice,%fallback:ui64):
   %result = "protocol.branch"(%choice,%fallback) ({
   ^none(%captured:ui64):
     "protocol.yield"(%captured) : (ui64)->()
   }, {
   ^some(%payload:ui64,%captured:ui64):
     "protocol.yield"(%payload) : (ui64)->()
   }) {site="choose",roles=["P","V"],output_roles=[["V"]],alternatives=["none","some"]} : (!Choice,ui64)->ui64
   "protocol.return"(%result) : (ui64)->()
 }) {sym_name="main",function_type=(!Choice,ui64)->ui64,roles=["P","V"],input_roles=[["P","V"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
