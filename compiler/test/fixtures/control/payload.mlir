!Choice = !data.variant<#data.identity<["atom", "PayloadControlChoice"]>, [#data.alternative<"none">, #data.alternative<"some", [i1]>]>
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%choice:!Choice):
   "protocol.branch"(%choice) ({
     "protocol.yield"() : ()->()
   }, {
   ^some(%payload:i1):
     "protocol.branch"(%payload) ({
       "protocol.yield"() : ()->()
     }, {
       "protocol.yield"() : ()->()
     }) {site="payload_choice",roles=["P","V"],output_roles=[],alternatives=["then","else"]} : (i1)->()
     "protocol.yield"() : ()->()
   }) {site="choose",roles=["P","V"],output_roles=[],alternatives=["none","some"]} : (!Choice)->()
   "protocol.return"() : ()->()
 }) {sym_name="main",function_type=(!Choice)->(),roles=["P","V"],input_roles=[["P","V"]],output_roles=[]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
