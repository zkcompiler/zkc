!Choice = !data.variant<#data.identity<["atom", "ConstructedControlChoice"]>, [#data.alternative<"none">, #data.alternative<"some", [ui64]>]>
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%x:ui64):
   %received = protocol.exchange %x {site="receive",sender="P",receiver="V"} : ui64
   %whole = "protocol.assemble_roles"(%x,%received) {roles=["P","V"]} : (ui64,ui64)->ui64
   %choice = "data.make"(%whole) {alternative="some"} : (ui64)->!Choice
   %result = "protocol.branch"(%choice) ({
     %zero = "data.index"() {value=0:ui64} : ()->ui64
     "protocol.yield"(%zero) : (ui64)->()
   }, {
   ^some(%payload:ui64):
     "protocol.yield"(%payload) : (ui64)->()
   }) {site="choose",roles=["P","V"],output_roles=[["V"]],alternatives=["none","some"]} : (!Choice)->ui64
   "protocol.return"(%result) : (ui64)->()
 }) {sym_name="main",function_type=(ui64)->ui64,roles=["P","V"],input_roles=[["P"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
