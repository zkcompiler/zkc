module { "protocol.module"() ({
 "protocol.func"() ({
 ^entry(%choice:i1,%x:ui64,%coins:!protocol.service_ref<"random.bls12-381.fr/0">,%go:i1):
   %result = "protocol.branch"(%choice,%x,%coins,%go) ({
   ^then(%value:ui64,%service:!protocol.service_ref<"random.bls12-381.fr/0">,%enabled:i1):
     %received = protocol.exchange %value {site="chosen_message",sender="P",receiver="V"} : ui64
     protocol.guard %enabled {site="chosen_guard",owner="V"}
     "protocol.yield"(%received) : (ui64)->()
   }, {
   ^else(%value:ui64,%service:!protocol.service_ref<"random.bls12-381.fr/0">,%enabled:i1):
     %random = "protocol.query"(%service) {site="alternative_draw",owner="V",method="draw"} : (!protocol.service_ref<"random.bls12-381.fr/0">)->!algebra.field<"bls12-381.fr">
     %seven = "data.index"() {value=7:ui64} : ()->ui64
     "protocol.yield"(%seven) : (ui64)->()
   }) {site="choose",roles=["P","V"],output_roles=[["V"]],alternatives=["then","else"]} : (i1,ui64,!protocol.service_ref<"random.bls12-381.fr/0">,i1)->ui64
   "protocol.return"(%result) : (ui64)->()
 }) {sym_name="main",function_type=(i1,ui64,!protocol.service_ref<"random.bls12-381.fr/0">,i1)->ui64,roles=["P","V"],input_roles=[["P","V"],["P"],["V"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
