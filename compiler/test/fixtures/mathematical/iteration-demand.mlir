!f = !algebra.field<"bls12-381.fr">
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%n:ui64,%x:!f):
   %twice = algebra.field_add %x,%x : (!f,!f)->!f
   %out = "protocol.repeat"(%n,%x,%twice) ({ ^body(%i:ui64,%state:!f,%step:!f):
     %next = algebra.field_add %state,%step : (!f,!f)->!f
     "protocol.yield"(%next) : (!f)->()
   }) {site="rounds",carried=1:i64,maximum=8:i64,roles=["P"],carried_roles=[["P"]]} : (ui64,!f,!f)->!f
   "protocol.return"(%out) : (!f)->()
 }) {sym_name="main",function_type=(ui64,!f)->!f,roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
