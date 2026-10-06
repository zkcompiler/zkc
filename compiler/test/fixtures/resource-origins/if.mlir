!s = !local.capability<"rng:bls12-381.fr">
module { "protocol.module"() ({
 local.func @step(%s:!s,%go:i1,%lo:ui64,%hi:ui64) -> !s attributes {logical_origin=["step",[]]} {
 %next = "local.if"(%go,%s) ({ ^yes(%a:!s):
   "local.yield"(%a) : (!s)->()
 }, { ^no(%b:!s):
   "local.yield"(%b) : (!s)->()
 }) {site="choice"} : (i1,!s)->!s
 local.return %next : !s
 }
 "protocol.func"() ({ ^entry(%n:ui64,%s:!s,%go:i1,%lo:ui64,%hi:ui64):
  %done = "protocol.repeat"(%n,%s,%go,%lo,%hi) ({
   ^round(%i:ui64,%state:!s,%choice:i1,%lower:ui64,%upper:ui64):
    %next = "protocol.local_call"(%state,%choice,%lower,%upper) {callee=@step,role="P",site="step"} : (!s,i1,ui64,ui64)->!s
    "protocol.yield"(%next) : (!s)->()
  }) {site="rounds",carried=1:i64,maximum=8:i64,roles=["P"],carried_roles=[["P"]]} : (ui64,!s,i1,ui64,ui64)->!s
  "protocol.return"(%done) : (!s)->()
 }) {sym_name="main",function_type=(ui64,!s,i1,ui64,ui64)->!s,roles=["P"],input_roles=[["P"],["P"],["P"],["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
