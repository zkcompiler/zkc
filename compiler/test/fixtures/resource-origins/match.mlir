!s = !local.capability<"rng:bls12-381.fr">
!tag = !local.variant<"variant:5b227a6b632e76617269616e74222c5b2243686f696365222c226c656674222c5b5d2c5b2231222c2232225d2c227269676874222c5b2234222c2232225d2c5b2233222c2235225d2c5b2230222c2236225d5d5d">
module { "protocol.module"() ({
 local.func @step(%s:!s,%go:i1,%lo:ui64,%hi:ui64) -> !s attributes {logical_origin=["step",[]]} {
 %tag = "local.variant_inject"() {alternative="left",site="tag"} : ()->!tag
 %next = "local.match"(%tag,%s) ({ ^left(%a:!s):
   "local.yield"(%a) : (!s)->()
 }, { ^right(%b:!s):
   "local.yield"(%b) : (!s)->()
 }) {alternatives=["left","right"],site="choice"} : (!tag,!s)->!s
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
