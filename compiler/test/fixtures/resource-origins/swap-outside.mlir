!s = !local.capability<"rng:bls12-381.fr">
module { "protocol.module"() ({
 local.func @swap(%a:!s,%b:!s,%lo:ui64,%hi:ui64) -> (!s,!s) attributes {logical_origin=["swap",[]]} {
  %next:2 = "local.for"(%lo,%hi,%a,%b) ({ ^body(%i:ui64,%x:!s,%y:!s):
   "local.yield"(%y,%x) : (!s,!s)->()
  }) {site="inner"} : (ui64,ui64,!s,!s)->(!s,!s)
  local.return %next#0,%next#1 : !s,!s
 }
 "protocol.func"() ({ ^entry(%n:ui64,%a:!s,%b:!s,%lo:ui64,%hi:ui64):
  %done:2 = "protocol.local_call"(%a,%b,%lo,%hi) {callee=@swap,role="P",site="swap"} : (!s,!s,ui64,ui64)->(!s,!s)
  "protocol.return"(%done#0,%done#1) : (!s,!s)->()
 }) {sym_name="main",function_type=(ui64,!s,!s,ui64,ui64)->(!s,!s),roles=["P"],input_roles=[["P"],["P"],["P"],["P"],["P"]],output_roles=[["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
