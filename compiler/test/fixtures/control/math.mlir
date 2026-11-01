module { "protocol.module"() ({
 func.func private @identity(%x:ui64)->ui64 { return %x : ui64 }
 func.func private @choose(%choice:i1,%x:ui64,%y:ui64)->ui64 {
   %result = "data.branch"(%choice,%x,%y) ({
   ^then(%left:ui64,%right:ui64):
     %forwarded = func.call @identity(%left) : (ui64)->ui64
     "data.yield"(%forwarded) : (ui64)->()
   }, {
   ^else(%left:ui64,%right:ui64):
     "data.yield"(%right) : (ui64)->()
   }) {alternatives=["then","else"]} : (i1,ui64,ui64)->ui64
   return %result : ui64
 }
 "protocol.func"() ({ ^entry(%choice:i1,%x:ui64,%y:ui64):
   %result = func.call @choose(%choice,%x,%y) : (i1,ui64,ui64)->ui64
   "protocol.return"(%result) : (ui64)->()
 }) {sym_name="main",function_type=(i1,ui64,ui64)->ui64,roles=["P"],input_roles=[["P"],["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
