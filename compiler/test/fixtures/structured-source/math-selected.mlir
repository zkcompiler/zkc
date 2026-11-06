module { "protocol.module"() ({
 func.func private @choose(%outer:i1,%inner:i1,%x:ui64,%y:ui64)->(ui64,ui64) {
   %pair:2 = "data.branch"(%outer,%inner,%x,%y,%x) ({
   ^then(%choice:i1,%left:ui64,%right:ui64,%alias:ui64):
     %nested:2 = "data.branch"(%choice,%left,%right) ({
     ^then(%a:ui64,%b:ui64):
       "data.yield"(%a,%b) : (ui64,ui64)->()
     }, {
     ^else(%a:ui64,%b:ui64):
       "data.yield"(%b,%a) : (ui64,ui64)->()
     }) {alternatives=["then","else"]} : (i1,ui64,ui64)->(ui64,ui64)
     "data.yield"(%nested#0,%alias) : (ui64,ui64)->()
   }, {
   ^else(%choice:i1,%left:ui64,%right:ui64,%alias:ui64):
     "data.yield"(%right,%left) : (ui64,ui64)->()
   }) {alternatives=["then","else"]} : (i1,i1,ui64,ui64,ui64)->(ui64,ui64)
   func.return %pair#0,%pair#1 : ui64,ui64
 }
 "protocol.func"() ({ ^entry(%outer:i1,%inner:i1,%x:ui64,%y:ui64):
   %result:2 = func.call @choose(%outer,%inner,%x,%y) : (i1,i1,ui64,ui64)->(ui64,ui64)
   %accepted = "data.index_equal"(%result#0,%result#1) : (ui64,ui64)->i1
   "protocol.return"(%accepted,%result#0,%result#1) : (i1,ui64,ui64)->()
 }) {sym_name="main",origin=["math_selection",[]],function_type=(i1,i1,ui64,ui64)->(i1,ui64,ui64),roles=["P","V"],input_roles=[["P","V"],["P","V"],["P","V"],["P","V"]],output_roles=[["V"],["V"],["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
