!F = !algebra.field<"bls12-381.fr">
module { "protocol.module"() ({
 local.func @first(%lo:ui64,%hi:ui64,%a:!F,%b:!F) -> (!F,!F) attributes {logical_origin=["first",[]]} {
   %r:2 = "local.for"(%lo,%hi,%a,%b) ({
   ^body(%i:ui64,%x:!F,%y:!F):
     %done = "local.bool_constant"() {value=false,site="finish"} : ()->i1
     "local.condition"(%done,%y,%x) : (i1,!F,!F)->()
   }) {site="loop"} : (ui64,ui64,!F,!F)->(!F,!F)
   local.return %r#0,%r#1 : !F,!F
 }
 "protocol.func"() ({ ^entry(%lo:ui64,%hi:ui64,%a:!F,%b:!F):
   %r:2 = "protocol.local_call"(%lo,%hi,%a,%b) {callee=@first,role="P",site="first"} : (ui64,ui64,!F,!F)->(!F,!F)
   "protocol.return"(%r#0,%r#1) : (!F,!F)->()
 }) {sym_name="main",function_type=(ui64,ui64,!F,!F)->(!F,!F),roles=["P"],input_roles=[["P"],["P"],["P"],["P"]],output_roles=[["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
