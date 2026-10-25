!F = !algebra.field<"bls12-381.fr">
module { "protocol.module"() ({
 local.func private @swap(%a:!F,%b:!F) -> (!F,!F) attributes {logical_origin=["original_swap",[["Field","bls12-381.fr"],["Group","bls12-381.g1"]]]} {
   local.return %b,%a : !F,!F
 }
 local.func @control(%a:!F,%b:!F,%c:!F,%d:!F,%lo:ui64,%hi:ui64,%go:i1) -> (!F,!F) attributes {logical_origin=["control",[]]} {
   %r:2 = "local.for"(%lo,%hi,%a,%b,%c,%d,%go) ({
   ^body(%i:ui64,%x:!F,%y:!F,%left:!F,%right:!F,%flag:i1):
     %next:2 = "local.if"(%flag,%x,%y,%left,%right) ({
     ^yes(%aa:!F,%bb:!F,%cc:!F,%dd:!F):
       "local.yield"(%cc,%bb) : (!F,!F)->()
     }, {
     ^no(%aa:!F,%bb:!F,%cc:!F,%dd:!F):
       "local.yield"(%aa,%dd) : (!F,!F)->()
     }) {site="choose"} : (i1,!F,!F,!F,!F)->(!F,!F)
     "local.yield"(%next#1,%next#0,%left,%right,%flag) : (!F,!F,!F,!F,i1)->()
   }) {site="loop"} : (ui64,ui64,!F,!F,!F,!F,i1)->(!F,!F)
   "local.for"(%lo,%hi,%go) ({
   ^body(%i:ui64,%flag:i1):
     "local.if"(%flag) ({ "local.yield"() : ()->() }, { "local.stop"() {reason="reject",site="check_failed"} : ()->() }) {site="check"} : (i1)->()
     "local.yield"(%flag) : (i1)->()
   }) {site="empty_loop"} : (ui64,ui64,i1)->()
   %s:2 = "local.for"(%lo,%hi,%r#0,%r#1,%c,%d,%go) ({
   ^body(%i:ui64,%x:!F,%y:!F,%left:!F,%right:!F,%flag:i1):
     "local.condition"(%flag,%y,%x,%left,%right,%flag) : (i1,!F,!F,!F,!F,i1)->()
   }) {site="conditional_loop"} : (ui64,ui64,!F,!F,!F,!F,i1)->(!F,!F)
   %first:2 = local.apply @swap(%s#0,%s#1) {site="first"} : (!F,!F)->(!F,!F)
   %second:2 = local.apply @swap(%c,%d) {site="second"} : (!F,!F)->(!F,!F)
   local.return %first#0,%second#1 : !F,!F
 }
 "protocol.func"() ({
 ^entry(%a:!F,%b:!F,%c:!F,%d:!F,%lo:ui64,%hi:ui64,%go:i1):
   %r:2 = "protocol.local_call"(%a,%b,%c,%d,%lo,%hi,%go) {callee=@control,role="Owner",site="invoke"} : (!F,!F,!F,!F,ui64,ui64,i1)->(!F,!F)
   "protocol.return"(%r#0,%r#1) : (!F,!F)->()
 }) {sym_name="entry",origin=["entry",[]],function_type=(!F,!F,!F,!F,ui64,ui64,i1)->(!F,!F),roles=["Owner"],input_roles=[["Owner"],["Owner"],["Owner"],["Owner"],["Owner"],["Owner"],["Owner"]],output_roles=[["Owner"],["Owner"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
