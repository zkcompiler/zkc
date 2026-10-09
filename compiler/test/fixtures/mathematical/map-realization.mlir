!F = !algebra.field<"koala-bear">
!V = tensor<?x!F>
module { "protocol.module"() ({
 func.func private @square(%x:!F)->!F {
   %r = "algebra.field_multiply"(%x,%x) : (!F,!F)->!F
   func.return %r : !F
 }
 func.func private @formula(%a:!F,%b:!F,%unused:!F,%s:!F)->!F {
   %one = "algebra.constant"() {value="1"} : ()->!F
   %sq = func.call @square(%a) : (!F)->!F
   %d = "algebra.field_subtract"(%sq,%b) : (!F,!F)->!F
   %t = "algebra.field_add"(%s,%one) : (!F,!F)->!F
   %m = "algebra.field_multiply"(%t,%d) : (!F,!F)->!F
   %p = "algebra.field_add"(%m,%s) : (!F,!F)->!F
   %dead = "algebra.field_add"(%unused,%unused) : (!F,!F)->!F
   func.return %p : !F
 }
 algebra.map_realize @mapped = @formula [true, true, true, false] : (!V,!V,!V,!F)->!V
 local.func @work(%a:!V,%b:!V,%c:!V,%s:!F)->!V attributes {logical_origin=["work",[]]} {
   %r = local.apply @mapped(%a,%b,%c,%s) {site="map"} : (!V,!V,!V,!F)->!V
   local.return %r : !V
 }
 "protocol.func"() ({
 ^entry(%a:!V,%b:!V,%c:!V,%s:!F):
   %r = "protocol.local_call"(%a,%b,%c,%s) {callee=@work,role="P",site="work"} : (!V,!V,!V,!F)->!V
   "protocol.return"(%r) : (!V)->()
 }) {sym_name="main",function_type=(!V,!V,!V,!F)->!V,roles=["P"],input_roles=[["P"],["P"],["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
