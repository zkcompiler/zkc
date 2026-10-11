!F = !algebra.field<"bls12-381.fr">
!A = !algebra.field_array<"bls12-381.fr", 2>
module { "protocol.module"() ({
 "data.domain"() ({ ^entry(%lo:ui64,%hi:ui64):
   %d = "data.domain_range"(%lo,%hi) : (ui64,ui64)->!data.domain<ui64>
   "data.domain_yield"(%d) : (!data.domain<ui64>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(ui64,ui64)->!data.domain<ui64>} : ()->()
 func.func private @body(%i:ui64,%lo:ui64,%hi:ui64,%value:!F)->!F {
   func.return %value : !F
 }
 "protocol.func"() ({ ^entry(%value:!F):
   %zero = "data.index"() {value="0"} : ()->ui64
   %two = "data.index"() {value="2"} : ()->ui64
   %r = "algebra.finite_collect"(%zero,%two,%value) {domain=@items,body=@body} : (ui64,ui64,!F)->!A
   "protocol.return"(%r) : (!A)->()
 }) {sym_name="main",function_type=(!F)->!A,roles=["P"],input_roles=[["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
