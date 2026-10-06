!f = !algebra.field<"bls12-381.fr">
!t = !poly.multilinear<"bls12-381.fr">
!p = !poly.point<"bls12-381.fr">
module { "protocol.module"() ({
 "poly.recipe"() ({ ^slots(%a:!f,%b:!f):
   %product = algebra.field_multiply %a,%b : (!f,!f)->!f
   "poly.recipe_yield"(%product) : (!f)->()
 }) {sym_name="product",degree=2:i64} : ()->()
 "poly.realize"() {sym_name="evaluate",recipe=@product,kind="evaluate",function_type=(!p,!t,!t)->!f} : ()->()
 "protocol.func"() ({ ^entry(%point:!p,%T:!t,%U:!t):
   %actual = "protocol.local_call"(%point,%T,%U) {callee=@evaluate,role="P",site="evaluate"} : (!p,!t,!t)->!f
   "protocol.return"(%actual) : (!f)->()
 }) {sym_name="main",function_type=(!p,!t,!t)->!f,roles=["P"],input_roles=[["P"],["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
