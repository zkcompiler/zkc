!F = !algebra.field<"bls12-381.fr">
!V = !data.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
 func.func private @square(%x:!F)->!F {
   %r = "algebra.field_multiply"(%x,%x) : (!F,!F)->!F
   func.return %r : !F
 }
 func.func private @formula(%a:!F,%b:!F,%unused:!F,%s:!F)->!F {
   %one = "algebra.constant"() {value=#algebra.literal<!F, 1 : ui255>} : ()->!F
   %sq = func.call @square(%a) : (!F)->!F
   %d = "algebra.field_subtract"(%sq,%b) : (!F,!F)->!F
   %t = "algebra.field_add"(%s,%one) : (!F,!F)->!F
   %m = "algebra.field_multiply"(%t,%d) : (!F,!F)->!F
   %p = "algebra.field_add"(%m,%s) : (!F,!F)->!F
   %dead = "algebra.field_add"(%unused,%unused) : (!F,!F)->!F
   func.return %p : !F
 }
 "data.domain"() ({
 ^entry(%a:!V,%b:!V,%c:!V):
   %as = "data.domain_elements"(%a) : (!V)->!data.domain<!F>
   %bs = "data.domain_elements"(%b) : (!V)->!data.domain<!F>
   %cs = "data.domain_elements"(%c) : (!V)->!data.domain<!F>
   %rows = "data.domain_zip"(%as,%bs,%cs) : (!data.domain<!F>,!data.domain<!F>,!data.domain<!F>)->!data.domain<!F,!F,!F>
   "data.domain_yield"(%rows) : (!data.domain<!F,!F,!F>)->()
 }) {sym_name="rows",sym_visibility="private",function_type=(!V,!V,!V)->!data.domain<!F,!F,!F>} : ()->()
func.func private @row(%scope:!runtime.scope,%a0:!F,%a1:!F,%a2:!F,%a3:!V,%a4:!V,%a5:!V,%a6:!F)->!exec.outcome<(!F)> attributes {no_inline,runtime.origin=["row",[]]} {
%value_attempt = "exec.compute"(%scope,%a0,%a1,%a2,%a6) {callee=@formula,site="calculate"} : (!runtime.scope,!F,!F,!F,!F)->!exec.outcome<(!F)>
"exec.dispatch"(%value_attempt)[^value,^failed] : (!exec.outcome<(!F)>)->()
^value(%r:!F):
%done = "exec.returned"(%r) : (!F)->!exec.outcome<(!F)>
func.return %done : !exec.outcome<(!F)>
^failed(%reason:!exec.stop):
%failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(!F)>
func.return %failure : !exec.outcome<(!F)>
}
func.func @work(%scope:!runtime.scope,%a0:!V,%a1:!V,%a2:!V,%a3:!F)->!exec.outcome<(!V)> attributes {no_inline,runtime.origin=["work",[]]} {
%value_attempt = "exec.collect"(%scope,%a0,%a1,%a2,%a3) {domain=@rows,body=@row,site="map"} : (!runtime.scope,!V,!V,!V,!F)->!exec.outcome<(!V)>
"exec.dispatch"(%value_attempt)[^value,^failed] : (!exec.outcome<(!V)>)->()
^value(%r:!V):
%done = "exec.returned"(%r) : (!V)->!exec.outcome<(!V)>
func.return %done : !exec.outcome<(!V)>
^failed(%reason:!exec.stop):
%failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(!V)>
func.return %failure : !exec.outcome<(!V)>
}
 "protocol.func"() ({
 ^entry(%a:!V,%b:!V,%c:!V,%s:!F):
   %r = "protocol.local_call"(%a,%b,%c,%s) {callee=@work,role="P",site="work"} : (!V,!V,!V,!F)->!V
   "protocol.return"(%r) : (!V)->()
 }) {sym_name="main",origin=["main",[]],function_type=(!V,!V,!V,!F)->!V,roles=["P"],input_roles=[["P"],["P"],["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
