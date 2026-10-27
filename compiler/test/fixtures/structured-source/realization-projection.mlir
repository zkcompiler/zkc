!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
 func.func private @value(%xs:!V,%dimension:ui64,%width:ui64)->!V {
   func.return %xs : !V
 }
func.func @work(%scope:!runtime.scope,%a0:!V,%a1:ui64,%a2:ui64)->!exec.outcome<(!V)> attributes {no_inline,runtime.origin=["work",[]]} {
%value_attempt = "exec.compute"(%scope,%a0,%a1,%a2) {callee=@value,site="realize"} : (!runtime.scope,!V,ui64,ui64)->!exec.outcome<(!V)>
"exec.dispatch"(%value_attempt)[^value,^failed] : (!exec.outcome<(!V)>)->()
^value(%r:!V):
%done = "exec.returned"(%r) : (!V)->!exec.outcome<(!V)>
func.return %done : !exec.outcome<(!V)>
^failed(%reason:!exec.stop):
%failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(!V)>
func.return %failure : !exec.outcome<(!V)>
}
 "protocol.func"() ({
 ^entry(%xs:!V,%dimension:ui64,%width:ui64):
   %r = "protocol.local_call"(%xs,%dimension,%width) {callee=@work,role="P",site="work"} : (!V,ui64,ui64)->!V
   "protocol.return"(%r) : (!V)->()
 }) {sym_name="main",origin=["main",[]],function_type=(!V,ui64,ui64)->!V,roles=["P"],input_roles=[["P"],["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
