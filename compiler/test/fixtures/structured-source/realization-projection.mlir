!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
 func.func private @value(%xs:!V,%dimension:ui64,%width:ui64)->!V {
   func.return %xs : !V
 }
 local.realize @realized = @value : (!V,ui64,ui64)->!V
 local.func @work(%xs:!V,%dimension:ui64,%width:ui64)->!V attributes {logical_origin=["work",[]]} {
   %r = local.apply @realized(%xs,%dimension,%width) {site="realize"} : (!V,ui64,ui64)->!V
   local.return %r : !V
 }
 "protocol.func"() ({
 ^entry(%xs:!V,%dimension:ui64,%width:ui64):
   %r = "protocol.local_call"(%xs,%dimension,%width) {callee=@work,role="P",site="work"} : (!V,ui64,ui64)->!V
   "protocol.return"(%r) : (!V)->()
 }) {sym_name="main",function_type=(!V,ui64,ui64)->!V,roles=["P"],input_roles=[["P"],["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
