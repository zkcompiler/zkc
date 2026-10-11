!F = !algebra.field<"bls12-381.fr">
!V = tensor<?x!F>
!R = !local.capability<"rng:bls12-381.fr">
module { "protocol.module"() ({
 "data.domain"() ({
 ^entry(%xs:!V):
   %d = "data.domain_elements"(%xs) : (!V) -> !data.domain<!F>
   "data.domain_yield"(%d) : (!data.domain<!F>) -> ()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
 local.func private @step(%a:!R,%b:!R,%item:!F,%xs:!V) -> (!R,!R) attributes {logical_origin=["step",[]]} {
   local.return %a,%b : !R,!R
 }
 "local.finite_fold"() {sym_name="fold",function_type=(!V,!R,!R)->(!R,!R),domain=@items,step=@step} : ()->()
 local.func @work(%xs:!V,%a:!R,%b:!R) -> (!R,!R) attributes {logical_origin=["work",[]]} {
   %r:2 = local.apply @fold(%xs,%a,%b) {site="fold"} : (!V,!R,!R)->(!R,!R)
   local.return %r#0,%r#1 : !R,!R
 }
 "protocol.func"() ({
 ^entry(%xs:!V,%a:!R,%b:!R):
   %r:2 = "protocol.local_call"(%xs,%a,%b) {callee=@work,role="P",site="work"} : (!V,!R,!R)->(!R,!R)
   "protocol.return"(%r#0,%r#1) : (!R,!R)->()
 }) {sym_name="main",function_type=(!V,!R,!R)->(!R,!R),roles=["P"],input_roles=[["P"],["P"],["P"]],output_roles=[["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
