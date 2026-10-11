!F = !algebra.field<"bls12-381.fr">
!V = tensor<?x!F>
module { "protocol.module"() ({
 "data.domain"() ({ ^entry(%xs:!V,%ys:!V,%zs:!V):
   %d = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
   "data.domain_yield"(%d) : (!data.domain<!F>)->()
 }) {sym_name="outer",sym_visibility="private",function_type=(!V,!V,!V)->!data.domain<!F>} : ()->()
 "data.domain"() ({ ^entry(%ys:!V,%zs:!V):
   %y = "data.domain_elements"(%ys) : (!V)->!data.domain<!F>
   %z = "data.domain_elements"(%zs) : (!V)->!data.domain<!F>
   %d = "data.domain_zip"(%y,%z) : (!data.domain<!F>,!data.domain<!F>)->!data.domain<!F,!F>
   "data.domain_yield"(%d) : (!data.domain<!F,!F>)->()
 }) {sym_name="inner",sym_visibility="private",function_type=(!V,!V)->!data.domain<!F,!F>} : ()->()
 local.func private @inside(%s:!F,%y:!F,%z:!F,%ys:!V,%zs:!V) -> !F attributes {logical_origin=["inside",[]]} {
   local.return %s : !F
 }
 "local.finite_fold"() {sym_name="inner_fold",function_type=(!V,!V,!F)->!F,domain=@inner,step=@inside} : ()->()
 local.func private @outside(%s:!F,%x:!F,%xs:!V,%ys:!V,%zs:!V) -> !F attributes {logical_origin=["outside",[]]} {
   %r = local.apply @inner_fold(%ys,%zs,%s) {site="inner"} : (!V,!V,!F)->!F
   local.return %r : !F
 }
 "local.finite_fold"() {sym_name="fold",function_type=(!V,!V,!V,!F)->!F,domain=@outer,step=@outside} : ()->()
 local.func @work(%xs:!V,%ys:!V,%zs:!V,%init:!F) -> !F attributes {logical_origin=["work",[]]} {
   %r = local.apply @fold(%xs,%ys,%zs,%init) {site="fold"} : (!V,!V,!V,!F)->!F
   local.return %r : !F
 }
 "protocol.func"() ({ ^entry(%xs:!V,%ys:!V,%zs:!V,%init:!F):
   %r = "protocol.local_call"(%xs,%ys,%zs,%init) {callee=@work,role="P",site="work"} : (!V,!V,!V,!F)->!F
   "protocol.return"(%r) : (!F)->()
 }) {sym_name="main",function_type=(!V,!V,!V,!F)->!F,roles=["P"],input_roles=[["P"],["P"],["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
