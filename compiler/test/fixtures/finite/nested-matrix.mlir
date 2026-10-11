!F = !algebra.field<"bls12-381.fr">
!V = tensor<?x!F>
!M = tensor<?x?x!F>
module { "protocol.module"() ({
 "local.binding"() {sym_name="add",contract="field.add",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="mul",contract="field.mul",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="constant",contract="field.constant",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "data.domain"() ({
 ^entry(%m:!M,%r:ui64,%xs:!V,%ignored:!V):
   %a = "data.domain_matrix_row"(%m,%r) : (!M,ui64)->!data.domain<!F>
   %b = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
   %c = "data.domain_elements"(%ignored) : (!V)->!data.domain<!F>
   %d = "data.domain_zip"(%a,%b,%c) : (!data.domain<!F>,!data.domain<!F>,!data.domain<!F>)->!data.domain<!F,!F,!F>
   "data.domain_yield"(%d) : (!data.domain<!F,!F,!F>)->()
 }) {sym_name="inner_domain",sym_visibility="private",function_type=(!M,ui64,!V,!V)->!data.domain<!F,!F,!F>} : ()->()
 local.func private @step(%s:!F,%a:!F,%b:!F,%ignored:!F,%m:!M,%r:ui64,%xs:!V,%zs:!V) -> !F attributes {logical_origin=["step",[]]} {
   %p = "algebra.exec.field_multiply"(%a,%b) {binding=@mul,parameters=[],site="product"} : (!F,!F)->!F
   %out = "algebra.exec.field_add"(%s,%p) {binding=@add,parameters=[],site="sum"} : (!F,!F)->!F
   local.return %out : !F
 }
 "local.finite_fold"() {sym_name="inner",function_type=(!M,ui64,!V,!V,!F)->!F,domain=@inner_domain,step=@step} : ()->()
 "data.domain"() ({
 ^entry(%m:!M,%xs:!V,%ignored:!V,%otherm:!M,%otherv:!V,%seed:!F,%otherseed:!F):
   %rows = "data.domain_indices"(%m) {axis=0:i64} : (!M)->!data.domain<ui64>
   "data.domain_yield"(%rows) : (!data.domain<ui64>)->()
 }) {sym_name="outer_domain",sym_visibility="private",function_type=(!M,!V,!V,!M,!V,!F,!F)->!data.domain<ui64>} : ()->()
 local.func private @body(%r:ui64,%m:!M,%xs:!V,%ignored:!V,%otherm:!M,%otherv:!V,%seed:!F,%otherseed:!F) -> !F attributes {logical_origin=["body",[]]} {
   %out = local.apply @inner(%m,%r,%xs,%ignored,%seed) {site="inner"} : (!M,ui64,!V,!V,!F)->!F
   local.return %out : !F
 }
 "local.finite_collect"() {sym_name="all_rows",function_type=(!M,!V,!V,!M,!V,!F,!F)->!V,domain=@outer_domain,body=@body} : ()->()
 local.func @work(%m:!M,%xs:!V,%ignored:!V,%otherm:!M,%otherv:!V,%seed:!F,%otherseed:!F) -> !V attributes {logical_origin=["work",[]]} {
   %out = local.apply @all_rows(%m,%xs,%ignored,%otherm,%otherv,%seed,%otherseed) {site="collect"} : (!M,!V,!V,!M,!V,!F,!F)->!V
   local.return %out : !V
 }
 "protocol.func"() ({
 ^entry(%m:!M,%xs:!V,%ignored:!V,%otherm:!M,%otherv:!V,%seed:!F,%otherseed:!F):
   %out = "protocol.local_call"(%m,%xs,%ignored,%otherm,%otherv,%seed,%otherseed) {callee=@work,role="P",site="work"} : (!M,!V,!V,!M,!V,!F,!F)->!V
   "protocol.return"(%out) : (!V)->()
 }) {sym_name="main",function_type=(!M,!V,!V,!M,!V,!F,!F)->!V,roles=["P"],input_roles=[["P"],["P"],["P"],["P"],["P"],["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
