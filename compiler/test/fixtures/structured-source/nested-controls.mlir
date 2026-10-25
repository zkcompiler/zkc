!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
 "data.domain"() ({ ^entry(%xs:!V):
   %d = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
   "data.domain_yield"(%d) : (!data.domain<!F>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
 local.func private @step(%a:!F,%b:!F,%item:!F,%xs:!V,%enabled:i1) -> (!F,!F) attributes {logical_origin=["step",[]]} {
   %r:2 = "local.if"(%enabled,%a,%b,%item,%enabled) ({
   ^then(%aa:!F,%bb:!F,%xx:!F,%yes:i1):
     %s:2 = "local.if"(%yes,%aa,%bb,%xx) ({
     ^yes(%aaa:!F,%bbb:!F,%xxx:!F):
       "local.yield"(%bbb,%xxx) : (!F,!F)->()
     }, {
     ^no(%aaa:!F,%bbb:!F,%xxx:!F):
       "local.yield"(%aaa,%bbb) : (!F,!F)->()
     }) {site="inner"} : (i1,!F,!F,!F)->(!F,!F)
     "local.yield"(%s#0,%s#1) : (!F,!F)->()
   }, {
   ^else(%aa:!F,%bb:!F,%xx:!F,%yes:i1):
     "local.yield"(%aa,%bb) : (!F,!F)->()
   }) {site="outer"} : (i1,!F,!F,!F,i1)->(!F,!F)
   local.return %r#0,%r#1 : !F,!F
 }
 "local.finite_fold"() {sym_name="fold",function_type=(!V,!F,!F,i1)->(!F,!F),domain=@items,step=@step} : ()->()
 local.func @work(%xs:!V,%a:!F,%b:!F,%enabled:i1) -> (!F,!F) attributes {logical_origin=["work",[]]} {
   %r:2 = local.apply @fold(%xs,%a,%b,%enabled) {site="fold"} : (!V,!F,!F,i1)->(!F,!F)
   "local.if"(%enabled) ({ "local.yield"() : ()->() }, { "local.stop"() {site="disabled",reason="abort"} : ()->() }) {site="empty"} : (i1)->()
   local.return %r#0,%r#1 : !F,!F
 }
 "protocol.func"() ({ ^entry(%xs:!V,%a:!F,%b:!F,%enabled:i1):
   %r:2 = "protocol.local_call"(%xs,%a,%b,%enabled) {callee=@work,role="P",site="work"} : (!V,!F,!F,i1)->(!F,!F)
   "protocol.return"(%r#0,%r#1) : (!F,!F)->()
 }) {sym_name="main",origin=["main",[]],function_type=(!V,!F,!F,i1)->(!F,!F),roles=["P"],input_roles=[["P"],["P"],["P"],["P"]],output_roles=[["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
