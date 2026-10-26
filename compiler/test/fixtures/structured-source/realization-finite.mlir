!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
 "data.domain"() ({
 ^entry(%xs:!V):
   %d = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
   "data.domain_yield"(%d) : (!data.domain<!F>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
 func.func private @step(%acc:!F,%x:!F,%xs:!V)->!F {
   %s = "algebra.field_add"(%acc,%x) : (!F,!F)->!F
   func.return %s : !F
 }
 func.func private @sum(%xs:!V)->!F {
   %zero = "algebra.constant"() {value="0"} : ()->!F
   %sum = "algebra.finite_fold"(%xs,%zero) {domain=@items,step=@step} : (!V,!F)->!F
   func.return %sum : !F
 }
 func.func @realized(%scope:!runtime.scope,%a0:!V)->!exec.outcome<(!F)> attributes {no_inline,runtime.origin=["realized",[]]} {
   %call = "exec.compute"(%scope,%a0) {callee=@sum,site="kernel"} : (!runtime.scope,!V)->!exec.outcome<(!F)>
   "exec.dispatch"(%call)[^done,^failed] : (!exec.outcome<(!F)>)->()
 ^done(%r0:!F):
   %result = "exec.returned"(%r0) : (!F)->!exec.outcome<(!F)>
   func.return %result : !exec.outcome<(!F)>
 ^failed(%stop:!exec.stop):
   %failure = "exec.failed"(%stop) : (!exec.stop)->!exec.outcome<(!F)>
   func.return %failure : !exec.outcome<(!F)>
 }
 "protocol.func"() ({ "protocol.return"() : ()->() })
 {sym_name="main",origin=["main",[]],function_type=()->(),roles=["P"],input_roles=[],output_roles=[]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
