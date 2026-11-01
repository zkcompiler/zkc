!F = !algebra.field<"bls12-381.fr">
!V = !data.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
 "data.domain"() ({
 ^entry(%xs:!V):
   %d = "data.domain_elements"(%xs) : (!V) -> !data.domain<!F>
   "data.domain_yield"(%d) : (!data.domain<!F>) -> ()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
 func.func private @step(%scope:!runtime.scope,%item:!F,%xs:!V,%enabled:i1) -> !exec.outcome<> attributes {no_inline,runtime.origin=["step",[]]} {
   %stop = "exec.reject"(%scope) {site="body_stop",reason="abort"} : (!runtime.scope)->!exec.stop
   cf.br ^failed(%stop : !exec.stop)
 ^failed(%cause:!exec.stop):
   %failed = "exec.failed"(%cause) : (!exec.stop)->!exec.outcome<>
   func.return %failed : !exec.outcome<>
 }
 func.func private @predicate(%scope:!runtime.scope,%item:!F,%xs:!V,%enabled:i1) -> !exec.outcome<(i1)> attributes {no_inline,runtime.origin=["predicate",[]]} {
   %result = "exec.returned"(%enabled) : (i1)->!exec.outcome<(i1)>
   func.return %result : !exec.outcome<(i1)>
 }
 func.func @work(%scope:!runtime.scope,%xs:!V,%enabled:i1) -> !exec.outcome<(i1)> attributes {no_inline,runtime.origin=["work",[]]} {
   %fold = "exec.fold"(%scope,%xs,%enabled) {domain=@items,step=@step,predicate=@predicate,site="fold"} : (!runtime.scope,!V,i1)->!exec.outcome<>
   "exec.dispatch"(%fold)[^done,^failed] : (!exec.outcome<>)->()
 ^done:
   %result = "exec.returned"(%enabled) : (i1)->!exec.outcome<(i1)>
   func.return %result : !exec.outcome<(i1)>
 ^failed(%cause:!exec.stop):
   %failure = "exec.failed"(%cause) : (!exec.stop)->!exec.outcome<(i1)>
   func.return %failure : !exec.outcome<(i1)>
 }
 "protocol.func"() ({
 ^entry(%xs:!V,%enabled:i1):
   %r = "protocol.local_call"(%xs,%enabled) {callee=@work,role="P",site="work"} : (!V,i1)->i1
   "protocol.return"(%r) : (i1)->()
 }) {sym_name="main",origin=["main",[]],function_type=(!V,i1)->i1,roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
