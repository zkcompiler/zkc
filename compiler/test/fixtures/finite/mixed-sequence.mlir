!F = !algebra.field<"bls12-381.fr">
!S = !data.sequence<i1>
module { "protocol.module"() ({
 "local.binding"() {sym_name="add",contract="field.add",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "data.domain"() ({ ^entry(%xs:!S):
   %d = "data.domain_elements"(%xs) : (!S)->!data.domain<i1>
   "data.domain_yield"(%d) : (!data.domain<i1>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!S)->!data.domain<i1>} : ()->()
 local.func private @step(%s:!F,%take:i1,%xs:!S,%weight:!F) -> !F attributes {logical_origin=["step",[]]} {
   %r = "local.if"(%take,%s,%weight) ({ ^yes(%a:!F,%w:!F):
     %v = "algebra.exec.field_add"(%a,%w) {binding=@add,parameters=[],site="add"} : (!F,!F)->!F
     "local.yield"(%v) : (!F)->()
   }, { ^no(%a:!F,%w:!F):
     "local.yield"(%a) : (!F)->()
   }) {site="take"} : (i1,!F,!F)->!F
   local.return %r : !F
 }
 "local.finite_fold"() {sym_name="fold",function_type=(!S,!F,!F)->!F,domain=@items,step=@step} : ()->()
 local.func @work(%xs:!S,%init:!F,%weight:!F) -> !F attributes {logical_origin=["work",[]]} {
   %r = local.apply @fold(%xs,%init,%weight) {site="fold"} : (!S,!F,!F)->!F
   local.return %r : !F
 }
 "protocol.func"() ({ ^entry(%a:i1,%b:i1,%init:!F,%weight:!F):
   %empty = "data.sequence_empty"() : ()->!S
   %one = "data.sequence_append"(%empty,%a) : (!S,i1)->!S
   %xs = "data.sequence_append"(%one,%b) : (!S,i1)->!S
   %r = "protocol.local_call"(%xs,%init,%weight) {callee=@work,role="P",site="work"} : (!S,!F,!F)->!F
   "protocol.return"(%r) : (!F)->()
 }) {sym_name="main",function_type=(i1,i1,!F,!F)->!F,roles=["P"],input_roles=[["P"],["P"],["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
