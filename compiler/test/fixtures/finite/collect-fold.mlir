!F = !algebra.field<"bls12-381.fr">
!V = !data.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
 "data.domain"() ({ ^entry(%xs:!V):
   %d = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
   "data.domain_yield"(%d) : (!data.domain<!F>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
 "data.domain"() ({ ^entry(%xs:!V):
   %d = "data.domain_indices"(%xs) {axis=0:i64} : (!V)->!data.domain<ui64>
   "data.domain_yield"(%d) : (!data.domain<ui64>)->()
 }) {sym_name="positions",sym_visibility="private",function_type=(!V)->!data.domain<ui64>} : ()->()
 func.func private @body(%x:!F,%xs:!V,%factor:!F)->!F {
   %dead = algebra.field_multiply %x,%x : (!F,!F)->!F
   %scaled = algebra.field_multiply %x,%factor : (!F,!F)->!F
   %shifted = algebra.field_add %scaled,%factor : (!F,!F)->!F
   func.return %shifted : !F
 }
 func.func private @step(%a:!F,%b:!F,%x:!F,%ys:!V,%bias:!F)->(!F,!F) {
   %sum = algebra.field_add %a,%x : (!F,!F)->!F
   %next = algebra.field_subtract %sum,%bias : (!F,!F)->!F
   func.return %b,%next : !F,!F
 }
 func.func private @indexed_step(%a:!F,%b:!F,%i:ui64,%ys:!V,%bias:!F,%alias:!V)->(!F,!F)
 attributes {data.preconditions=[#data.index_bound<2,3,0>,#data.index_bound<2,5,0>]} {
   %x = "data.bounded_at"(%ys,%i) : (!V,ui64)->!F
   %again = "data.bounded_at"(%alias,%i) : (!V,ui64)->!F
   %sum = algebra.field_add %a,%x : (!F,!F)->!F
   %shift = algebra.field_subtract %sum,%bias : (!F,!F)->!F
   %next = algebra.field_multiply %shift,%again : (!F,!F)->!F
   func.return %b,%next : !F,!F
 }
 func.func private @elements(%xs:!V,%factor:!F,%bias:!F,%first:!F,%second:!F)->(!F,!F) {
   %ys = "data.finite_collect"(%xs,%factor) {domain=@items,body=@body} : (!V,!F)->!V
   %r:2 = "data.finite_fold"(%ys,%first,%second,%bias) {domain=@items,step=@step} : (!V,!F,!F,!F)->(!F,!F)
   func.return %r#0,%r#1 : !F,!F
 }
 func.func private @indices(%xs:!V,%factor:!F,%bias:!F,%first:!F,%second:!F)->(!F,!F) {
   %ys = "data.finite_collect"(%xs,%factor) {domain=@items,body=@body} : (!V,!F)->!V
   %r:2 = "data.finite_fold"(%ys,%first,%second,%bias,%ys) {domain=@positions,step=@indexed_step} : (!V,!F,!F,!F,!V)->(!F,!F)
   func.return %r#0,%r#1 : !F,!F
 }
 func.func private @nonzero_seeds(%xs:!V,%factor:!F,%bias:!F)->(!F,!F) {
   %first = "algebra.constant"() {value=#algebra.literal<!F, 7 : ui255>} : ()->!F
   %second = "algebra.constant"() {value=#algebra.literal<!F, 11 : ui255>} : ()->!F
   %ys = "data.finite_collect"(%xs,%factor) {domain=@items,body=@body} : (!V,!F)->!V
   %r:2 = "data.finite_fold"(%ys,%first,%second,%bias) {domain=@items,step=@step} : (!V,!F,!F,!F)->(!F,!F)
   func.return %r#0,%r#1 : !F,!F
 }
 func.func private @unit_step(%x:!F,%ys:!V,%bias:!F) {
   %dead = algebra.field_subtract %x,%bias : (!F,!F)->!F
   func.return
 }
 func.func private @unit_state(%xs:!V,%factor:!F,%bias:!F) {
   %ys = "data.finite_collect"(%xs,%factor) {domain=@items,body=@body} : (!V,!F)->!V
   "data.finite_fold"(%ys,%bias) {domain=@items,step=@unit_step} : (!V,!F)->()
   func.return
 }
 func.func private @mixed_step(%ok:i1,%state:!F,%x:!F,%ys:!V,%bias:!F)->(i1,!F) {
   %yes = arith.constant true
   %next = arith.xori %ok,%yes : i1
   %difference = algebra.field_subtract %x,%bias : (!F,!F)->!F
   %sum = algebra.field_add %state,%difference : (!F,!F)->!F
   func.return %next,%sum : i1,!F
 }
 func.func private @mixed_states(%xs:!V,%factor:!F,%bias:!F,%ok:i1,%seed:!F)->(i1,!F) {
   %ys = "data.finite_collect"(%xs,%factor) {domain=@items,body=@body} : (!V,!F)->!V
   %r:2 = "data.finite_fold"(%ys,%ok,%seed,%bias) {domain=@items,step=@mixed_step} : (!V,i1,!F,!F)->(i1,!F)
   func.return %r#0,%r#1 : i1,!F
 }
 "data.domain"() ({ ^entry(%xs:!V,%other:!V):
   %x = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
   %y = "data.domain_elements"(%other) : (!V)->!data.domain<!F>
   %zip = "data.domain_zip"(%x,%y) : (!data.domain<!F>,!data.domain<!F>)->!data.domain<!F,!F>
   "data.domain_yield"(%zip) : (!data.domain<!F,!F>)->()
 }) {sym_name="paired",sym_visibility="private",function_type=(!V,!V)->!data.domain<!F,!F>} : ()->()
 func.func private @nested_step(%state:!F,%x:!F,%y:!F,%xs:!V,%other:!V)->!F {
   %next = algebra.field_add %state,%x : (!F,!F)->!F
   func.return %next : !F
 }
 func.func private @checked_body(%x:!F,%xs:!V,%factor:!F,%other:!V)->!F {
   // Identical factors discharge total zip's equal-extent obligation while
   // retaining the nested admission check, even though its result is unused.
   %dead = "data.finite_fold"(%xs,%xs,%x) {domain=@paired,step=@nested_step} : (!V,!V,!F)->!F
   %r = algebra.field_multiply %x,%factor : (!F,!F)->!F
   func.return %r : !F
 }
 func.func private @nested_checks(%xs:!V,%other:!V,%factor:!F,%bias:!F,%a:!F,%b:!F)->(!F,!F) {
   %ys = "data.finite_collect"(%xs,%factor,%other) {domain=@items,body=@checked_body} : (!V,!F,!V)->!V
   %r:2 = "data.finite_fold"(%ys,%a,%b,%bias) {domain=@items,step=@step} : (!V,!F,!F,!F)->(!F,!F)
   func.return %r#0,%r#1 : !F,!F
 }
 "protocol.func"() ({ "protocol.return"() : ()->() })
 {sym_name="main",function_type=()->(),roles=["P"],input_roles=[],output_roles=[]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
