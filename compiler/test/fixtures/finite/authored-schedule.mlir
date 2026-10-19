!F = !algebra.field<"bls12-381.fr">
// Authored independently of scheduleEntry and finite recipe production.
// This schedule must parse with ordinary MLIR verification enabled, including
// the isolated Local bound-admission frames inside the standard function.
module {
 "local.binding"() {sym_name="add",contract="field.add",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="subtract",contract="field.sub",arguments=["bls12-381.fr"],implementation=""} : ()->()
 func.func @evaluate(%lower:ui64,%upper:ui64,%first:!F,%second:!F,%factor:!F,%bias:!F)->(!F,!F)
 attributes {logical_origin=["evaluate",[]]} {
   "local.for"(%lower,%lower) ({ ^lower_check(%i:ui64):
     "local.yield"() : ()->()
   }) {site="traverse_schedule_lower"} : (ui64,ui64)->()
   "local.for"(%upper,%upper) ({ ^upper_check(%i:ui64):
     "local.yield"() : ()->()
   }) {site="traverse_schedule_upper"} : (ui64,ui64)->()
   %lo = builtin.unrealized_conversion_cast %lower : ui64 to i64
   %hi = builtin.unrealized_conversion_cast %upper : ui64 to i64
   %one = arith.constant 1 : i64
   %r:4 = "scf.for"(%lo,%hi,%one,%first,%second,%factor,%bias) ({
   ^body(%position:i64,%a:!F,%b:!F,%scale:!F,%shift:!F):
     %i = builtin.unrealized_conversion_cast %position : i64 to ui64
     %sum = "algebra.exec.field_add"(%a,%scale) {binding=@add,parameters=[],site="sum"} : (!F,!F)->!F
     %next = "algebra.exec.field_subtract"(%sum,%shift) {binding=@subtract,parameters=[],site="next"} : (!F,!F)->!F
     "scf.yield"(%b,%next,%scale,%shift) : (!F,!F,!F,!F)->()
   }) {unsignedCmp,site="traverse",state_count=2:i64} : (i64,i64,i64,!F,!F,!F,!F)->(!F,!F,!F,!F)
   func.return %r#0,%r#1 : !F,!F
 }
}
