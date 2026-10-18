!F = !algebra.field<"bls12-381.fr">
// Independently authored expected executable for authored-schedule.mlir.
module { "protocol.module"() ({
 "local.binding"() {sym_name="add",contract="field.add",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="subtract",contract="field.sub",arguments=["bls12-381.fr"],implementation=""} : ()->()
 local.func @evaluate(%lower:ui64,%upper:ui64,%first:!F,%second:!F,%factor:!F,%bias:!F)->(!F,!F)
 attributes {logical_origin=["evaluate",[]]} {
   %r:2 = "local.for"(%lower,%upper,%first,%second,%factor,%bias) ({
   ^body(%position:ui64,%a:!F,%b:!F,%scale:!F,%shift:!F):
     %sum = "algebra.exec.field_add"(%a,%scale) {binding=@add,parameters=[],site="sum"} : (!F,!F)->!F
     %next = "algebra.exec.field_subtract"(%sum,%shift) {binding=@subtract,parameters=[],site="next"} : (!F,!F)->!F
     "local.yield"(%b,%next,%scale,%shift) : (!F,!F,!F,!F)->()
   }) {site="traverse"} : (ui64,ui64,!F,!F,!F,!F)->(!F,!F)
   local.return %r#0,%r#1 : !F,!F
 }
}) {profile=#protocol.profile<exec>} : ()->() }
