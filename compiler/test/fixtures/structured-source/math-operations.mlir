!F = !algebra.field<"bls12-381.fr">
module { "protocol.module"() ({
 func.func private @arithmetic(%a:!F,%b:!F,%flag:i1) -> (!F,i1) {
   %one = "algebra.constant"() {value="1"} : ()->!F
   %sum = algebra.field_add %b,%a : (!F,!F)->!F
   %difference = algebra.field_subtract %a,%b : (!F,!F)->!F
   %product = algebra.field_multiply %sum,%difference : (!F,!F)->!F
   %same = algebra.field_equal %a,%one : (!F,!F)->i1
   %yes = arith.constant true
   %both = arith.andi %same,%flag : i1
   %either = arith.ori %both,%yes : i1
   %xor = arith.xori %either,%flag : i1
   %equal = arith.cmpi eq,%xor,%flag : i1
   %unequal = arith.cmpi ne,%equal,%same : i1
   %selected = arith.select %unequal,%product,%one : !F
   func.return %selected,%unequal : !F,i1
 }
 "protocol.func"() ({
 ^entry(%a:!F,%b:!F,%flag:i1):
   %first:2 = func.call @arithmetic(%a,%b,%flag) : (!F,!F,i1)->(!F,i1)
   %second:2 = func.call @arithmetic(%b,%a,%flag) : (!F,!F,i1)->(!F,i1)
   "protocol.return"(%first#0,%second#0,%first#1,%second#1) : (!F,!F,i1,i1)->()
 }) {sym_name="main",origin=["main",[]],function_type=(!F,!F,i1)->(!F,!F,i1,i1),roles=["P"],input_roles=[["P"],["P"],["P"]],output_roles=[["P"],["P"],["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
