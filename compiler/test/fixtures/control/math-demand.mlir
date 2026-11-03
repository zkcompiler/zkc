!F = !algebra.field<"bls12-381.fr">
module { "protocol.module"() ({
 func.func private @sum(%x:!F,%y:!F)->!F {
   %result = algebra.field_add %x,%y : (!F,!F)->!F
   return %result : !F
 }
 func.func private @choose(%choice:i1,%x:!F,%y:!F)->!F {
   %result = "data.branch"(%choice,%x,%y) ({
   ^then(%left:!F,%right:!F):
     %sum = func.call @sum(%left,%right) : (!F,!F)->!F
     "data.yield"(%sum) : (!F)->()
   }, {
   ^else(%left:!F,%right:!F):
     "data.yield"(%right) : (!F)->()
   }) {alternatives=["then","else"]} : (i1,!F,!F)->!F
   return %result : !F
 }
 "protocol.func"() ({ ^entry(%choice:i1,%x:!F,%y:!F,%expected:!F):
   %value = func.call @choose(%choice,%x,%y) : (i1,!F,!F)->!F
   %ok = algebra.field_equal %value,%expected : (!F,!F)->i1
   "protocol.guard"(%ok) {owner="P",site="first_demand"} : (i1)->()
   %twice = algebra.field_add %value,%value : (!F,!F)->!F
   "protocol.return"(%value,%twice) : (!F,!F)->()
 }) {sym_name="main",function_type=(i1,!F,!F,!F)->(!F,!F),roles=["P"],input_roles=[["P"],["P"],["P"],["P"]],output_roles=[["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
