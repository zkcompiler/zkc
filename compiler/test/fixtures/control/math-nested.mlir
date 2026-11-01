!F = !algebra.field<"bls12-381.fr">
!Tuple = !data.variant<#data.identity<["tuple", [["atom", "bls12-381.fr"], ["atom", "bls12-381.fr"]]]>, [#data.alternative<"value", [!F, !F]>]>
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
 "protocol.func"() ({ ^entry(%outer:i1,%inner:i1,%x:!F,%y:!F):
   %before = func.call @choose(%inner,%x,%y) : (i1,!F,!F)->!F
   %pair = "data.branch"(%outer,%inner,%x,%y,%before) ({
   ^then(%choice:i1,%left:!F,%right:!F,%prior:!F):
     %selected = func.call @choose(%choice,%left,%right) : (i1,!F,!F)->!F
     %tuple = "data.make"(%selected,%prior) {alternative="value"} : (!F,!F)->!Tuple
     "data.yield"(%tuple) : (!Tuple)->()
   }, {
   ^else(%choice:i1,%left:!F,%right:!F,%prior:!F):
     %tuple = "data.make"(%right,%left) {alternative="value"} : (!F,!F)->!Tuple
     "data.yield"(%tuple) : (!Tuple)->()
   }) {alternatives=["then","else"]} : (i1,i1,!F,!F,!F)->!Tuple
   %first = "data.get"(%pair) {index=0:i64} : (!Tuple)->!F
   %second = "data.get"(%pair) {index=1:i64} : (!Tuple)->!F
   "protocol.return"(%pair,%first,%second) : (!Tuple,!F,!F)->()
 }) {sym_name="main",function_type=(i1,i1,!F,!F)->(!Tuple,!F,!F),roles=["P"],input_roles=[["P"],["P"],["P"],["P"]],output_roles=[["P"],["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
