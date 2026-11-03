!F = !algebra.field<"bls12-381.fr">
!Choice = !data.variant<#data.identity<["atom", "MathematicalChoice"]>, [#data.alternative<"none">, #data.alternative<"single", [!F]>, #data.alternative<"pair", [ui64, !F]>, #data.alternative<"empty">]>
!Record = !data.variant<#data.identity<["atom", "MathematicalRecord"]>, [#data.alternative<"record", [ui64, !F]>]>
module { "protocol.module"() ({
 func.func private @twice(%x:!F)->!F {
   %sum = algebra.field_add %x,%x : (!F,!F)->!F
   return %sum : !F
 }
 func.func private @choose(%choice:!Choice,%count:ui64,%x:!F)->!Record {
   %result = "data.branch"(%choice,%count,%x) ({
   ^none(%n:ui64,%value:!F):
     %record = "data.make"(%n,%value) {alternative="record"} : (ui64,!F)->!Record
     "data.yield"(%record) : (!Record)->()
   }, {
   ^single(%payload:!F,%n:ui64,%value:!F):
     %sum = func.call @twice(%payload) : (!F)->!F
     %record = "data.make"(%n,%sum) {alternative="record"} : (ui64,!F)->!Record
     "data.yield"(%record) : (!Record)->()
   }, {
   ^pair(%payload_count:ui64,%payload:!F,%n:ui64,%value:!F):
     %record = "data.make"(%payload_count,%payload) {alternative="record"} : (ui64,!F)->!Record
     "data.yield"(%record) : (!Record)->()
   }, {
   ^empty(%n:ui64,%value:!F):
     %zero = "data.index"() {value=0:ui64} : ()->ui64
     %record = "data.make"(%zero,%value) {alternative="record"} : (ui64,!F)->!Record
     "data.yield"(%record) : (!Record)->()
   }) {alternatives=["none","single","pair","empty"]} : (!Choice,ui64,!F)->!Record
   return %result : !Record
 }
 "protocol.func"() ({ ^entry(%choice:!Choice,%count:ui64,%x:!F):
   %record = func.call @choose(%choice,%count,%x) : (!Choice,ui64,!F)->!Record
   %n = "data.get"(%record) {index=0:i64} : (!Record)->ui64
   %value = "data.get"(%record) {index=1:i64} : (!Record)->!F
   "protocol.return"(%record,%n,%value) : (!Record,ui64,!F)->()
 }) {sym_name="main",function_type=(!Choice,ui64,!F)->(!Record,ui64,!F),roles=["P"],input_roles=[["P"],["P"],["P"]],output_roles=[["P"],["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
