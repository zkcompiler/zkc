!F = !algebra.field<"bls12-381.fr">
!V = !data.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
 "data.domain"() ({ ^entry(%lo:ui64,%hi:ui64):
   %d = "data.domain_range"(%lo,%hi) : (ui64,ui64)->!data.domain<ui64>
   "data.domain_yield"(%d) : (!data.domain<ui64>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(ui64,ui64)->!data.domain<ui64>} : ()->()
 func.func private @element(%i:ui64,%lo:ui64,%hi:ui64,%value:!F)->!F {
   return %value : !F
 }
 func.func private @step(%state:!F,%i:ui64,%lo:ui64,%hi:ui64,%value:!F,%enabled:i1)->!F {
   %result = "data.branch"(%enabled,%state,%value) ({
   ^then(%acc:!F,%x:!F):
     %sum = algebra.field_add %acc,%x : (!F,!F)->!F
     "data.yield"(%sum) : (!F)->()
   }, {
   ^else(%acc:!F,%x:!F):
     "data.yield"(%acc) : (!F)->()
   }) {alternatives=["then","else"]} : (i1,!F,!F)->!F
   return %result : !F
 }
 "protocol.func"() ({ ^entry(%enabled:i1,%count:ui64,%value:!F):
   %zero = "data.index"() {value=0:ui64} : ()->ui64
   %result = "data.branch"(%enabled,%zero,%count,%value) ({
   ^then(%lo:ui64,%hi:ui64,%x:!F):
     %values = "data.finite_collect"(%lo,%hi,%x) {domain=@items,body=@element} : (ui64,ui64,!F)->!V
     %length = "data.dim"(%values) {axis=0:i64} : (!V)->ui64
     "data.yield"(%length) : (ui64)->()
   }, {
   ^else(%lo:ui64,%hi:ui64,%x:!F):
     "data.yield"(%lo) : (ui64)->()
   }) {alternatives=["then","else"]} : (i1,ui64,ui64,!F)->ui64
   %total = "data.finite_fold"(%zero,%count,%value,%value,%enabled) {domain=@items,step=@step} : (ui64,ui64,!F,!F,i1)->!F
   "protocol.return"(%result,%total) : (ui64,!F)->()
 }) {sym_name="main",function_type=(i1,ui64,!F)->(ui64,!F),roles=["P"],input_roles=[["P"],["P"],["P"]],output_roles=[["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
