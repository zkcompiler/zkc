!f = !algebra.field<"bls12-381.fr">
!r = !local.capability<"rng:bls12-381.fr">
!s = !protocol.service_ref<"random.bls12-381.fr/1">
module { "protocol.module"() ({
 "local.binding"() {sym_name="random",contract="random.draw",arguments=["bls12-381.fr"],implementation=""} : ()->()
 local.func @draw(%r:!r)->(!f,!r) attributes {logical_origin=["draw",[]]} {
   %sample:2 = "crypto.exec.random_draw"(%r) {binding=@random,parameters=[],site="sample"} : (!r)->(!f,!r)
   local.return %sample#0,%sample#1 : !f,!r
 }
 "local.binding"() {sym_name="inverse",contract="field.inverse",arguments=["bls12-381.fr"],implementation=""} : ()->()
 local.func @prepare(%zero:i1,%x:!f,%r:!r)->(!f,!r) attributes {logical_origin=["prepare",[]]} {
   %out:2 = "local.if"(%zero,%x,%r) ({ ^retry(%a:!f,%state:!r):
     "local.yield"(%a,%state) : (!f,!r)->()
   }, { ^ready(%a:!f,%state:!r):
     %inverse = "algebra.exec.field_inverse"(%a) {binding=@inverse,parameters=[],site="inverse"} : (!f)->!f
     "local.yield"(%inverse,%state) : (!f,!r)->()
   }) {site="partial_inverse"} : (i1,!f,!r)->(!f,!r)
   local.return %out#0,%out#1 : !f,!r
 }
 "protocol.func"() ({ ^entry(%a:!f,%b:!f,%rng:!r,%coins:!s):
   %sample:2 = "protocol.local_call"(%rng) {callee=@draw,role="P",site="salt"} : (!r)->(!f,!r)
   %zero = algebra.field_subtract %a,%a : (!f,!f)->!f
   %iszero = algebra.field_equal %sample#0,%zero : (!f,!f)->i1
   %yes = arith.constant true
   %complete = arith.xori %iszero,%yes : i1
   %prepared:2 = "protocol.local_call"(%iszero,%sample#0,%sample#1) {callee=@prepare,role="P",site="prepare"} : (i1,!f,!r)->(!f,!r)
   %salt = protocol.exchange %prepared#0 {sender="P",receiver="V",site="salt_message"} : !f
   %bound = "data.index"() {value="2"} : ()->ui64
   %carried = "protocol.repeat"(%bound,%prepared#1,%iszero,%complete) ({
   ^outer(%i:ui64,%outer_rng:!r,%abandon:i1,%done:i1):
     %one = "data.index"() {value="1"} : ()->ui64
     %inside = "protocol.repeat"(%one,%outer_rng,%abandon,%done) ({
     ^inner(%j:ui64,%r:!r,%stop:i1,%result:i1):
       %next = "protocol.finish_if"(%stop,%result,%r) {owner="P",site="abandon"} : (i1,i1,!r)->!r
       "protocol.yield"(%next) : (!r)->()
     }) {site="inner",carried=1:i64,maximum=1:i64,roles=["P"],carried_roles=[["P"]]} : (ui64,!r,i1,i1)->!r
     "protocol.yield"(%inside) : (!r)->()
   }) {site="outer",carried=1:i64,maximum=2:i64,roles=["P"],carried_roles=[["P"]]} : (ui64,!r,i1,i1)->!r
   %n = "data.index"() {value="2"} : ()->ui64
   %fold:2 = "protocol.repeat"(%n,%a,%a,%b,%coins) ({
   ^round(%i:ui64,%left:!f,%right:!f,%step:!f,%random:!s):
     %message = protocol.exchange %left {sender="P",receiver="V",site="coefficient"} : !f
     %same = algebra.field_equal %message,%right : (!f,!f)->i1
     protocol.guard %same {owner="V",site="coefficient_check"}
     %c = "protocol.query"(%random) {method="draw",owner="V",site="draw"} : (!s)->!f
     %challenge = protocol.exchange %c {sender="V",receiver="P",site="challenge"} : !f
     %p = algebra.field_multiply %challenge,%step : (!f,!f)->!f
     %v = algebra.field_multiply %c,%step : (!f,!f)->!f
     %nextP = algebra.field_add %left,%p : (!f,!f)->!f
     %nextV = algebra.field_add %right,%v : (!f,!f)->!f
     "protocol.yield"(%nextP,%nextV) : (!f,!f)->()
   }) {site="fold",carried=2:i64,maximum=2:i64,roles=["P","V"],carried_roles=[["P"],["V"]]} : (ui64,!f,!f,!f,!s)->(!f,!f)
   %final = protocol.exchange %fold#0 {sender="P",receiver="V",site="result"} : !f
   %accepted = algebra.field_equal %final,%fold#1 : (!f,!f)->i1
   "protocol.return"(%accepted,%complete,%carried) : (i1,i1,!r)->()
 }) {sym_name="main",function_type=(!f,!f,!r,!s)->(i1,i1,!r),roles=["P","V"],input_roles=[["P","V"],["P","V"],["P"],["V"]],output_roles=[["V"],["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
