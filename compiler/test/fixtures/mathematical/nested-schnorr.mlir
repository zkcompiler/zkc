!f = !algebra.field<"bls12-381.fr">
!g = !algebra.group<"bls12-381.g1">
!rng = !protocol.service_ref<"random.bls12-381.fr/1">
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%g:!g,%x:!f,%y:!g,%nonce:!rng,%challenge_service:!rng):
%k = "protocol.query"(%nonce) {method="draw", owner="P", site="nonce"} : (!rng) -> !f
%r = algebra.group_scale %g, %k : (!g, !f) -> !g
%commitment = protocol.exchange %r {site="commitment",sender="P",receiver="V"} : !g
%c = "protocol.query"(%challenge_service) {method="draw", owner="V", site="draw_challenge"} : (!rng) -> !f
%challenge = protocol.exchange %c {site="challenge",sender="V",receiver="P"} : !f
%cx = algebra.field_multiply %challenge, %x : (!f, !f) -> !f
%z = algebra.field_add %k, %cx : (!f, !f) -> !f
%response = protocol.exchange %z {site="response",sender="P",receiver="V"} : !f
%lhs = algebra.group_scale %g, %response : (!g, !f) -> !g
%cy = algebra.group_scale %y, %challenge : (!g, !f) -> !g
%rhs = algebra.group_add %commitment, %cy : (!g, !g) -> !g
%ok = algebra.group_equal %lhs, %rhs : (!g, !g) -> i1
protocol.guard %ok {owner="V",site="equation"}
"protocol.return"() : ()->()
 }) {sym_name="step",function_type=(!g,!f,!g,!rng,!rng)->(),roles=["P","V"],input_roles=[["P","V"],["P"],["P","V"],["P"],["V"]],output_roles=[]} : ()->()
 "protocol.func"() ({ ^entry(%n:ui64,%g:!g,%x:!f,%y:!g,%nonce:!rng,%coins:!rng):
   "protocol.repeat"(%n,%g,%x,%y,%nonce,%coins) ({
   ^body(%j:ui64,%G:!g,%X:!f,%Y:!g,%N:!rng,%C:!rng):
     "protocol.apply"(%G,%X,%Y,%N,%C) {callee=@step,roles=["P","V"],site="first"} : (!g,!f,!g,!rng,!rng)->()
     "protocol.apply"(%G,%X,%Y,%N,%C) {callee=@step,roles=["P","V"],site="second"} : (!g,!f,!g,!rng,!rng)->()
     "protocol.yield"() : ()->()
   }) {site="inner",carried=0:i64,maximum=8:i64,roles=["P","V"],carried_roles=[]} : (ui64,!g,!f,!g,!rng,!rng)->()
   "protocol.return"() : ()->()
 }) {sym_name="segment",function_type=(ui64,!g,!f,!g,!rng,!rng)->(),roles=["P","V"],input_roles=[["P","V"],["P","V"],["P"],["P","V"],["P"],["V"]],output_roles=[]} : ()->()
 "protocol.func"() ({ ^entry(%n:ui64,%g:!g,%x:!f,%y:!g,%nonce:!rng,%coins:!rng):
   "protocol.repeat"(%n,%g,%x,%y,%nonce,%coins) ({
   ^body(%i:ui64,%G:!g,%X:!f,%Y:!g,%N:!rng,%C:!rng):
     %m = protocol.exchange %i {sender="P",receiver="V",site="inner_count"} : ui64
     "protocol.apply"(%m,%G,%X,%Y,%N,%C) {callee=@segment,roles=["P","V"],site="segment"} : (ui64,!g,!f,!g,!rng,!rng)->()
     "protocol.yield"() : ()->()
   }) {site="outer",carried=0:i64,maximum=8:i64,roles=["P","V"],carried_roles=[]} : (ui64,!g,!f,!g,!rng,!rng)->()
   // Owner-local work has no transcript events and needs no transcript carry.
   "protocol.repeat"(%n) ({
   ^body(%j:ui64):
     %same = "data.index_equal"(%j,%j) : (ui64,ui64)->i1
     protocol.guard %same {owner="P",site="local_check"}
     "protocol.yield"() : ()->()
   }) {site="local_work",carried=0:i64,maximum=8:i64,roles=["P"],carried_roles=[]} : (ui64)->()
   %accepted = arith.constant true
   "protocol.return"(%accepted) : (i1)->()
 }) {sym_name="main",function_type=(ui64,!g,!f,!g,!rng,!rng)->i1,roles=["P","V"],input_roles=[["P","V"],["P","V"],["P"],["P","V"],["P"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
