!f = !algebra.field<"bn254.fr">
!g1 = !algebra.group<"bn254.g1">
!g2 = !algebra.group<"bn254.g2">
!b = !algebra.field<"koala-bear">
!e = !algebra.field<"koala-bear.ext8-binomial3">
!s = !protocol.service_ref<"random.koala-bear.ext8-binomial3/1">
!bnrng = !protocol.service_ref<"random.bn254.fr/1">
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%x:!f,%a:!g1,%b:!g2,%base:!b,%ext:!e,%random:!s,%bnrandom:!bnrng,%extrandom:!s):
   %bnDraw = "protocol.query"(%bnrandom) {owner="P",method="draw",site="bn_draw"} : (!bnrng)->!f
   %extDraw = "protocol.query"(%extrandom) {owner="P",method="draw",site="ext_draw"} : (!s)->!e
   %bnReceived = protocol.exchange %bnDraw {sender="P",receiver="V",site="bn_random"} : !f
   %extReceived = protocol.exchange %extDraw {sender="P",receiver="V",site="ext_random"} : !e
   %xP = algebra.field_add %x,%bnDraw : (!f,!f)->!f
   %xV = algebra.field_add %x,%bnReceived : (!f,!f)->!f
   %extP = algebra.field_add %ext,%extDraw : (!e,!e)->!e
   %extV = algebra.field_add %ext,%extReceived : (!e,!e)->!e
   %expectedA = algebra.group_scale %a,%xV : (!g1,!f)->!g1
   %expectedB = algebra.group_scale %b,%xV : (!g2,!f)->!g2
   %expectedScalar = algebra.field_multiply %xV,%xV : (!f,!f)->!f
   %scaledA = algebra.group_scale %a,%xP : (!g1,!f)->!g1
   %scaledB = algebra.group_scale %b,%xP : (!g2,!f)->!g2
   %sentA = protocol.exchange %scaledA {sender="P",receiver="V",site="a"} : !g1
   %sentB = protocol.exchange %scaledB {sender="P",receiver="V",site="b"} : !g2
   %square = algebra.field_multiply %xP,%xP : (!f,!f)->!f
   %sentScalar = protocol.exchange %square {sender="P",receiver="V",site="scalar"} : !f
   %base2 = algebra.field_multiply %base,%base : (!b,!b)->!b
   %sentBase = protocol.exchange %base2 {sender="P",receiver="V",site="base"} : !b
   %q = "protocol.query"(%random) {owner="V",method="draw",site="draw"} : (!s)->!e
   %challenge = protocol.exchange %q {sender="V",receiver="P",site="challenge"} : !e
   %sum = algebra.field_add %extP,%challenge : (!e,!e)->!e
   %sent = protocol.exchange %sum {sender="P",receiver="V",site="extension"} : !e
   %expectedExt = algebra.field_add %extV,%q : (!e,!e)->!e
   %okA = algebra.group_equal %sentA,%expectedA : (!g1,!g1)->i1
   %okB = algebra.group_equal %sentB,%expectedB : (!g2,!g2)->i1
   %okScalar = algebra.field_equal %sentScalar,%expectedScalar : (!f,!f)->i1
   %okBase = algebra.field_equal %sentBase,%base2 : (!b,!b)->i1
   %okExt = algebra.field_equal %sent,%expectedExt : (!e,!e)->i1
   %ab = arith.andi %okA,%okB : i1
   %be = arith.andi %okBase,%okExt : i1
   %combined = arith.andi %ab,%be : i1
   %ok = arith.andi %combined,%okScalar : i1
   "protocol.return"(%ok) : (i1)->()
 }) {sym_name="main",function_type=(!f,!g1,!g2,!b,!e,!s,!bnrng,!s)->i1,roles=["P","V"],input_roles=[["P","V"],["P","V"],["P","V"],["P","V"],["P","V"],["V"],["P"],["P"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
