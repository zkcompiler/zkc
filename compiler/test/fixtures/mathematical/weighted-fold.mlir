!f = !algebra.field<"bls12-381.fr">
!v = tensor<?x!f>
!rng = !protocol.service_ref<"random.bls12-381.fr/1">
module { "protocol.module"() ({
 "local.binding"() {sym_name="split",contract="vector.split",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="dot",contract="vector.dot",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="scale",contract="vector.scale",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="add",contract="vector.add",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="inverse",contract="field.inverse",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="length",contract="vector.length_check",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="at",contract="vector.at",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="require",contract="control.require",arguments=[],implementation=""} : ()->()

 local.func @cross_terms(%a:!v,%b:!v) -> (!f,!f) attributes {logical_origin=["cross_terms",[]]} {
   %aSplit:2 = "algebra.exec.vector_split"(%a) {binding=@split,parameters=[],site="splitA"} : (!v)->(!v,!v)
   %bSplit:2 = "algebra.exec.vector_split"(%b) {binding=@split,parameters=[],site="splitB"} : (!v)->(!v,!v)
   %L = "algebra.exec.vector_dot"(%aSplit#0,%bSplit#1) {binding=@dot,parameters=[],site="left"} : (!v,!v)->!f
   %R = "algebra.exec.vector_dot"(%aSplit#1,%bSplit#0) {binding=@dot,parameters=[],site="right"} : (!v,!v)->!f
   local.return %L,%R : !f,!f
 }
 local.func @invert(%x:!f) -> !f attributes {logical_origin=["invert",[]]} {
   %v = "algebra.exec.field_inverse"(%x) {binding=@inverse,parameters=[],site="nonzero"} : (!f)->!f
   local.return %v : !f
 }
 local.func @weighted_fold(%a:!v,%b:!v,%x:!f) -> (!v,!v) attributes {logical_origin=["weighted_fold",[]]} {
   %ix = "algebra.exec.field_inverse"(%x) {binding=@inverse,parameters=[],site="nonzero"} : (!f)->!f
   %aSplit:2 = "algebra.exec.vector_split"(%a) {binding=@split,parameters=[],site="splitA"} : (!v)->(!v,!v)
   %bSplit:2 = "algebra.exec.vector_split"(%b) {binding=@split,parameters=[],site="splitB"} : (!v)->(!v,!v)
   %aL = "algebra.exec.vector_scale"(%aSplit#0,%x) {binding=@scale,parameters=[],site="scaleAL"} : (!v,!f)->!v
   %aR = "algebra.exec.vector_scale"(%aSplit#1,%ix) {binding=@scale,parameters=[],site="scaleAR"} : (!v,!f)->!v
   %bL = "algebra.exec.vector_scale"(%bSplit#0,%ix) {binding=@scale,parameters=[],site="scaleBL"} : (!v,!f)->!v
   %bR = "algebra.exec.vector_scale"(%bSplit#1,%x) {binding=@scale,parameters=[],site="scaleBR"} : (!v,!f)->!v
   %nextA = "algebra.exec.vector_add"(%aL,%aR) {binding=@add,parameters=[],site="addA"} : (!v,!v)->!v
   %nextB = "algebra.exec.vector_add"(%bL,%bR) {binding=@add,parameters=[],site="addB"} : (!v,!v)->!v
   local.return %nextA,%nextB : !v,!v
 }
 local.func @terminal_values(%a:!v,%b:!v) -> (!f,!f) attributes {logical_origin=["terminal_values",[]]} {
   %aOne = "algebra.exec.vector_length_check"(%a) {binding=@length,parameters=["1"],site="lengthA"} : (!v)->i1
   "local.exec.require"(%aOne) {binding=@require,parameters=[],site="shapeA"} : (i1)->()
   %bOne = "algebra.exec.vector_length_check"(%b) {binding=@length,parameters=["1"],site="lengthB"} : (!v)->i1
   "local.exec.require"(%bOne) {binding=@require,parameters=[],site="shapeB"} : (i1)->()
   %a0 = "algebra.exec.vector_at"(%a) {binding=@at,parameters=["0"],site="valueA"} : (!v)->!f
   %b0 = "algebra.exec.vector_at"(%b) {binding=@at,parameters=["0"],site="valueB"} : (!v)->!f
   local.return %a0,%b0 : !f,!f
 }
 "protocol.func"() ({ ^entry(%n:ui64,%a:!v,%b:!v,%claim:!f,%coins:!rng):
   %done:3 = "protocol.repeat"(%n,%a,%b,%claim,%coins) ({
   ^round(%i:ui64,%av:!v,%bv:!v,%current:!f,%random:!rng):
     %cross:2 = "protocol.local_call"(%av,%bv) {callee=@cross_terms,role="P",site="cross_terms"} : (!v,!v)->(!f,!f)
     %L = protocol.exchange %cross#0 {sender="P",receiver="V",site="left"} : !f
     %R = protocol.exchange %cross#1 {sender="P",receiver="V",site="right"} : !f
     %x = "protocol.query"(%random) {method="draw",owner="V",site="draw"} : (!rng)->!f
     %ix = "protocol.local_call"(%x) {callee=@invert,role="V",site="verifier_inverse"} : (!f)->!f
     %xP = protocol.exchange %x {sender="V",receiver="P",site="challenge"} : !f
     %folded:2 = "protocol.local_call"(%av,%bv,%xP) {callee=@weighted_fold,role="P",site="fold"} : (!v,!v,!f)->(!v,!v)
     %xx = algebra.field_multiply %x,%x : (!f,!f)->!f
     %ii = algebra.field_multiply %ix,%ix : (!f,!f)->!f
     %weightedL = algebra.field_multiply %xx,%L : (!f,!f)->!f
     %weightedR = algebra.field_multiply %ii,%R : (!f,!f)->!f
     %cross_sum = algebra.field_add %weightedL,%weightedR : (!f,!f)->!f
     %next = algebra.field_add %current,%cross_sum : (!f,!f)->!f
     "protocol.yield"(%folded#0,%folded#1,%next) : (!v,!v,!f)->()
   }) {site="rounds",carried=3:i64,maximum=8:i64,roles=["P","V"],carried_roles=[["P"],["P"],["V"]]} : (ui64,!v,!v,!f,!rng)->(!v,!v,!f)
   %terminal:2 = "protocol.local_call"(%done#0,%done#1) {callee=@terminal_values,role="P",site="terminal"} : (!v,!v)->(!f,!f)
   %aV = protocol.exchange %terminal#0 {sender="P",receiver="V",site="terminalA"} : !f
   %bV = protocol.exchange %terminal#1 {sender="P",receiver="V",site="terminalB"} : !f
   %product = algebra.field_multiply %aV,%bV : (!f,!f)->!f
   %accepted = algebra.field_equal %product,%done#2 : (!f,!f)->i1
   "protocol.return"(%accepted,%terminal#0,%terminal#1) : (i1,!f,!f)->()
 }) {sym_name="main",function_type=(ui64,!v,!v,!f,!rng)->(i1,!f,!f),roles=["P","V"],input_roles=[["P","V"],["P"],["P"],["V"],["V"]],output_roles=[["V"],["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
