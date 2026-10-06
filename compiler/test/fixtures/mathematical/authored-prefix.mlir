// A returned retry skips a local suffix but still reaches the later send.
!words = tensor<?xui64>
!f = !algebra.field<"bls12-381.fr">
!rng = !local.capability<"rng:bls12-381.fr">
module { "protocol.module"() ({
 "local.binding"() {sym_name="constant",contract="index.constant",arguments=[],implementation=""} : ()->()
 "local.binding"() {sym_name="length",contract="indices.length",arguments=[],implementation=""} : ()->()
 "local.binding"() {sym_name="at",contract="indices.at",arguments=[],implementation=""} : ()->()
 "local.binding"() {sym_name="equal",contract="index.equal",arguments=[],implementation=""} : ()->()
 "local.binding"() {sym_name="and",contract="bool.and",arguments=[],implementation=""} : ()->()
 local.func @same(%a:!words,%b:!words)->i1 attributes {logical_origin=["same",[]]} {
   %n = "algebra.exec.indices_length"(%a) {binding=@length,parameters=[],site="n"} : (!words)->ui64
   %m = "algebra.exec.indices_length"(%b) {binding=@length,parameters=[],site="m"} : (!words)->ui64
   %eq = "algebra.exec.index_equal"(%n,%m) {binding=@equal,parameters=[],site="lengths"} : (ui64,ui64)->i1
   %result = "local.if"(%eq,%a,%b,%n) ({ ^same_length(%left:!words,%right:!words,%count:ui64):
     %zero = "algebra.exec.index_constant"() {binding=@constant,parameters=["0"],site="zero"} : ()->ui64
     %yes = "local.bool_constant"() {value=true,site="yes"} : ()->i1
     %checked = "local.for"(%zero,%count,%yes,%left,%right) ({ ^element(%i:ui64,%ok:i1,%l:!words,%r:!words):
       %x = "algebra.exec.indices_at"(%l,%i) {binding=@at,parameters=[],site="left"} : (!words,ui64)->ui64
       %y = "algebra.exec.indices_at"(%r,%i) {binding=@at,parameters=[],site="right"} : (!words,ui64)->ui64
       %same = "algebra.exec.index_equal"(%x,%y) {binding=@equal,parameters=[],site="same"} : (ui64,ui64)->i1
       %next = "algebra.exec.bool_and"(%ok,%same) {binding=@and,parameters=[],site="next"} : (i1,i1)->i1
       "local.yield"(%next,%l,%r) : (i1,!words,!words)->()
     }) {site="elements"} : (ui64,ui64,i1,!words,!words)->i1
     "local.yield"(%checked) : (i1)->()
   }, { ^different_length(%left:!words,%right:!words,%count:ui64):
     %no = "local.bool_constant"() {value=false,site="no"} : ()->i1
     "local.yield"(%no) : (i1)->()
   }) {site="compare"} : (i1,!words,!words,ui64)->i1
   local.return %result : i1
 }
 "local.binding"() {sym_name="init",contract="external.monero.init",arguments=[],implementation=""} : ()->()
 "local.binding"() {sym_name="update",contract="external.monero.update",arguments=[],implementation=""} : ()->()
 "local.binding"() {sym_name="random",contract="random.draw",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="zero",contract="field.constant",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="field_equal",contract="field.equal",arguments=["bls12-381.fr"],implementation=""} : ()->()
 local.func @prepare(%seed:!words,%context:!words,%rng:!rng)->(!words,i1,!rng) attributes {logical_origin=["prepare",[]]} {
   %draw:2 = "crypto.exec.random_draw"(%rng) {binding=@random,parameters=[],site="prefix_draw"} : (!rng)->(!f,!rng)
   %state = "crypto.exec.monero_init"(%seed) {binding=@init,parameters=[],site="init"} : (!words)->!words
   %prefix:2 = "crypto.exec.monero_update"(%state,%context) {binding=@update,parameters=[],site="prefix_hash"} : (!words,!words)->(!words,!words)
   %zero = "algebra.exec.field_constant"() {binding=@zero,parameters=["0"],site="zero"} : ()->!f
   %retry = "algebra.exec.field_equal"(%draw#0,%zero) {binding=@field_equal,parameters=[],site="decision"} : (!f,!f)->i1
   %result:3 = "local.if"(%retry,%prefix#0,%prefix#1,%context,%draw#1) ({ ^abandoned(%s:!words,%challenge:!words,%ctx:!words,%r:!rng):
     %no = "local.bool_constant"() {value=false,site="retry"} : ()->i1
     "local.yield"(%challenge,%no,%r) : (!words,i1,!rng)->()
   }, { ^continue(%s:!words,%challenge:!words,%ctx:!words,%r:!rng):
     %next:2 = "crypto.exec.random_draw"(%r) {binding=@random,parameters=[],site="suffix_draw"} : (!rng)->(!f,!rng)
     %suffix:2 = "crypto.exec.monero_update"(%s,%ctx) {binding=@update,parameters=[],site="suffix_hash"} : (!words,!words)->(!words,!words)
     %yes = "local.bool_constant"() {value=true,site="complete"} : ()->i1
     "local.yield"(%suffix#1,%yes,%next#1) : (!words,i1,!rng)->()
   }) {site="suffix"} : (i1,!words,!words,!words,!rng)->(!words,i1,!rng)
   local.return %result#0,%result#1,%result#2 : !words,i1,!rng
 }
 local.func @expected(%seed:!words,%context:!words)->!words attributes {logical_origin=["expected",[]]} {
   %state = "crypto.exec.monero_init"(%seed) {binding=@init,parameters=[],site="init"} : (!words)->!words
   %first:2 = "crypto.exec.monero_update"(%state,%context) {binding=@update,parameters=[],site="first"} : (!words,!words)->(!words,!words)
   %second:2 = "crypto.exec.monero_update"(%first#0,%context) {binding=@update,parameters=[],site="second"} : (!words,!words)->(!words,!words)
   local.return %second#1 : !words
 }
 "protocol.func"() ({ ^entry(%seed:!words,%context:!words,%rng:!rng):
   %prepared:3 = "protocol.local_call"(%seed,%context,%rng) {callee=@prepare,role="P",site="prepare"} : (!words,!words,!rng)->(!words,i1,!rng)
   %claim = protocol.exchange %prepared#0 {sender="P",receiver="V",site="claim"} : !words
   %expected = "protocol.local_call"(%seed,%context) {callee=@expected,role="V",site="expected"} : (!words,!words)->!words
   %ok = "protocol.local_call"(%claim,%expected) {callee=@same,role="V",site="terminal"} : (!words,!words)->i1
   "protocol.return"(%ok,%prepared#1,%prepared#2) : (i1,i1,!rng)->()
 }) {sym_name="main",function_type=(!words,!words,!rng)->(i1,i1,!rng),roles=["P","V"],input_roles=[["P","V"],["P","V"],["P"]],output_roles=[["V"],["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
