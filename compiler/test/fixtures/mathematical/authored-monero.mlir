// Exact encoded-word hash transitions. This is a transcript consistency client.
!words = tensor<?xui64>
!rounds = !data.sequence<!words>
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
 "local.binding"() {sym_name="binding_init",contract="external.monero.init",arguments=[],implementation=""} : ()->()
 local.func @init(%a0:!words)->(!words) attributes {logical_origin=["init",[]]} {
   %v = "crypto.exec.monero_init"(%a0) {binding=@binding_init,parameters=[],site="step"} : (!words)->(!words)
   local.return %v : !words
 }
 "local.binding"() {sym_name="binding_update",contract="external.monero.update",arguments=[],implementation=""} : ()->()
 local.func @update(%a0:!words,%a1:!words)->(!words,!words) attributes {logical_origin=["update",[]]} {
   %v:2 = "crypto.exec.monero_update"(%a0,%a1) {binding=@binding_update,parameters=[],site="step"} : (!words,!words)->(!words,!words)
   local.return %v#0,%v#1 : !words,!words
 }
 "local.binding"() {sym_name="round_at",contract="sequence.at",arguments=["indices"],implementation=""} : ()->()
 "local.binding"() {sym_name="empty",contract="indices.empty",arguments=[],implementation=""} : ()->()
 local.func @round(%rounds:!rounds,%i:ui64)->!words attributes {logical_origin=["round",[]]} {
   %word = "data.exec.sequence_at"(%rounds,%i) {binding=@round_at,parameters=[],site="word"} : (!rounds,ui64)->!words
   local.return %word : !words
 }
 local.func @finish(%state:!words)->!words attributes {logical_origin=["finish",[]]} {
   %empty = "algebra.exec.indices_empty"() {binding=@empty,parameters=[],site="empty"} : ()->!words
   %v:2 = "crypto.exec.monero_update"(%state,%empty) {binding=@binding_update,parameters=[],site="final"} : (!words,!words)->(!words,!words)
   local.return %v#1 : !words
 }
 "protocol.func"() ({ ^entry(%seed:!words,%context:!words,%count:ui64,%rounds:!rounds,%complete:i1):
   %p = "protocol.local_call"(%seed) {callee=@init,role="P",site="init_p"} : (!words)->!words
   %v = "protocol.local_call"(%seed) {callee=@init,role="V",site="init_v"} : (!words)->!words
   %p0:2 = "protocol.local_call"(%p,%context) {callee=@update,role="P",site="context_p"} : (!words,!words)->(!words,!words)
   %v0:2 = "protocol.local_call"(%v,%context) {callee=@update,role="V",site="context_v"} : (!words,!words)->(!words,!words)
   %states:2 = "protocol.repeat"(%count,%p0#0,%v0#0,%rounds) ({ ^step(%i:ui64,%ps:!words,%vs:!words,%items:!rounds):
     %word = "protocol.local_call"(%items,%i) {callee=@round,role="P",site="word"} : (!rounds,ui64)->!words
     %received = protocol.exchange %word {sender="P",receiver="V",site="word_message"} : !words
     %pn:2 = "protocol.local_call"(%ps,%word) {callee=@update,role="P",site="step_p"} : (!words,!words)->(!words,!words)
     %vn:2 = "protocol.local_call"(%vs,%received) {callee=@update,role="V",site="step_v"} : (!words,!words)->(!words,!words)
     "protocol.yield"(%pn#0,%vn#0) : (!words,!words)->()
   }) {site="rounds",carried=2:i64,maximum=64:i64,roles=["P","V"],carried_roles=[["P"],["V"]]} : (ui64,!words,!words,!rounds)->(!words,!words)
   %final_p = "protocol.local_call"(%states#0) {callee=@finish,role="P",site="final_p"} : (!words)->!words
   %final_v = "protocol.local_call"(%states#1) {callee=@finish,role="V",site="final_v"} : (!words)->!words
   %claim = protocol.exchange %final_p {sender="P",receiver="V",site="claim"} : !words
   %ok = "protocol.local_call"(%claim,%final_v) {callee=@same,role="V",site="terminal"} : (!words,!words)->i1
   "protocol.return"(%ok,%complete) : (i1,i1)->()
 }) {sym_name="main",function_type=(!words,!words,ui64,!rounds,i1)->(i1,i1),roles=["P","V"],input_roles=[["P","V"],["P","V"],["P","V"],["P"],["P"]],output_roles=[["V"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
