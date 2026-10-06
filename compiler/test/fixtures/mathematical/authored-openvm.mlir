// Candidate search uses immutable trials and checks the chosen witness on live state.
!words = tensor<?xui64>
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
 "local.binding"() {sym_name="binding_init",contract="external.openvm.init",arguments=[],implementation=""} : ()->()
 local.func @init()->(!words) attributes {logical_origin=["init",[]]} {
   %v = "crypto.exec.openvm_init"() {binding=@binding_init,parameters=[],site="step"} : ()->(!words)
   local.return %v : !words
 }
 "local.binding"() {sym_name="binding_observe",contract="external.openvm.observe",arguments=[],implementation=""} : ()->()
 local.func @observe(%a0:!words,%a1:!words)->(!words) attributes {logical_origin=["observe",[]]} {
   %v = "crypto.exec.openvm_observe"(%a0,%a1) {binding=@binding_observe,parameters=[],site="step"} : (!words,!words)->(!words)
   local.return %v : !words
 }
 "local.binding"() {sym_name="binding_check",contract="external.openvm.check_witness",arguments=[],implementation=""} : ()->()
 local.func @check(%a0:!words,%a1:ui64,%a2:ui64)->(!words,i1) attributes {logical_origin=["check",[]]} {
   %v:2 = "crypto.exec.openvm_check_witness"(%a0,%a1,%a2) {binding=@binding_check,parameters=[],site="step"} : (!words,ui64,ui64)->(!words,i1)
   local.return %v#0,%v#1 : !words,i1
 }
 "local.binding"() {sym_name="ext",contract="external.openvm.sample_ext",arguments=[],implementation=""} : ()->()
 "local.binding"() {sym_name="bits",contract="external.openvm.sample_bits",arguments=[],implementation=""} : ()->()
 "local.binding"() {sym_name="scalar",contract="external.openvm.sample",arguments=[],implementation=""} : ()->()
 local.func @samples(%state:!words,%width:ui64)->(!words,ui64,ui64) attributes {logical_origin=["samples",[]]} {
   %ext:2 = "crypto.exec.openvm_sample_ext"(%state) {binding=@ext,parameters=[],site="extension"} : (!words)->(!words,!words)
   %bits:2 = "crypto.exec.openvm_sample_bits"(%ext#0,%width) {binding=@bits,parameters=[],site="bits"} : (!words,ui64)->(!words,ui64)
   %scalar:2 = "crypto.exec.openvm_sample"(%bits#0) {binding=@scalar,parameters=[],site="scalar"} : (!words)->(!words,ui64)
   local.return %ext#1,%bits#1,%scalar#1 : !words,ui64,ui64
 }
 local.func @search(%live:!words,%difficulty:ui64,%candidates:!words)->(ui64,i1) attributes {logical_origin=["search",[]]} {
   %zero = "algebra.exec.index_constant"() {binding=@constant,parameters=["0"],site="zero"} : ()->ui64
   %no = "local.bool_constant"() {value=false,site="no"} : ()->i1
   %count = "algebra.exec.indices_length"(%candidates) {binding=@length,parameters=[],site="count"} : (!words)->ui64
   %result:2 = "local.for"(%zero,%count,%zero,%no,%live,%difficulty,%candidates) ({ ^candidate(%i:ui64,%chosen:ui64,%found:i1,%state:!words,%width:ui64,%choices:!words):
     %next:2 = "local.if"(%found,%chosen,%state,%width,%choices,%i) ({ ^done(%w:ui64,%s:!words,%b:ui64,%cs:!words,%j:ui64):
       %yes = "local.bool_constant"() {value=true,site="found"} : ()->i1
       "local.yield"(%w,%yes) : (ui64,i1)->()
     }, { ^trial(%w:ui64,%s:!words,%b:ui64,%cs:!words,%j:ui64):
       %witness = "algebra.exec.indices_at"(%cs,%j) {binding=@at,parameters=[],site="candidate"} : (!words,ui64)->ui64
       %checked:2 = "crypto.exec.openvm_check_witness"(%s,%b,%witness) {binding=@binding_check,parameters=[],site="trial"} : (!words,ui64,ui64)->(!words,i1)
       "local.yield"(%witness,%checked#1) : (ui64,i1)->()
     }) {site="searching"} : (i1,ui64,!words,ui64,!words,ui64)->(ui64,i1)
     "local.yield"(%next#0,%next#1,%state,%width,%choices) : (ui64,i1,!words,ui64,!words)->()
   }) {site="candidates"} : (ui64,ui64,ui64,i1,!words,ui64,!words)->(ui64,i1)
   local.return %result#0,%result#1 : ui64,i1
 }
 "protocol.func"() ({ ^entry(%context:!words,%difficulty:ui64,%width:ui64,%candidates:!words):
   %p = "protocol.local_call"() {callee=@init,role="P",site="init_p"} : ()->!words
   %v = "protocol.local_call"() {callee=@init,role="V",site="init_v"} : ()->!words
   %ps = "protocol.local_call"(%p,%context) {callee=@observe,role="P",site="context_p"} : (!words,!words)->!words
   %vs = "protocol.local_call"(%v,%context) {callee=@observe,role="V",site="context_v"} : (!words,!words)->!words
   %choice:2 = "protocol.local_call"(%ps,%difficulty,%candidates) {callee=@search,role="P",site="search"} : (!words,ui64,!words)->(ui64,i1)
   %witness = protocol.exchange %choice#0 {sender="P",receiver="V",site="witness"} : ui64
   %pchecked:2 = "protocol.local_call"(%ps,%difficulty,%choice#0) {callee=@check,role="P",site="live_p"} : (!words,ui64,ui64)->(!words,i1)
   %vchecked:2 = "protocol.local_call"(%vs,%difficulty,%witness) {callee=@check,role="V",site="live_v"} : (!words,ui64,ui64)->(!words,i1)
   protocol.guard %vchecked#1 {owner="V",site="witness_valid"}
   %pout:3 = "protocol.local_call"(%pchecked#0,%width) {callee=@samples,role="P",site="samples_p"} : (!words,ui64)->(!words,ui64,ui64)
   %vout:3 = "protocol.local_call"(%vchecked#0,%width) {callee=@samples,role="V",site="samples_v"} : (!words,ui64)->(!words,ui64,ui64)
   %extension = protocol.exchange %pout#0 {sender="P",receiver="V",site="extension"} : !words
   %bits = protocol.exchange %pout#1 {sender="P",receiver="V",site="bits"} : ui64
   %scalar = protocol.exchange %pout#2 {sender="P",receiver="V",site="scalar"} : ui64
   %eq = "protocol.local_call"(%extension,%vout#0) {callee=@same,role="V",site="extension_equal"} : (!words,!words)->i1
   %bits_ok = "data.index_equal"(%bits,%vout#1) : (ui64,ui64)->i1
   %scalar_ok = "data.index_equal"(%scalar,%vout#2) : (ui64,ui64)->i1
   %both = arith.andi %eq,%bits_ok : i1
   %ok = arith.andi %both,%scalar_ok : i1
   "protocol.return"(%ok,%choice#1) : (i1,i1)->()
 }) {sym_name="main",function_type=(!words,ui64,ui64,!words)->(i1,i1),roles=["P","V"],input_roles=[["P","V"],["P","V"],["P","V"],["P"]],output_roles=[["V"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
