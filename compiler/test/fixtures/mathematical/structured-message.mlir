!f = !algebra.field<"bls12-381.fr">
!v = tensor<?x!f>
!mode = !local.variant<"variant:5b227a6b632e76617269616e74222c5b224261746368222c226e6f6e65222c5b5d2c5b2231222c2232225d2c22706c61696e222c22766563746f723a626c7331322d3338312e6672222c5b2235225d2c5b2234222c2236225d2c227363616c6564222c226669656c643a626c7331322d3338312e6672222c5b2235222c2239225d2c5b2238222c223130225d2c5b2233222c2237222c223131225d2c5b2230222c223132225d5d5d">
!packet = !local.variant<"variant:5b227a6b632e76617269616e74222c5b22416e6e6f756e63656d656e74222c227265636f7264222c2267726f75703a626c7331322d3338312e6731222c224261746368222c226e6f6e65222c5b5d2c5b2234222c2235225d2c22706c61696e222c22766563746f723a626c7331322d3338312e6672222c5b2238225d2c5b2237222c2239225d2c227363616c6564222c226669656c643a626c7331322d3338312e6672222c5b2238222c223132225d2c5b223131222c223133225d2c5b2236222c223130222c223134225d2c5b2233222c223135225d2c5b2232222c223136225d2c5b2231222c223137225d2c5b223138225d2c5b2230222c223139225d5d5d">
module {
"protocol.module"() ({
"local.binding"() {sym_name="index",contract="index.constant",arguments=[],implementation=""} : ()->()
"local.binding"() {sym_name="constant",contract="field.constant",arguments=["bls12-381.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="length",contract="vector.length",arguments=["bls12-381.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="sum",contract="vector.sum",arguments=["bls12-381.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="multiply",contract="field.mul",arguments=["bls12-381.fr"],implementation=""} : ()->()
local.func @inspect(%mode:!mode) -> (ui64,!f,ui64) attributes {logical_origin=["inspect",[]]} {
 %result:3 = "local.match"(%mode) ({
   %n = "algebra.exec.index_constant"() {binding=@index,parameters=["0"],site="count_1"} : ()->ui64
   %x = "algebra.exec.field_constant"() {binding=@constant,parameters=["0"],site="value_2"} : ()->!f
   "local.yield"(%n,%x,%n) : (ui64,!f,ui64)->()
 }, { ^plain(%v:!v):
   %n = "algebra.exec.vector_length"(%v) {binding=@length,parameters=[],site="count_3"} : (!v)->ui64
   %x = "algebra.exec.vector_sum"(%v) {binding=@sum,parameters=[],site="value_4"} : (!v)->!f
   %tag = "algebra.exec.index_constant"() {binding=@index,parameters=["1"],site="tag_5"} : ()->ui64
   "local.yield"(%n,%x,%tag) : (ui64,!f,ui64)->()
 }, { ^scaled(%v:!v,%factor:!f):
   %n = "algebra.exec.vector_length"(%v) {binding=@length,parameters=[],site="count_6"} : (!v)->ui64
   %sum = "algebra.exec.vector_sum"(%v) {binding=@sum,parameters=[],site="sum_7"} : (!v)->!f
   %x = "algebra.exec.field_multiply"(%sum,%factor) {binding=@multiply,parameters=[],site="value_8"} : (!f,!f)->!f
   %tag = "algebra.exec.index_constant"() {binding=@index,parameters=["2"],site="tag_9"} : ()->ui64
   "local.yield"(%n,%x,%tag) : (ui64,!f,ui64)->()
 }) {alternatives=["none","plain","scaled"],site="mode_10"} : (!mode)->(ui64,!f,ui64)
 local.return %result#0,%result#1,%result#2 : ui64,!f,ui64
}

relation.declare @schnorr_relation {kind="external", key="example/schnorr", revision="1", signature=(!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> i1, purposes=["parameter", "statement", "witness"]}
"protocol.func"() ({
^entry(%g: !algebra.group<"bls12-381.g1">, %x: !algebra.field<"bls12-381.fr">, %y: !algebra.group<"bls12-381.g1">, %nonce: !protocol.service_ref<"random.bls12-381.fr/1">, %challenge_service: !protocol.service_ref<"random.bls12-381.fr/1">, %mode:!mode, %count:ui64, %expected:!f, %tag:ui64):
protocol.statement @schnorr_relation(%g, %y, %x) {selectors=["Bob","Bob","Alice"], acceptance=0 : i64} : !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">
%k = "protocol.query"(%nonce) {method="draw", owner="Alice", site="nonce"} : (!protocol.service_ref<"random.bls12-381.fr/1">) -> !algebra.field<"bls12-381.fr">
%r = algebra.group_scale %g, %k : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
%packet = "data.make"(%r,%mode) {alternative="record"} : (!algebra.group<"bls12-381.g1">,!mode)->!packet
%received = protocol.exchange %packet {site="commitment",sender="Alice",receiver="Bob"} : !packet
%commitment = "data.get"(%received) {index=0:i64} : (!packet)->!algebra.group<"bls12-381.g1">
%batch = "data.get"(%received) {index=1:i64} : (!packet)->!mode
%checked:3 = "protocol.local_call"(%batch) {callee=@inspect,role="Bob",site="batch"} : (!mode)->(ui64,!f,ui64)
%count_ok = "data.index_equal"(%checked#0,%count) : (ui64,ui64)->i1
%tag_ok = "data.index_equal"(%checked#2,%tag) : (ui64,ui64)->i1
%value_ok = algebra.field_equal %checked#1,%expected : (!f,!f)->i1
protocol.guard %count_ok {owner="Bob",site="count_check"}
protocol.guard %tag_ok {owner="Bob",site="tag_check"}
protocol.guard %value_ok {owner="Bob",site="value_check"}
%c = "protocol.query"(%challenge_service) {method="draw", owner="Bob", site="draw_challenge"} : (!protocol.service_ref<"random.bls12-381.fr/1">) -> !algebra.field<"bls12-381.fr">
%challenge = protocol.exchange %c {site="challenge",sender="Bob",receiver="Alice"} : !algebra.field<"bls12-381.fr">
%cx = algebra.field_multiply %challenge, %x : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
%z = algebra.field_add %k, %cx : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
%response = protocol.exchange %z {site="response",sender="Alice",receiver="Bob"} : !algebra.field<"bls12-381.fr">
%lhs = algebra.group_scale %g, %response : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
%cy = algebra.group_scale %y, %challenge : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
%rhs = algebra.group_add %commitment, %cy : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
%ok = algebra.group_equal %lhs, %rhs : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> i1
"protocol.return"(%ok) : (i1) -> ()
}) {sym_name="main", function_type=(!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">, !algebra.group<"bls12-381.g1">, !protocol.service_ref<"random.bls12-381.fr/1">, !protocol.service_ref<"random.bls12-381.fr/1">,!mode,ui64,!f,ui64) -> (i1), roles=["Alice", "Bob"], input_roles=[["Alice", "Bob"], ["Alice"], ["Alice", "Bob"], ["Alice"], ["Bob"],["Alice"],["Bob"],["Bob"],["Bob"]], output_roles=[["Bob"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> ()
}
