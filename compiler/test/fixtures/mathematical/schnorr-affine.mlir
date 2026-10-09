module {
"protocol.module"() ({
"local.binding"() {sym_name="empty", contract="curve.empty", arguments=["bls12-381.g1"], implementation=""} : () -> ()
"local.binding"() {sym_name="append", contract="curve.append", arguments=["bls12-381.g1"], implementation=""} : () -> ()
"local.binding"() {sym_name="at", contract="curve.at", arguments=["bls12-381.g1"], implementation=""} : () -> ()
"local.binding"() {sym_name="commit", contract="curve.commit", arguments=["bls12-381.g1"], implementation=""} : () -> ()
"local.binding"() {sym_name="respond", contract="curve.response", arguments=["bls12-381.fr"], implementation=""} : () -> ()
local.func @nonce_commit(%g: !algebra.group<"bls12-381.g1">, %nonce: !local.capability<"nonce:bls12-381.fr">) -> (!algebra.group<"bls12-381.g1">, !local.capability<"nonce:bls12-381.fr">) attributes {logical_origin=["nonce_commit", []]} {
%empty = "algebra.exec.group_empty"() {binding=@empty, parameters=[], site="empty"} : () -> tensor<?x!algebra.group<"bls12-381.g1">>
%bases = "algebra.exec.group_append"(%empty, %g) {binding=@append, parameters=[], site="append"} : (tensor<?x!algebra.group<"bls12-381.g1">>, !algebra.group<"bls12-381.g1">) -> tensor<?x!algebra.group<"bls12-381.g1">>
%ready:2 = "crypto.exec.curve_commit"(%bases, %nonce) {binding=@commit, parameters=[], site="commit"} : (tensor<?x!algebra.group<"bls12-381.g1">>, !local.capability<"nonce:bls12-381.fr">) -> (tensor<?x!algebra.group<"bls12-381.g1">>, !local.capability<"nonce:bls12-381.fr">)
%r = "algebra.exec.group_at"(%ready#0) {binding=@at, parameters=["0"], site="at"} : (tensor<?x!algebra.group<"bls12-381.g1">>) -> !algebra.group<"bls12-381.g1">
local.return %r, %ready#1 : !algebra.group<"bls12-381.g1">, !local.capability<"nonce:bls12-381.fr">
}
local.func @nonce_respond(%x: !algebra.field<"bls12-381.fr">, %c: !algebra.field<"bls12-381.fr">, %nonce: !local.capability<"nonce:bls12-381.fr">) -> !algebra.field<"bls12-381.fr"> attributes {logical_origin=["nonce_respond", []]} {
%z = "crypto.exec.curve_response"(%x, %c, %nonce) {binding=@respond, parameters=[], site="respond"} : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !local.capability<"nonce:bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
local.return %z : !algebra.field<"bls12-381.fr">
}
relation.declare @schnorr_relation {kind="external", key="example/schnorr", revision="0", signature=(!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> i1, purposes=["parameter", "statement", "witness"]}
"protocol.func"() ({
^entry(%g: !algebra.group<"bls12-381.g1">, %x: !algebra.field<"bls12-381.fr">, %y: !algebra.group<"bls12-381.g1">, %nonce: !local.capability<"nonce:bls12-381.fr">, %challenge_service: !protocol.service_ref<"random.bls12-381.fr/0">):
protocol.statement @schnorr_relation(%g, %y, %x) {selectors=["Bob","Bob","Alice"], acceptance=0 : i64} : !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">
%ready:2 = "protocol.local_call"(%g, %nonce) {callee=@nonce_commit, role="Alice", site="nonce"} : (!algebra.group<"bls12-381.g1">, !local.capability<"nonce:bls12-381.fr">) -> (!algebra.group<"bls12-381.g1">, !local.capability<"nonce:bls12-381.fr">)
%commitment = protocol.exchange %ready#0 {site="commitment",sender="Alice",receiver="Bob"} : !algebra.group<"bls12-381.g1">
%c = "protocol.query"(%challenge_service) {method="draw", owner="Bob", site="draw_challenge"} : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
%challenge = protocol.exchange %c {site="challenge",sender="Bob",receiver="Alice"} : !algebra.field<"bls12-381.fr">
%z = "protocol.local_call"(%x, %challenge, %ready#1) {callee=@nonce_respond, role="Alice", site="respond"} : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !local.capability<"nonce:bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
%response = protocol.exchange %z {site="response",sender="Alice",receiver="Bob"} : !algebra.field<"bls12-381.fr">
%lhs = algebra.group_scale %g, %response : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
%cy = algebra.group_scale %y, %challenge : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
%rhs = algebra.group_add %commitment, %cy : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
%ok = algebra.group_equal %lhs, %rhs : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> i1
"protocol.return"(%ok) : (i1) -> ()
}) {sym_name="main", function_type=(!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">, !algebra.group<"bls12-381.g1">, !local.capability<"nonce:bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (i1), roles=["Alice", "Bob"], input_roles=[["Alice", "Bob"], ["Alice"], ["Alice", "Bob"], ["Alice"], ["Bob"]], output_roles=[["Bob"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> ()
}
