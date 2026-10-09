module {
"protocol.module"() ({
relation.declare @schnorr_relation {kind="external", key="example/schnorr", revision="0", signature=(!algebra.group<"ristretto255.group">, !algebra.group<"ristretto255.group">, !algebra.field<"ristretto255.scalar">) -> i1, purposes=["parameter", "statement", "witness"]}
"protocol.func"() ({
^entry(%g: !algebra.group<"ristretto255.group">, %x: !algebra.field<"ristretto255.scalar">, %y: !algebra.group<"ristretto255.group">, %nonce: !protocol.service_ref<"random.ristretto255.scalar/0">, %challenge_service: !protocol.service_ref<"random.ristretto255.scalar/0">):
protocol.statement @schnorr_relation(%g, %y, %x) {selectors=["Bob","Bob","Alice"], acceptance=0 : i64} : !algebra.group<"ristretto255.group">, !algebra.group<"ristretto255.group">, !algebra.field<"ristretto255.scalar">
%k = "protocol.query"(%nonce) {method="draw", owner="Alice", site="nonce"} : (!protocol.service_ref<"random.ristretto255.scalar/0">) -> !algebra.field<"ristretto255.scalar">
%r = algebra.group_scale %g, %k : (!algebra.group<"ristretto255.group">, !algebra.field<"ristretto255.scalar">) -> !algebra.group<"ristretto255.group">
%commitment = protocol.exchange %r {site="commitment",sender="Alice",receiver="Bob"} : !algebra.group<"ristretto255.group">
%c = "protocol.query"(%challenge_service) {method="draw", owner="Bob", site="draw_challenge"} : (!protocol.service_ref<"random.ristretto255.scalar/0">) -> !algebra.field<"ristretto255.scalar">
%challenge = protocol.exchange %c {site="challenge",sender="Bob",receiver="Alice"} : !algebra.field<"ristretto255.scalar">
%cx = algebra.field_multiply %challenge, %x : (!algebra.field<"ristretto255.scalar">, !algebra.field<"ristretto255.scalar">) -> !algebra.field<"ristretto255.scalar">
%z = algebra.field_add %k, %cx : (!algebra.field<"ristretto255.scalar">, !algebra.field<"ristretto255.scalar">) -> !algebra.field<"ristretto255.scalar">
%response = protocol.exchange %z {site="response",sender="Alice",receiver="Bob"} : !algebra.field<"ristretto255.scalar">
%lhs = algebra.group_scale %g, %response : (!algebra.group<"ristretto255.group">, !algebra.field<"ristretto255.scalar">) -> !algebra.group<"ristretto255.group">
%cy = algebra.group_scale %y, %challenge : (!algebra.group<"ristretto255.group">, !algebra.field<"ristretto255.scalar">) -> !algebra.group<"ristretto255.group">
%rhs = algebra.group_add %commitment, %cy : (!algebra.group<"ristretto255.group">, !algebra.group<"ristretto255.group">) -> !algebra.group<"ristretto255.group">
%ok = algebra.group_equal %lhs, %rhs : (!algebra.group<"ristretto255.group">, !algebra.group<"ristretto255.group">) -> i1
"protocol.return"(%ok) : (i1) -> ()
}) {sym_name="main", function_type=(!algebra.group<"ristretto255.group">, !algebra.field<"ristretto255.scalar">, !algebra.group<"ristretto255.group">, !protocol.service_ref<"random.ristretto255.scalar/0">, !protocol.service_ref<"random.ristretto255.scalar/0">) -> (i1), roles=["Alice", "Bob"], input_roles=[["Alice", "Bob"], ["Alice"], ["Alice", "Bob"], ["Alice"], ["Bob"]], output_roles=[["Bob"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> ()
}
