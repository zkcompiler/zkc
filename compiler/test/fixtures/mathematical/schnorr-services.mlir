module {
"protocol.module"() ({
relation.declare @schnorr_relation {kind="external", key="example/schnorr", revision="0", signature=(!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> i1, purposes=["parameter", "statement", "witness"]}
"protocol.func"() ({
^entry(%g: !algebra.group<"bls12-381.g1">, %x: !algebra.field<"bls12-381.fr">, %y: !algebra.group<"bls12-381.g1">, %nonce: !protocol.service_ref<"random.bls12-381.fr/0">, %challenge_service: !protocol.service_ref<"random.bls12-381.fr/0">):
protocol.statement @schnorr_relation(%g, %y, %x) {selectors=["Bob","Bob","Alice"], acceptance=0 : i64} : !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">
%k = "protocol.query"(%nonce) {method="draw", owner="Alice", site="nonce"} : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
%r = algebra.group_scale %g, %k : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
%commitment = protocol.exchange %r {site="commitment",sender="Alice",receiver="Bob"} : !algebra.group<"bls12-381.g1">
%c = "protocol.query"(%challenge_service) {method="draw", owner="Bob", site="draw_challenge"} : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
%challenge = protocol.exchange %c {site="challenge",sender="Bob",receiver="Alice"} : !algebra.field<"bls12-381.fr">
%cx = algebra.field_multiply %challenge, %x : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
%z = algebra.field_add %k, %cx : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
%response = protocol.exchange %z {site="response",sender="Alice",receiver="Bob"} : !algebra.field<"bls12-381.fr">
%lhs = algebra.group_scale %g, %response : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
%cy = algebra.group_scale %y, %challenge : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
%rhs = algebra.group_add %commitment, %cy : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
%ok = algebra.group_equal %lhs, %rhs : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> i1
"protocol.return"(%ok) : (i1) -> ()
}) {sym_name="main", function_type=(!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">, !algebra.group<"bls12-381.g1">, !protocol.service_ref<"random.bls12-381.fr/0">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (i1), roles=["Alice", "Bob"], input_roles=[["Alice", "Bob"], ["Alice"], ["Alice", "Bob"], ["Alice"], ["Bob"]], output_roles=[["Bob"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> ()
}
