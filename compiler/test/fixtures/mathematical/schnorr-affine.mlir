module {
"protocol.module"() ({
"runtime.binding"() {sym_name="empty", contract="curve.empty", arguments=["bls12-381.g1"], implementation=""} : () -> ()
"runtime.binding"() {sym_name="append", contract="curve.append", arguments=["bls12-381.g1"], implementation=""} : () -> ()
"runtime.binding"() {sym_name="at", contract="curve.at", arguments=["bls12-381.g1"], implementation=""} : () -> ()
"runtime.binding"() {sym_name="commit", contract="curve.commit", arguments=["bls12-381.g1"], implementation=""} : () -> ()
"runtime.binding"() {sym_name="respond", contract="curve.response", arguments=["bls12-381.fr"], implementation=""} : () -> ()
    func.func @nonce_commit(%arg0: !runtime.scope, %arg1: !algebra.group<"bls12-381.g1">, %arg2: !runtime.capability<"nonce:bls12-381.fr">) -> !exec.outcome<(!algebra.group<"bls12-381.g1">, !runtime.capability<"nonce:bls12-381.fr">)> attributes {no_inline, runtime.origin = ["nonce_commit", []]} {
      %0 = "exec.apply"(%arg0) <{binding = @empty, parameters = [], site = "empty"}> : (!runtime.scope) -> !exec.outcome<(!algebra.group_vector<"bls12-381.g1">)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!algebra.group_vector<"bls12-381.g1">)>) -> ()
    ^bb1(%1: !algebra.group_vector<"bls12-381.g1">):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %1, %arg1) <{binding = @append, parameters = [], site = "append"}> : (!runtime.scope, !algebra.group_vector<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> !exec.outcome<(!algebra.group_vector<"bls12-381.g1">)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(!algebra.group_vector<"bls12-381.g1">)>) -> ()
    ^bb2(%3: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!algebra.group<"bls12-381.g1">, !runtime.capability<"nonce:bls12-381.fr">)>
      return %4 : !exec.outcome<(!algebra.group<"bls12-381.g1">, !runtime.capability<"nonce:bls12-381.fr">)>
    ^bb3(%5: !algebra.group_vector<"bls12-381.g1">):  // pred: ^bb1
      %6 = "exec.apply"(%arg0, %5, %arg2) <{binding = @commit, parameters = [], site = "commit"}> : (!runtime.scope, !algebra.group_vector<"bls12-381.g1">, !runtime.capability<"nonce:bls12-381.fr">) -> !exec.outcome<(!algebra.group_vector<"bls12-381.g1">, !runtime.capability<"nonce:bls12-381.fr">)>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<(!algebra.group_vector<"bls12-381.g1">, !runtime.capability<"nonce:bls12-381.fr">)>) -> ()
    ^bb4(%7: !algebra.group_vector<"bls12-381.g1">, %8: !runtime.capability<"nonce:bls12-381.fr">):  // pred: ^bb3
      %9 = "exec.apply"(%arg0, %7) <{binding = @at, parameters = ["0"], site = "at"}> : (!runtime.scope, !algebra.group_vector<"bls12-381.g1">) -> !exec.outcome<(!algebra.group<"bls12-381.g1">)>
      "exec.dispatch"(%9)[^bb5, ^bb2] : (!exec.outcome<(!algebra.group<"bls12-381.g1">)>) -> ()
    ^bb5(%10: !algebra.group<"bls12-381.g1">):  // pred: ^bb4
      %11 = "exec.returned"(%10, %8) : (!algebra.group<"bls12-381.g1">, !runtime.capability<"nonce:bls12-381.fr">) -> !exec.outcome<(!algebra.group<"bls12-381.g1">, !runtime.capability<"nonce:bls12-381.fr">)>
      return %11 : !exec.outcome<(!algebra.group<"bls12-381.g1">, !runtime.capability<"nonce:bls12-381.fr">)>
    }
    func.func @nonce_respond(%arg0: !runtime.scope, %arg1: !algebra.field<"bls12-381.fr">, %arg2: !algebra.field<"bls12-381.fr">, %arg3: !runtime.capability<"nonce:bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)> attributes {no_inline, runtime.origin = ["nonce_respond", []]} {
      %0 = "exec.apply"(%arg0, %arg1, %arg2, %arg3) <{binding = @respond, parameters = [], site = "respond"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !runtime.capability<"nonce:bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%1: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      return %2 : !exec.outcome<(!algebra.field<"bls12-381.fr">)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      return %4 : !exec.outcome<(!algebra.field<"bls12-381.fr">)>
    }


relation.declare @schnorr_relation {kind="external", key="example/schnorr", revision="0", signature=(!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> i1, purposes=["parameter", "statement", "witness"]}
"protocol.func"() ({
^entry(%g: !algebra.group<"bls12-381.g1">, %x: !algebra.field<"bls12-381.fr">, %y: !algebra.group<"bls12-381.g1">, %nonce: !runtime.capability<"nonce:bls12-381.fr">, %challenge_service: !protocol.service_ref<"random.bls12-381.fr/0">):
protocol.statement @schnorr_relation(%g, %y, %x) {selectors=["Bob","Bob","Alice"], acceptance=0 : i64} : !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">
%ready:2 = "protocol.local_call"(%g, %nonce) {callee=@nonce_commit, role="Alice", site="nonce"} : (!algebra.group<"bls12-381.g1">, !runtime.capability<"nonce:bls12-381.fr">) -> (!algebra.group<"bls12-381.g1">, !runtime.capability<"nonce:bls12-381.fr">)
%commitment = protocol.exchange %ready#0 {site="commitment",sender="Alice",receiver="Bob"} : !algebra.group<"bls12-381.g1">
%c = "protocol.query"(%challenge_service) {method="draw", owner="Bob", site="draw_challenge"} : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
%challenge = protocol.exchange %c {site="challenge",sender="Bob",receiver="Alice"} : !algebra.field<"bls12-381.fr">
%z = "protocol.local_call"(%x, %challenge, %ready#1) {callee=@nonce_respond, role="Alice", site="respond"} : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !runtime.capability<"nonce:bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
%response = protocol.exchange %z {site="response",sender="Alice",receiver="Bob"} : !algebra.field<"bls12-381.fr">
%lhs = algebra.group_scale %g, %response : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
%cy = algebra.group_scale %y, %challenge : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
%rhs = algebra.group_add %commitment, %cy : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
%ok = algebra.group_equal %lhs, %rhs : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> i1
"protocol.return"(%ok) : (i1) -> ()
}) {sym_name="main", function_type=(!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">, !algebra.group<"bls12-381.g1">, !runtime.capability<"nonce:bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (i1), roles=["Alice", "Bob"], input_roles=[["Alice", "Bob"], ["Alice"], ["Alice", "Bob"], ["Alice"], ["Bob"]], output_roles=[["Bob"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> ()
}
