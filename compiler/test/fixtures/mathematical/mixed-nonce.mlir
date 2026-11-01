module { "protocol.module"() ({
"runtime.binding"() {sym_name="binding_commit", contract="curve.commit", arguments=["bls12-381.g1"], implementation="",function_type=(!runtime.scope, !data.group_vector<"bls12-381.g1">, !runtime.capability<nonce, "bls12-381.fr">) -> !exec.outcome<(!data.group_vector<"bls12-381.g1">, !runtime.capability<nonce, "bls12-381.fr">)>} : () -> ()
"runtime.binding"() {sym_name="binding_respond", contract="curve.response", arguments=["bls12-381.fr"], implementation="",function_type=(!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !runtime.capability<nonce, "bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>} : () -> ()
    func.func @commit(%arg0: !runtime.scope, %arg1: !data.group_vector<"bls12-381.g1">, %arg2: !runtime.capability<nonce, "bls12-381.fr">) -> !exec.outcome<(!data.group_vector<"bls12-381.g1">, !runtime.capability<nonce, "bls12-381.fr">)> attributes {no_inline, runtime.origin = ["commit", []]} {
      %0 = "exec.apply"(%arg0, %arg1, %arg2) <{binding = @binding_commit, parameters = [], site = "commit"}> : (!runtime.scope, !data.group_vector<"bls12-381.g1">, !runtime.capability<nonce, "bls12-381.fr">) -> !exec.outcome<(!data.group_vector<"bls12-381.g1">, !runtime.capability<nonce, "bls12-381.fr">)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!data.group_vector<"bls12-381.g1">, !runtime.capability<nonce, "bls12-381.fr">)>) -> ()
    ^bb1(%1: !data.group_vector<"bls12-381.g1">, %2: !runtime.capability<nonce, "bls12-381.fr">):  // pred: ^bb0
      %3 = "exec.returned"(%1, %2) : (!data.group_vector<"bls12-381.g1">, !runtime.capability<nonce, "bls12-381.fr">) -> !exec.outcome<(!data.group_vector<"bls12-381.g1">, !runtime.capability<nonce, "bls12-381.fr">)>
      return %3 : !exec.outcome<(!data.group_vector<"bls12-381.g1">, !runtime.capability<nonce, "bls12-381.fr">)>
    ^bb2(%4: !exec.stop):  // pred: ^bb0
      %5 = "exec.failed"(%4) : (!exec.stop) -> !exec.outcome<(!data.group_vector<"bls12-381.g1">, !runtime.capability<nonce, "bls12-381.fr">)>
      return %5 : !exec.outcome<(!data.group_vector<"bls12-381.g1">, !runtime.capability<nonce, "bls12-381.fr">)>
    }
    func.func @respond(%arg0: !runtime.scope, %arg1: !algebra.field<"bls12-381.fr">, %arg2: !algebra.field<"bls12-381.fr">, %arg3: !runtime.capability<nonce, "bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)> attributes {no_inline, runtime.origin = ["respond", []]} {
      %0 = "exec.apply"(%arg0, %arg1, %arg2, %arg3) <{binding = @binding_respond, parameters = [], site = "respond"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !runtime.capability<nonce, "bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%1: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      return %2 : !exec.outcome<(!algebra.field<"bls12-381.fr">)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      return %4 : !exec.outcome<(!algebra.field<"bls12-381.fr">)>
    }



"protocol.func"() ({
^entry(%bases: !data.group_vector<"bls12-381.g1">, %nonce: !runtime.capability<nonce, "bls12-381.fr">, %secret: !algebra.field<"bls12-381.fr">, %challenge: !algebra.field<"bls12-381.fr">, %go: i1):
%ready:2 = "protocol.local_call"(%bases, %nonce) {callee=@commit, role="P", site="commit"} : (!data.group_vector<"bls12-381.g1">, !runtime.capability<nonce, "bls12-381.fr">) -> (!data.group_vector<"bls12-381.g1">, !runtime.capability<nonce, "bls12-381.fr">)
%sent = protocol.exchange %ready#0 {sender="P", receiver="V", site="commitments"} : !data.group_vector<"bls12-381.g1">
%received = protocol.exchange %challenge {sender="V", receiver="P", site="challenge"} : !algebra.field<"bls12-381.fr">
protocol.guard %go {owner="P", site="after_receive"}
%response = "protocol.local_call"(%secret, %received, %ready#1) {callee=@respond, role="P", site="respond"} : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !runtime.capability<nonce, "bls12-381.fr">) -> (!algebra.field<"bls12-381.fr">)
"protocol.return"(%response) : (!algebra.field<"bls12-381.fr">) -> ()
}) {sym_name="main", function_type=(!data.group_vector<"bls12-381.g1">, !runtime.capability<nonce, "bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, i1) -> (!algebra.field<"bls12-381.fr">), roles=["P", "V"], input_roles=[["P"], ["P"], ["P"], ["V"], ["P"]], output_roles=[["P"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () }
