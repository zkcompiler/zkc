module { "protocol.module"() ({
"local.binding"() {sym_name="binding_commit", contract="curve.commit", arguments=["bls12-381.g1"], implementation=""} : () -> ()
"local.binding"() {sym_name="binding_respond", contract="curve.response", arguments=["bls12-381.fr"], implementation=""} : () -> ()
local.func @commit(%bases: tensor<?x!algebra.group<"bls12-381.g1">>, %nonce: !local.capability<"nonce:bls12-381.fr">) -> (tensor<?x!algebra.group<"bls12-381.g1">>, !local.capability<"nonce:bls12-381.fr">) attributes {logical_origin=["commit", []]} {
%v:2 = "crypto.exec.curve_commit"(%bases, %nonce) {binding=@binding_commit, parameters=[], site="commit"} : (tensor<?x!algebra.group<"bls12-381.g1">>, !local.capability<"nonce:bls12-381.fr">) -> (tensor<?x!algebra.group<"bls12-381.g1">>, !local.capability<"nonce:bls12-381.fr">)
local.return %v#0, %v#1 : tensor<?x!algebra.group<"bls12-381.g1">>, !local.capability<"nonce:bls12-381.fr">
}
local.func @respond(%secret: !algebra.field<"bls12-381.fr">, %challenge: !algebra.field<"bls12-381.fr">, %nonce: !local.capability<"nonce:bls12-381.fr">) -> (!algebra.field<"bls12-381.fr">) attributes {logical_origin=["respond", []]} {
%v = "crypto.exec.curve_response"(%secret, %challenge, %nonce) {binding=@binding_respond, parameters=[], site="respond"} : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !local.capability<"nonce:bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
local.return %v : !algebra.field<"bls12-381.fr">
}

"protocol.func"() ({
^entry(%bases: tensor<?x!algebra.group<"bls12-381.g1">>, %nonce: !local.capability<"nonce:bls12-381.fr">, %secret: !algebra.field<"bls12-381.fr">, %challenge: !algebra.field<"bls12-381.fr">, %go: i1):
%ready:2 = "protocol.local_call"(%bases, %nonce) {callee=@commit, role="P", site="commit"} : (tensor<?x!algebra.group<"bls12-381.g1">>, !local.capability<"nonce:bls12-381.fr">) -> (tensor<?x!algebra.group<"bls12-381.g1">>, !local.capability<"nonce:bls12-381.fr">)
%sent = protocol.exchange %ready#0 {sender="P", receiver="V", site="commitments"} : tensor<?x!algebra.group<"bls12-381.g1">>
%received = protocol.exchange %challenge {sender="V", receiver="P", site="challenge"} : !algebra.field<"bls12-381.fr">
protocol.guard %go {owner="P", site="after_receive"}
%response = "protocol.local_call"(%secret, %received, %ready#1) {callee=@respond, role="P", site="respond"} : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !local.capability<"nonce:bls12-381.fr">) -> (!algebra.field<"bls12-381.fr">)
"protocol.return"(%response) : (!algebra.field<"bls12-381.fr">) -> ()
}) {sym_name="main", function_type=(tensor<?x!algebra.group<"bls12-381.g1">>, !local.capability<"nonce:bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, i1) -> (!algebra.field<"bls12-381.fr">), roles=["P", "V"], input_roles=[["P"], ["P"], ["P"], ["V"], ["P"]], output_roles=[["P"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () }
