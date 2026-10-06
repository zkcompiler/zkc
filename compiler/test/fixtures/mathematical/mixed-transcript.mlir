module { "protocol.module"() ({
"local.binding"() {sym_name="binding_draw", contract="transcript.challenge", arguments=["merlin3.bls12-381.fr64be/1"], implementation=""} : () -> ()
local.func @draw(%state: !local.capability<"transcript:merlin3.bls12-381.fr64be/1">) -> (!algebra.field<"bls12-381.fr">, !local.capability<"transcript:merlin3.bls12-381.fr64be/1">) attributes {logical_origin=["draw", []]} {
%v:2 = "crypto.exec.transcript_challenge"(%state) {binding=@binding_draw, parameters=["Round", "challenge", "Challenge", "draw", "P"], site="draw"} : (!local.capability<"transcript:merlin3.bls12-381.fr64be/1">) -> (!algebra.field<"bls12-381.fr">, !local.capability<"transcript:merlin3.bls12-381.fr64be/1">)
local.return %v#0, %v#1 : !algebra.field<"bls12-381.fr">, !local.capability<"transcript:merlin3.bls12-381.fr64be/1">
}

"protocol.func"() ({
^entry(%state: !local.capability<"transcript:merlin3.bls12-381.fr64be/1">, %x: !algebra.field<"bls12-381.fr">, %reply: !algebra.field<"bls12-381.fr">, %go: i1):
%sent = protocol.exchange %x {sender="P", receiver="V", site="send"} : !algebra.field<"bls12-381.fr">
%received = protocol.exchange %reply {sender="V", receiver="P", site="reply"} : !algebra.field<"bls12-381.fr">
protocol.guard %go {owner="P", site="after_receive"}
%draw:2 = "protocol.local_call"(%state) {callee=@draw, role="P", site="draw"} : (!local.capability<"transcript:merlin3.bls12-381.fr64be/1">) -> (!algebra.field<"bls12-381.fr">, !local.capability<"transcript:merlin3.bls12-381.fr64be/1">)
%sum = algebra.field_add %received, %draw#0 : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
"protocol.return"(%sum, %draw#1) : (!algebra.field<"bls12-381.fr">, !local.capability<"transcript:merlin3.bls12-381.fr64be/1">) -> ()
}) {sym_name="main", function_type=(!local.capability<"transcript:merlin3.bls12-381.fr64be/1">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, i1) -> (!algebra.field<"bls12-381.fr">, !local.capability<"transcript:merlin3.bls12-381.fr64be/1">), roles=["P", "V"], input_roles=[["P"], ["P"], ["V"], ["P"]], output_roles=[["P"], ["P"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () }
