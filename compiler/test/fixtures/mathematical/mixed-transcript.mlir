module { "protocol.module"() ({
 "local.binding"() {sym_name="coordinates",contract="indices.empty",arguments=[],implementation=""} : ()->()
"local.binding"() {sym_name="binding_draw", contract="transcript.native.indexed.challenge", arguments=["merlin3.bls12-381.fr64be/1"], implementation=""} : () -> ()
local.func @draw(%state: !local.capability<"transcript:merlin3.bls12-381.fr64be/1">) -> (!algebra.field<"bls12-381.fr">, !local.capability<"transcript:merlin3.bls12-381.fr64be/1">) attributes {logical_origin=["draw", []]} {
%coordinates = "algebra.exec.indices_empty"() {binding=@coordinates,parameters=[],site="coordinates"} : ()->tensor<?xui64>
%v:2 = "crypto.exec.indexed_transcript_challenge"(%state,%coordinates) {binding=@binding_draw, parameters=["010500000000000000001a000000000000007a6b632e6e61746976652d6f726967696e2d74656d706c6174650004000000000000006d61696e0100000000000000000100000000000000000107000000000000000005000000000000007175657279000500000000000000526f756e6400040000000000000064726177000700000000000000696e7075745f3000150000000000000072616e646f6d2e626c7331322d3338312e66722f310004000000000000006472617700010000000000000050"], site="draw"} : (!local.capability<"transcript:merlin3.bls12-381.fr64be/1">,tensor<?xui64>) -> (!algebra.field<"bls12-381.fr">, !local.capability<"transcript:merlin3.bls12-381.fr64be/1">)
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
