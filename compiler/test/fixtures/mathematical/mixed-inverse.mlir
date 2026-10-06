module { "protocol.module"() ({
"local.binding"() {sym_name="binding_inverse", contract="field.inverse", arguments=["bls12-381.fr"], implementation=""} : () -> ()
local.func @inverse(%x: !algebra.field<"bls12-381.fr">) -> (!algebra.field<"bls12-381.fr">) attributes {logical_origin=["inverse", []]} {
%v = "algebra.exec.field_inverse"(%x) {binding=@binding_inverse, parameters=[], site="inverse"} : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
local.return %v : !algebra.field<"bls12-381.fr">
}

"protocol.func"() ({
^entry(%x: !algebra.field<"bls12-381.fr">, %reply: !algebra.field<"bls12-381.fr">, %go: i1):
%sent = protocol.exchange %x {sender="P", receiver="V", site="send"} : !algebra.field<"bls12-381.fr">
%received = protocol.exchange %reply {sender="V", receiver="P", site="reply"} : !algebra.field<"bls12-381.fr">
protocol.guard %go {owner="P", site="after_receive"}
%inverse = "protocol.local_call"(%received) {callee=@inverse, role="P", site="inverse"} : (!algebra.field<"bls12-381.fr">) -> (!algebra.field<"bls12-381.fr">)
%product = algebra.field_multiply %received, %inverse : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
"protocol.return"(%product) : (!algebra.field<"bls12-381.fr">) -> ()
}) {sym_name="main", function_type=(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, i1) -> (!algebra.field<"bls12-381.fr">), roles=["P", "V"], input_roles=[["P"], ["V"], ["P"]], output_roles=[["P"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () }
