module { "protocol.module"() ({
"local.binding"() {sym_name="binding_make", contract="resource_unit.create", arguments=["Slot.A"], implementation=""} : () -> ()
"local.binding"() {sym_name="binding_consume", contract="resource_unit.consume", arguments=["Slot.A"], implementation=""} : () -> ()
local.func @make() -> (!local.capability<"resource_unit:Slot.A">) attributes {logical_origin=["make", []]} {
%u = "local.exec.resource_unit_create"() {binding=@binding_make, parameters=[], site="make"} : () -> !local.capability<"resource_unit:Slot.A">
local.return %u : !local.capability<"resource_unit:Slot.A">
}
local.func @consume(%u: !local.capability<"resource_unit:Slot.A">) -> () attributes {logical_origin=["consume", []]} {
"local.exec.resource_unit_consume"(%u) {binding=@binding_consume, parameters=[], site="consume"} : (!local.capability<"resource_unit:Slot.A">) -> ()
local.return
}

"protocol.func"() ({
^entry(%x: !algebra.field<"bls12-381.fr">, %reply: !algebra.field<"bls12-381.fr">, %go: i1):
%u = "protocol.local_call"() {callee=@make, role="P", site="make"} : () -> (!local.capability<"resource_unit:Slot.A">)
%sent = protocol.exchange %x {sender="P", receiver="V", site="send"} : !algebra.field<"bls12-381.fr">
%received = protocol.exchange %reply {sender="V", receiver="P", site="reply"} : !algebra.field<"bls12-381.fr">
protocol.guard %go {owner="P", site="after_receive"}
"protocol.local_call"(%u) {callee=@consume, role="P", site="consume"} : (!local.capability<"resource_unit:Slot.A">) -> ()
"protocol.return"(%received) : (!algebra.field<"bls12-381.fr">) -> ()
}) {sym_name="main", function_type=(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, i1) -> (!algebra.field<"bls12-381.fr">), roles=["P", "V"], input_roles=[["P"], ["V"], ["P"]], output_roles=[["P"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () }
