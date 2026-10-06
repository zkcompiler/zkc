!s = !local.capability<"rng:bls12-381.fr">
!u = !local.capability<"resource_unit:Slot.A">
module { "protocol.module"() ({
 "local.binding"() {sym_name="create",contract="resource_unit.create",arguments=["Slot.A"],implementation=""} : ()->()
 local.func @never() attributes {logical_origin=["never",[]]} {
  "local.stop"() {site="halt",reason="abort"} : ()->()
 }
 local.func @halt()->!u attributes {logical_origin=["halt",[]]} {
  local.apply @never() {site="never"} : ()->()
  %new = "local.exec.resource_unit_create"() {binding=@create,parameters=[],site="new"} : ()->!u
  local.return %new : !u
 }
 local.func @swap(%a:!s,%b:!s)->(!s,!s) attributes {logical_origin=["swap",[]]} {
  local.return %b,%a : !s,!s
 }

 "protocol.func"() ({ ^entry(%n:ui64,%x:!s,%y:!s):
 %done:2 = "protocol.repeat"(%n,%x,%y) ({ ^round(%i:ui64,%a:!s,%b:!s):

  %stopped = "protocol.local_call"() {callee=@halt,role="A",site="stop_A"} : ()->!u
  %out:2 = "protocol.local_call"(%a,%b) {callee=@swap,role="B",site="swap_B"} : (!s,!s)->(!s,!s)

 "protocol.yield"(%out#0,%out#1) : (!s,!s)->()
 }) {site="rounds",carried=2:i64,maximum=8:i64,roles=["A","B"],carried_roles=[["B"],["B"]]} : (ui64,!s,!s)->(!s,!s)
 "protocol.return"(%done#0,%done#1) : (!s,!s)->()
 }) {sym_name="main",function_type=(ui64,!s,!s)->(!s,!s),roles=["A","B"],input_roles=[["A","B"],["B"],["B"]],output_roles=[["B"],["B"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
