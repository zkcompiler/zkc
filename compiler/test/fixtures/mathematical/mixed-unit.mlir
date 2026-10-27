module { "protocol.module"() ({
"runtime.binding"() {sym_name="binding_make", contract="resource_unit.create", arguments=["Slot.A"], implementation=""} : () -> ()
"runtime.binding"() {sym_name="binding_consume", contract="resource_unit.consume", arguments=["Slot.A"], implementation=""} : () -> ()
    func.func @make(%arg0: !runtime.scope) -> !exec.outcome<(!runtime.capability<"resource_unit:Slot.A">)> attributes {no_inline, runtime.origin = ["make", []]} {
      %0 = "exec.apply"(%arg0) <{binding = @binding_make, parameters = [], site = "make"}> : (!runtime.scope) -> !exec.outcome<(!runtime.capability<"resource_unit:Slot.A">)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!runtime.capability<"resource_unit:Slot.A">)>) -> ()
    ^bb1(%1: !runtime.capability<"resource_unit:Slot.A">):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!runtime.capability<"resource_unit:Slot.A">) -> !exec.outcome<(!runtime.capability<"resource_unit:Slot.A">)>
      return %2 : !exec.outcome<(!runtime.capability<"resource_unit:Slot.A">)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!runtime.capability<"resource_unit:Slot.A">)>
      return %4 : !exec.outcome<(!runtime.capability<"resource_unit:Slot.A">)>
    }
    func.func @consume(%arg0: !runtime.scope, %arg1: !runtime.capability<"resource_unit:Slot.A">) -> !exec.outcome<> attributes {no_inline, runtime.origin = ["consume", []]} {
      %0 = "exec.apply"(%arg0, %arg1) <{binding = @binding_consume, parameters = [], site = "consume"}> : (!runtime.scope, !runtime.capability<"resource_unit:Slot.A">) -> !exec.outcome<>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<>) -> ()
    ^bb1:  // pred: ^bb0
      %1 = "exec.returned"() : () -> !exec.outcome<>
      return %1 : !exec.outcome<>
    ^bb2(%2: !exec.stop):  // pred: ^bb0
      %3 = "exec.failed"(%2) : (!exec.stop) -> !exec.outcome<>
      return %3 : !exec.outcome<>
    }



"protocol.func"() ({
^entry(%x: !algebra.field<"bls12-381.fr">, %reply: !algebra.field<"bls12-381.fr">, %go: i1):
%u = "protocol.local_call"() {callee=@make, role="P", site="make"} : () -> (!runtime.capability<"resource_unit:Slot.A">)
%sent = protocol.exchange %x {sender="P", receiver="V", site="send"} : !algebra.field<"bls12-381.fr">
%received = protocol.exchange %reply {sender="V", receiver="P", site="reply"} : !algebra.field<"bls12-381.fr">
protocol.guard %go {owner="P", site="after_receive"}
"protocol.local_call"(%u) {callee=@consume, role="P", site="consume"} : (!runtime.capability<"resource_unit:Slot.A">) -> ()
"protocol.return"(%received) : (!algebra.field<"bls12-381.fr">) -> ()
}) {sym_name="main", function_type=(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, i1) -> (!algebra.field<"bls12-381.fr">), roles=["P", "V"], input_roles=[["P"], ["V"], ["P"]], output_roles=[["P"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () }
