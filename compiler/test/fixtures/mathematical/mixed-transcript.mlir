module { "protocol.module"() ({
 "runtime.binding"() {sym_name="coordinates",contract="indices.empty",arguments=[],implementation="",function_type=(!runtime.scope) -> !exec.outcome<(!algebra.indices)>} : ()->()
"runtime.binding"() {sym_name="binding_draw", contract="transcript.native.indexed.challenge", arguments=["merlin3.bls12-381.fr64be/0"], implementation="",function_type=(!runtime.scope, !runtime.capability<transcript, "merlin3.bls12-381.fr64be/0">, !algebra.indices) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !runtime.capability<transcript, "merlin3.bls12-381.fr64be/0">)>} : () -> ()
    func.func @draw(%arg0: !runtime.scope, %arg1: !runtime.capability<transcript, "merlin3.bls12-381.fr64be/0">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !runtime.capability<transcript, "merlin3.bls12-381.fr64be/0">)> attributes {no_inline, runtime.origin = ["draw", []]} {
      %0 = "exec.apply"(%arg0) <{binding = @coordinates, parameters = [], site = "coordinates"}> : (!runtime.scope) -> !exec.outcome<(!algebra.indices)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!algebra.indices)>) -> ()
    ^bb1(%1: !algebra.indices):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %arg1, %1) <{binding = @binding_draw, parameters = [#runtime.origin<"main", #runtime.query_origin<"Round", "draw", 0, "random.bls12-381.fr/0", "draw", "P">>], site = "draw"}> : (!runtime.scope, !runtime.capability<transcript, "merlin3.bls12-381.fr64be/0">, !algebra.indices) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !runtime.capability<transcript, "merlin3.bls12-381.fr64be/0">)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">, !runtime.capability<transcript, "merlin3.bls12-381.fr64be/0">)>) -> ()
    ^bb2(%3: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !runtime.capability<transcript, "merlin3.bls12-381.fr64be/0">)>
      return %4 : !exec.outcome<(!algebra.field<"bls12-381.fr">, !runtime.capability<transcript, "merlin3.bls12-381.fr64be/0">)>
    ^bb3(%5: !algebra.field<"bls12-381.fr">, %6: !runtime.capability<transcript, "merlin3.bls12-381.fr64be/0">):  // pred: ^bb1
      %7 = "exec.returned"(%5, %6) : (!algebra.field<"bls12-381.fr">, !runtime.capability<transcript, "merlin3.bls12-381.fr64be/0">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !runtime.capability<transcript, "merlin3.bls12-381.fr64be/0">)>
      return %7 : !exec.outcome<(!algebra.field<"bls12-381.fr">, !runtime.capability<transcript, "merlin3.bls12-381.fr64be/0">)>
    }


"protocol.func"() ({
^entry(%state: !runtime.capability<transcript, "merlin3.bls12-381.fr64be/0">, %x: !algebra.field<"bls12-381.fr">, %reply: !algebra.field<"bls12-381.fr">, %go: i1):
%sent = protocol.exchange %x {sender="P", receiver="V", site="send"} : !algebra.field<"bls12-381.fr">
%received = protocol.exchange %reply {sender="V", receiver="P", site="reply"} : !algebra.field<"bls12-381.fr">
protocol.guard %go {owner="P", site="after_receive"}
%draw:2 = "protocol.local_call"(%state) {callee=@draw, role="P", site="draw"} : (!runtime.capability<transcript, "merlin3.bls12-381.fr64be/0">) -> (!algebra.field<"bls12-381.fr">, !runtime.capability<transcript, "merlin3.bls12-381.fr64be/0">)
%sum = algebra.field_add %received, %draw#0 : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
"protocol.return"(%sum, %draw#1) : (!algebra.field<"bls12-381.fr">, !runtime.capability<transcript, "merlin3.bls12-381.fr64be/0">) -> ()
}) {sym_name="main", function_type=(!runtime.capability<transcript, "merlin3.bls12-381.fr64be/0">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, i1) -> (!algebra.field<"bls12-381.fr">, !runtime.capability<transcript, "merlin3.bls12-381.fr64be/0">), roles=["P", "V"], input_roles=[["P"], ["P"], ["V"], ["P"]], output_roles=[["P"], ["P"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () }
