module {
"protocol.module"() ({
  "runtime.binding"() {sym_name="add", contract="field.add", arguments=["bls12-381.fr"], implementation=""} : () -> ()
  "runtime.binding"() {sym_name="require", contract="control.require", arguments=[], implementation=""} : () -> ()
    func.func @leaf(%arg0: !runtime.scope, %arg1: !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)> attributes {no_inline, runtime.origin = ["leaf", []]} {
      %0 = "exec.apply"(%arg0, %arg1, %arg1) <{binding = @add, parameters = [], site = "twice"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb1(%1: !algebra.field<"bls12-381.fr">):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      return %2 : !exec.outcome<(!algebra.field<"bls12-381.fr">)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      return %4 : !exec.outcome<(!algebra.field<"bls12-381.fr">)>
    }
    func.func @work(%arg0: !runtime.scope, %arg1: !algebra.field<"bls12-381.fr">, %arg2: !runtime.capability<"rng:bls12-381.fr">, %arg3: i1) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !runtime.capability<"rng:bls12-381.fr">)> attributes {no_inline, runtime.origin = ["work", []]} {
      %0 = "exec.test"(%arg0, %arg3) <{site = "authored_branch"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1: i1):  // pred: ^bb0
      cf.cond_br %1, ^bb3, ^bb4
    ^bb2(%2: !exec.stop):  // 8 preds: ^bb0, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb9, ^bb10
      %3 = "exec.failed"(%2) : (!exec.stop) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !runtime.capability<"rng:bls12-381.fr">)>
      return %3 : !exec.outcome<(!algebra.field<"bls12-381.fr">, !runtime.capability<"rng:bls12-381.fr">)>
    ^bb3:  // pred: ^bb1
      %4 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "authored_branch"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%4)[^bb6, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb4:  // pred: ^bb1
      %5 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "authored_branch"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%5)[^bb9, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb5:  // 2 preds: ^bb8, ^bb11
      %6 = call @leaf(%arg0, %arg1) {runtime.site = "nested"} : (!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%6)[^bb12, ^bb2] : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb6(%7: !runtime.scope):  // pred: ^bb3
      %8 = call @control_0(%7) : (!runtime.scope) -> !exec.outcome<>
      %9 = "runtime.exit_scope"(%7, %8) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%9)[^bb7, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb7(%10: !runtime.transfer<>):  // pred: ^bb6
      %11 = "runtime.accept_transfer"(%arg0, %10) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%11)[^bb8, ^bb2] : (!exec.outcome<>) -> ()
    ^bb8:  // pred: ^bb7
      cf.br ^bb5
    ^bb9(%12: !runtime.scope):  // pred: ^bb4
      %13 = call @control_1(%12) : (!runtime.scope) -> !exec.outcome<>
      %14 = "runtime.exit_scope"(%12, %13) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%14)[^bb10, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb10(%15: !runtime.transfer<>):  // pred: ^bb9
      %16 = "runtime.accept_transfer"(%arg0, %15) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%16)[^bb11, ^bb2] : (!exec.outcome<>) -> ()
    ^bb11:  // pred: ^bb10
      cf.br ^bb5
    ^bb12(%17: !algebra.field<"bls12-381.fr">):  // pred: ^bb5
      %18 = "exec.returned"(%17, %arg2) : (!algebra.field<"bls12-381.fr">, !runtime.capability<"rng:bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !runtime.capability<"rng:bls12-381.fr">)>
      return %18 : !exec.outcome<(!algebra.field<"bls12-381.fr">, !runtime.capability<"rng:bls12-381.fr">)>
    }
    func.func private @control_0(%arg0: !runtime.scope) -> !exec.outcome<> attributes {no_inline, runtime.region} {
      %0 = "exec.complete"(%arg0) : (!runtime.scope) -> !exec.outcome<>
      return %0 : !exec.outcome<>
    }
    func.func private @control_1(%arg0: !runtime.scope) -> !exec.outcome<> attributes {no_inline, runtime.region} {
      %0 = "exec.complete"(%arg0) : (!runtime.scope) -> !exec.outcome<>
      return %0 : !exec.outcome<>
    }
    func.func @check(%arg0: !runtime.scope, %arg1: i1) -> !exec.outcome<> attributes {no_inline, runtime.origin = ["check", []]} {
      %0 = "exec.apply"(%arg0, %arg1) <{binding = @require, parameters = [], site = "required"}> : (!runtime.scope, i1) -> !exec.outcome<>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<>) -> ()
    ^bb1:  // pred: ^bb0
      %1 = "exec.returned"() : () -> !exec.outcome<>
      return %1 : !exec.outcome<>
    ^bb2(%2: !exec.stop):  // pred: ^bb0
      %3 = "exec.failed"(%2) : (!exec.stop) -> !exec.outcome<>
      return %3 : !exec.outcome<>
    }



  "protocol.func"() ({
  ^entry(%x: !algebra.field<"bls12-381.fr">, %resource: !runtime.capability<"rng:bls12-381.fr">, %go: i1):
    %sum = algebra.field_add %x, %x : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
    protocol.guard %go {owner="P", site="before_work"}
    "protocol.local_call"(%go) {callee=@check, role="P", site="first_check"} : (i1) -> ()
    "protocol.local_call"(%go) {callee=@check, role="P", site="second_check"} : (i1) -> ()
    %done:2 = "protocol.local_call"(%sum, %resource, %go) {callee=@work, role="P", site="work"} : (!algebra.field<"bls12-381.fr">, !runtime.capability<"rng:bls12-381.fr">, i1) -> (!algebra.field<"bls12-381.fr">, !runtime.capability<"rng:bls12-381.fr">)
    %sent = protocol.exchange %done#0 {sender="P", receiver="V", site="send"} : !algebra.field<"bls12-381.fr">
    "protocol.return"(%sent, %done#1) : (!algebra.field<"bls12-381.fr">, !runtime.capability<"rng:bls12-381.fr">) -> ()
  }) {sym_name="main", function_type=(!algebra.field<"bls12-381.fr">, !runtime.capability<"rng:bls12-381.fr">, i1) -> (!algebra.field<"bls12-381.fr">, !runtime.capability<"rng:bls12-381.fr">), roles=["P", "V"], input_roles=[["P"],["P"],["P"]], output_roles=[["P", "V"],["P"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> ()
}
