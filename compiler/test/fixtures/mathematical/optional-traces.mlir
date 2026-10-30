!f = !algebra.field<"bls12-381.fr">
!m = !algebra.field_matrix<"bls12-381.fr">
!opt = !data.variant<#data.identity<["atom", "OptionalTrace"]>, [#data.alternative<"none">, #data.alternative<"some", [!algebra.field_matrix<"bls12-381.fr">]>]>
!pair = !data.variant<#data.identity<["atom", "TracePair"]>, [#data.alternative<"pair", [!data.variant<#data.identity<["atom", "OptionalTrace"]>, [#data.alternative<"none">, #data.alternative<"some", [!algebra.field_matrix<"bls12-381.fr">]>]>, !data.variant<#data.identity<["atom", "OptionalTrace"]>, [#data.alternative<"none">, #data.alternative<"some", [!algebra.field_matrix<"bls12-381.fr">]>]>]>]>
module { "protocol.module"() ({
 "runtime.binding"() {sym_name="dimension",contract="matrix.dimension",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "runtime.binding"() {sym_name="index",contract="index.constant",arguments=[],implementation=""} : ()->()
    func.func @dimensions(%arg0: !runtime.scope, %arg1: !opt) -> !exec.outcome<(ui64, ui64)> attributes {no_inline, runtime.origin = ["dimensions", []]} {
      "exec.match"(%arg0, %arg1)[^bb2, ^bb3, ^bb4] <{alternatives = ["none", "some"], site = "presence"}> : (!runtime.scope, !opt) -> ()
    ^bb1(%0: ui64, %1: ui64):  // 2 preds: ^bb7, ^bb10
      %2 = "exec.returned"(%0, %1) : (ui64, ui64) -> !exec.outcome<(ui64, ui64)>
      return %2 : !exec.outcome<(ui64, ui64)>
    ^bb2(%3: !exec.stop):  // 7 preds: ^bb0, ^bb3, ^bb4, ^bb5, ^bb6, ^bb8, ^bb9
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(ui64, ui64)>
      return %4 : !exec.outcome<(ui64, ui64)>
    ^bb3:  // pred: ^bb0
      %5 = "runtime.enter_scope"(%arg0) <{kind = "match", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "none", site = "presence"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%5)[^bb5, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb4(%6: !m):  // pred: ^bb0
      %7 = "runtime.enter_scope"(%arg0, %6) <{kind = "match", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "some", site = "presence"}> : (!runtime.scope, !m) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%7)[^bb8, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb5(%8: !runtime.scope):  // pred: ^bb3
      %9 = call @control_0(%8) : (!runtime.scope) -> !exec.outcome<(ui64, ui64)>
      %10 = "runtime.exit_scope"(%8, %9) : (!runtime.scope, !exec.outcome<(ui64, ui64)>) -> !exec.outcome<(!runtime.transfer<(ui64, ui64)>)>
      "exec.dispatch"(%10)[^bb6, ^bb2] : (!exec.outcome<(!runtime.transfer<(ui64, ui64)>)>) -> ()
    ^bb6(%11: !runtime.transfer<(ui64, ui64)>):  // pred: ^bb5
      %12 = "runtime.accept_transfer"(%arg0, %11) : (!runtime.scope, !runtime.transfer<(ui64, ui64)>) -> !exec.outcome<(ui64, ui64)>
      "exec.dispatch"(%12)[^bb7, ^bb2] : (!exec.outcome<(ui64, ui64)>) -> ()
    ^bb7(%13: ui64, %14: ui64):  // pred: ^bb6
      cf.br ^bb1(%13, %14 : ui64, ui64)
    ^bb8(%15: !runtime.scope):  // pred: ^bb4
      %16 = call @control_1(%15, %6) : (!runtime.scope, !m) -> !exec.outcome<(ui64, ui64)>
      %17 = "runtime.exit_scope"(%15, %16) : (!runtime.scope, !exec.outcome<(ui64, ui64)>) -> !exec.outcome<(!runtime.transfer<(ui64, ui64)>)>
      "exec.dispatch"(%17)[^bb9, ^bb2] : (!exec.outcome<(!runtime.transfer<(ui64, ui64)>)>) -> ()
    ^bb9(%18: !runtime.transfer<(ui64, ui64)>):  // pred: ^bb8
      %19 = "runtime.accept_transfer"(%arg0, %18) : (!runtime.scope, !runtime.transfer<(ui64, ui64)>) -> !exec.outcome<(ui64, ui64)>
      "exec.dispatch"(%19)[^bb10, ^bb2] : (!exec.outcome<(ui64, ui64)>) -> ()
    ^bb10(%20: ui64, %21: ui64):  // pred: ^bb9
      cf.br ^bb1(%20, %21 : ui64, ui64)
    }
    func.func private @control_0(%arg0: !runtime.scope) -> !exec.outcome<(ui64, ui64)> attributes {no_inline, runtime.region} {
      %0 = "exec.apply"(%arg0) <{binding = @index, parameters = ["0"], site = "absent"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1: ui64):  // pred: ^bb0
      %2 = "exec.complete"(%arg0, %1, %1) : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64, ui64)>
      return %2 : !exec.outcome<(ui64, ui64)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(ui64, ui64)>
      return %4 : !exec.outcome<(ui64, ui64)>
    }
    func.func private @control_1(%arg0: !runtime.scope, %arg1: !m) -> !exec.outcome<(ui64, ui64)> attributes {no_inline, runtime.region} {
      %0 = "exec.apply"(%arg0, %arg1) <{binding = @dimension, parameters = ["0"], site = "height"}> : (!runtime.scope, !m) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1: ui64):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %arg1) <{binding = @dimension, parameters = ["1"], site = "width"}> : (!runtime.scope, !m) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%3: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(ui64, ui64)>
      return %4 : !exec.outcome<(ui64, ui64)>
    ^bb3(%5: ui64):  // pred: ^bb1
      %6 = "exec.complete"(%arg0, %1, %5) : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64, ui64)>
      return %6 : !exec.outcome<(ui64, ui64)>
    }

 "protocol.func"() ({ ^entry(%first:!opt,%second:!opt):
   %pair = "data.make"(%first,%second) {alternative="pair"} : (!opt,!opt)->!pair
   %a = "data.get"(%pair) {index=0:i64} : (!pair)->!opt
   %b = "data.get"(%pair) {index=1:i64} : (!pair)->!opt
   %presentA = "data.is"(%a) {alternative="some"} : (!opt)->i1
   %presentB = "data.is"(%b) {alternative="some"} : (!opt)->i1
   %shapeA:2 = "protocol.local_call"(%a) {callee=@dimensions,role="P",site="first"} : (!opt)->(ui64,ui64)
   %shapeB:2 = "protocol.local_call"(%b) {callee=@dimensions,role="P",site="second"} : (!opt)->(ui64,ui64)
   "protocol.return"(%presentA,%presentB,%shapeA#0,%shapeA#1,%shapeB#0,%shapeB#1) : (i1,i1,ui64,ui64,ui64,ui64)->()
 }) {sym_name="main",function_type=(!opt,!opt)->(i1,i1,ui64,ui64,ui64,ui64),roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"],["P"],["P"],["P"],["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
