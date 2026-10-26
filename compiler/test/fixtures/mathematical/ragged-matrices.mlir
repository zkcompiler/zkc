!f = !algebra.field<"bls12-381.fr">
!m = !algebra.field_matrix<"bls12-381.fr">
!v = !algebra.field_vector<"bls12-381.fr">
!ms = !data.sequence<!m>
!vs = !data.sequence<!v>
module { "protocol.module"() ({
 "runtime.binding"() {sym_name="at",contract="sequence.at",arguments=["matrix:bls12-381.fr"],implementation=""} : ()->()
 "runtime.binding"() {sym_name="vector",contract="sequence.at",arguments=["vector:bls12-381.fr"],implementation=""} : ()->()
 "runtime.binding"() {sym_name="length",contract="sequence.length",arguments=["matrix:bls12-381.fr"],implementation=""} : ()->()
 "runtime.binding"() {sym_name="vlength",contract="sequence.length",arguments=["vector:bls12-381.fr"],implementation=""} : ()->()
 "runtime.binding"() {sym_name="constant",contract="index.constant",arguments=[],implementation=""} : ()->()
 "runtime.binding"() {sym_name="equal",contract="index.equal",arguments=[],implementation=""} : ()->()
 "runtime.binding"() {sym_name="and",contract="bool.and",arguments=[],implementation=""} : ()->()
 "runtime.binding"() {sym_name="zero",contract="field.constant",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "runtime.binding"() {sym_name="add",contract="field.add",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "runtime.binding"() {sym_name="bilinear",contract="matrix.bilinear",arguments=["bls12-381.fr"],implementation=""} : ()->()
    func.func @evaluate(%arg0: !runtime.scope, %arg1: !ms, %arg2: !vs, %arg3: !vs) -> !exec.outcome<(!f, i1)> attributes {no_inline, runtime.origin = ["evaluate", []]} {
      %0 = "exec.apply"(%arg0, %arg1) <{binding = @length, parameters = [], site = "count"}> : (!runtime.scope, !ms) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1: ui64):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %arg2) <{binding = @vlength, parameters = [], site = "rows"}> : (!runtime.scope, !vs) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%3: !exec.stop):  // 13 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb9, ^bb10, ^bb12, ^bb13, ^bb15, ^bb16
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!f, i1)>
      return %4 : !exec.outcome<(!f, i1)>
    ^bb3(%5: ui64):  // pred: ^bb1
      %6 = "exec.apply"(%arg0, %arg3) <{binding = @vlength, parameters = [], site = "columns"}> : (!runtime.scope, !vs) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%7: ui64):  // pred: ^bb3
      %8 = "exec.apply"(%arg0, %1, %5) <{binding = @equal, parameters = [], site = "rows_match"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%8)[^bb5, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb5(%9: i1):  // pred: ^bb4
      %10 = "exec.apply"(%arg0, %1, %7) <{binding = @equal, parameters = [], site = "columns_match"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%10)[^bb6, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb6(%11: i1):  // pred: ^bb5
      %12 = "exec.apply"(%arg0, %9, %11) <{binding = @and, parameters = [], site = "counts"}> : (!runtime.scope, i1, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%12)[^bb7, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb7(%13: i1):  // pred: ^bb6
      %14 = "exec.test"(%arg0, %13) <{site = "shape"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%14)[^bb8, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb8(%15: i1):  // pred: ^bb7
      cf.cond_br %15, ^bb9, ^bb10
    ^bb9:  // pred: ^bb8
      %16 = "runtime.enter_scope"(%arg0, %1, %arg1, %arg2, %arg3) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 4>, selection = "then", site = "shape"}> : (!runtime.scope, ui64, !ms, !vs, !vs) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%16)[^bb12, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb10:  // pred: ^bb8
      %17 = "runtime.enter_scope"(%arg0, %1, %arg1, %arg2, %arg3) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 4>, selection = "else", site = "shape"}> : (!runtime.scope, ui64, !ms, !vs, !vs) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%17)[^bb15, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb11(%18: !f):  // 2 preds: ^bb14, ^bb17
      %19 = "exec.returned"(%18, %13) : (!f, i1) -> !exec.outcome<(!f, i1)>
      return %19 : !exec.outcome<(!f, i1)>
    ^bb12(%20: !runtime.scope):  // pred: ^bb9
      %21 = call @control_0(%20, %1, %arg1, %arg2, %arg3) : (!runtime.scope, ui64, !ms, !vs, !vs) -> !exec.outcome<(!f)>
      %22 = "runtime.exit_scope"(%20, %21) : (!runtime.scope, !exec.outcome<(!f)>) -> !exec.outcome<(!runtime.transfer<(!f)>)>
      "exec.dispatch"(%22)[^bb13, ^bb2] : (!exec.outcome<(!runtime.transfer<(!f)>)>) -> ()
    ^bb13(%23: !runtime.transfer<(!f)>):  // pred: ^bb12
      %24 = "runtime.accept_transfer"(%arg0, %23) : (!runtime.scope, !runtime.transfer<(!f)>) -> !exec.outcome<(!f)>
      "exec.dispatch"(%24)[^bb14, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb14(%25: !f):  // pred: ^bb13
      cf.br ^bb11(%25 : !f)
    ^bb15(%26: !runtime.scope):  // pred: ^bb10
      %27 = call @control_2(%26, %1, %arg1, %arg2, %arg3) : (!runtime.scope, ui64, !ms, !vs, !vs) -> !exec.outcome<(!f)>
      %28 = "runtime.exit_scope"(%26, %27) : (!runtime.scope, !exec.outcome<(!f)>) -> !exec.outcome<(!runtime.transfer<(!f)>)>
      "exec.dispatch"(%28)[^bb16, ^bb2] : (!exec.outcome<(!runtime.transfer<(!f)>)>) -> ()
    ^bb16(%29: !runtime.transfer<(!f)>):  // pred: ^bb15
      %30 = "runtime.accept_transfer"(%arg0, %29) : (!runtime.scope, !runtime.transfer<(!f)>) -> !exec.outcome<(!f)>
      "exec.dispatch"(%30)[^bb17, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb17(%31: !f):  // pred: ^bb16
      cf.br ^bb11(%31 : !f)
    }
    func.func private @control_0(%arg0: !runtime.scope, %arg1: ui64, %arg2: !ms, %arg3: !vs, %arg4: !vs) -> !exec.outcome<(!f)> attributes {no_inline, runtime.region} {
      %0 = "exec.apply"(%arg0) <{binding = @constant, parameters = ["0"], site = "start"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1: ui64):  // pred: ^bb0
      %2 = "exec.apply"(%arg0) <{binding = @zero, parameters = ["0"], site = "zero"}> : (!runtime.scope) -> !exec.outcome<(!f)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb2(%3: !exec.stop):  // 5 preds: ^bb0, ^bb1, ^bb3, ^bb7, ^bb9
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!f)>
      return %4 : !exec.outcome<(!f)>
    ^bb3(%5: !f):  // pred: ^bb1
      %6 = "exec.range"(%arg0, %1, %arg1) <{site = "traces"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<(i64, i64)>) -> ()
    ^bb4(%7: i64, %8: i64):  // pred: ^bb3
      %9 = "runtime.borrow_transfer"(%arg0, %5) : (!runtime.scope, !f) -> !runtime.transfer<(!f)>
      cf.br ^bb5(%7, %9 : i64, !runtime.transfer<(!f)>)
    ^bb5(%10: i64, %11: !runtime.transfer<(!f)>):  // 2 preds: ^bb4, ^bb8
      %12 = arith.cmpi ult, %10, %8 : i64
      cf.cond_br %12, ^bb6, ^bb7(%11 : !runtime.transfer<(!f)>)
    ^bb6:  // pred: ^bb5
      %13 = "runtime.iteration"(%arg0, %10) <{site = "traces"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%13)[^bb10, ^bb9] : (!exec.outcome<(ui64)>) -> ()
    ^bb7(%14: !runtime.transfer<(!f)>):  // pred: ^bb5
      %15 = "runtime.accept_transfer"(%arg0, %14) : (!runtime.scope, !runtime.transfer<(!f)>) -> !exec.outcome<(!f)>
      "exec.dispatch"(%15)[^bb13, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb8(%16: !runtime.transfer<(!f)>):  // pred: ^bb12
      %c1_i64 = arith.constant 1 : i64
      %17 = arith.addi %10, %c1_i64 : i64
      cf.br ^bb5(%17, %16 : i64, !runtime.transfer<(!f)>)
    ^bb9(%18: !exec.stop):  // 3 preds: ^bb6, ^bb10, ^bb11
      "runtime.release_transfer"(%11) : (!runtime.transfer<(!f)>) -> ()
      cf.br ^bb2(%18 : !exec.stop)
    ^bb10(%19: ui64):  // pred: ^bb6
      %20 = "runtime.transfer_values"(%11) : (!runtime.transfer<(!f)>) -> !f
      %21 = "runtime.enter_scope"(%arg0, %10, %19, %20, %arg2, %arg3, %arg4) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 5>, site = "traces"}> : (!runtime.scope, i64, ui64, !f, !ms, !vs, !vs) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%21)[^bb11, ^bb9] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb11(%22: !runtime.scope):  // pred: ^bb10
      %23 = call @control_1(%22, %19, %20, %arg2, %arg3, %arg4) : (!runtime.scope, ui64, !f, !ms, !vs, !vs) -> !exec.outcome<(!f)>
      %24 = "runtime.exit_scope"(%22, %23) : (!runtime.scope, !exec.outcome<(!f)>) -> !exec.outcome<(!runtime.transfer<(!f)>)>
      "exec.dispatch"(%24)[^bb12, ^bb9] : (!exec.outcome<(!runtime.transfer<(!f)>)>) -> ()
    ^bb12(%25: !runtime.transfer<(!f)>):  // pred: ^bb11
      "runtime.release_transfer"(%11) : (!runtime.transfer<(!f)>) -> ()
      cf.br ^bb8(%25 : !runtime.transfer<(!f)>)
    ^bb13(%26: !f):  // pred: ^bb7
      %27 = "exec.complete"(%arg0, %26) : (!runtime.scope, !f) -> !exec.outcome<(!f)>
      return %27 : !exec.outcome<(!f)>
    }
    func.func private @control_1(%arg0: !runtime.scope, %arg1: ui64, %arg2: !f, %arg3: !ms, %arg4: !vs, %arg5: !vs) -> !exec.outcome<(!f)> attributes {no_inline, runtime.region} {
      %0 = "exec.apply"(%arg0, %arg3, %arg1) <{binding = @at, parameters = [], site = "matrix"}> : (!runtime.scope, !ms, ui64) -> !exec.outcome<(!m)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!m)>) -> ()
    ^bb1(%1: !m):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %arg4, %arg1) <{binding = @vector, parameters = [], site = "row"}> : (!runtime.scope, !vs, ui64) -> !exec.outcome<(!v)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(!v)>) -> ()
    ^bb2(%3: !exec.stop):  // 5 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!f)>
      return %4 : !exec.outcome<(!f)>
    ^bb3(%5: !v):  // pred: ^bb1
      %6 = "exec.apply"(%arg0, %arg5, %arg1) <{binding = @vector, parameters = [], site = "column"}> : (!runtime.scope, !vs, ui64) -> !exec.outcome<(!v)>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<(!v)>) -> ()
    ^bb4(%7: !v):  // pred: ^bb3
      %8 = "exec.apply"(%arg0, %1, %5, %7) <{binding = @bilinear, parameters = [], site = "term"}> : (!runtime.scope, !m, !v, !v) -> !exec.outcome<(!f)>
      "exec.dispatch"(%8)[^bb5, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb5(%9: !f):  // pred: ^bb4
      %10 = "exec.apply"(%arg0, %arg2, %9) <{binding = @add, parameters = [], site = "sum"}> : (!runtime.scope, !f, !f) -> !exec.outcome<(!f)>
      "exec.dispatch"(%10)[^bb6, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb6(%11: !f):  // pred: ^bb5
      %12 = "exec.complete"(%arg0, %11) : (!runtime.scope, !f) -> !exec.outcome<(!f)>
      return %12 : !exec.outcome<(!f)>
    }
    func.func private @control_2(%arg0: !runtime.scope, %arg1: ui64, %arg2: !ms, %arg3: !vs, %arg4: !vs) -> !exec.outcome<(!f)> attributes {no_inline, runtime.region} {
      %0 = "exec.apply"(%arg0) <{binding = @zero, parameters = ["0"], site = "mismatch_zero"}> : (!runtime.scope) -> !exec.outcome<(!f)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb1(%1: !f):  // pred: ^bb0
      %2 = "exec.complete"(%arg0, %1) : (!runtime.scope, !f) -> !exec.outcome<(!f)>
      return %2 : !exec.outcome<(!f)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!f)>
      return %4 : !exec.outcome<(!f)>
    }

 "protocol.func"() ({ ^entry(%matrices:!ms,%rows:!vs,%columns:!vs,%claim:!f):
   %received = protocol.exchange %matrices {sender="P",receiver="V",site="traces"} : !ms
   %result:2 = "protocol.local_call"(%received,%rows,%columns) {callee=@evaluate,role="V",site="evaluate"} : (!ms,!vs,!vs)->(!f,i1)
   %same = algebra.field_equal %result#0,%claim : (!f,!f)->i1
   %accepted = arith.andi %same,%result#1 : i1
   "protocol.return"(%accepted) : (i1)->()
 }) {sym_name="main",function_type=(!ms,!vs,!vs,!f)->i1,roles=["P","V"],input_roles=[["P"],["V"],["V"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
