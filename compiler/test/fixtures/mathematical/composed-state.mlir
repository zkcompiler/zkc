// Executable algebraic clients; see docs/compiler/mathematics.md.
!f = !algebra.field<"bls12-381.fr">
!g = !algebra.group<"bls12-381.g1">
!fs = !algebra.field_vector<"bls12-381.fr">
!gs = !algebra.group_vector<"bls12-381.g1">
!r = !runtime.capability<rng, "bls12-381.fr">
!s = !protocol.service_ref<"random.bls12-381.fr/0">
module { "protocol.module"() ({
  "runtime.binding"() {sym_name="random_draw",contract="random.draw",arguments=["bls12-381.fr"],implementation=""} : ()->()
  "runtime.binding"() {sym_name="field_constant",contract="field.constant",arguments=["bls12-381.fr"],implementation=""} : ()->()
  "runtime.binding"() {sym_name="field_equal",contract="field.equal",arguments=["bls12-381.fr"],implementation=""} : ()->()
  "runtime.binding"() {sym_name="field_inverse",contract="field.inverse",arguments=["bls12-381.fr"],implementation=""} : ()->()
  "runtime.binding"() {sym_name="bool_not",contract="bool.not",arguments=[],implementation=""} : ()->()
  "runtime.binding"() {sym_name="vector_scale",contract="vector.scale",arguments=["bls12-381.fr"],implementation=""} : ()->()
  "runtime.binding"() {sym_name="curve_msm",contract="curve.msm",arguments=["bls12-381.g1"],implementation=""} : ()->()
  "runtime.binding"() {sym_name="curve_append",contract="curve.append",arguments=["bls12-381.g1"],implementation=""} : ()->()
  "runtime.binding"() {sym_name="vector_append",contract="vector.append",arguments=["bls12-381.fr"],implementation=""} : ()->()
  "runtime.binding"() {sym_name="curve_get",contract="curve.get",arguments=["bls12-381.g1"],implementation=""} : ()->()
  "runtime.binding"() {sym_name="vector_get",contract="vector.get",arguments=["bls12-381.fr"],implementation=""} : ()->()
  "runtime.binding"() {sym_name="curve_empty",contract="curve.empty",arguments=["bls12-381.g1"],implementation=""} : ()->()
  "runtime.binding"() {sym_name="vector_empty",contract="vector.empty",arguments=["bls12-381.fr"],implementation=""} : ()->()
  "runtime.binding"() {sym_name="vector_split",contract="vector.split",arguments=["bls12-381.fr"],implementation=""} : ()->()
  "runtime.binding"() {sym_name="curve_split",contract="curve.split",arguments=["bls12-381.g1"],implementation=""} : ()->()
  "runtime.binding"() {sym_name="vector_add",contract="vector.add",arguments=["bls12-381.fr"],implementation=""} : ()->()
  "runtime.binding"() {sym_name="curve_vector_scale",contract="curve.vector_scale",arguments=["bls12-381.g1"],implementation=""} : ()->()
  "runtime.binding"() {sym_name="curve_vector_add",contract="curve.vector_add",arguments=["bls12-381.g1"],implementation=""} : ()->()
  "runtime.binding"() {sym_name="curve_length",contract="curve.length",arguments=["bls12-381.g1"],implementation=""} : ()->()
  "runtime.binding"() {sym_name="index_equal",contract="index.equal",arguments=[],implementation=""} : ()->()
  "runtime.binding"() {sym_name="index_constant",contract="index.constant",arguments=[],implementation=""} : ()->()
  "runtime.binding"() {sym_name="curve_equal",contract="curve.equal",arguments=["bls12-381.g1"],implementation=""} : ()->()
  "runtime.binding"() {sym_name="bool_and",contract="bool.and",arguments=[],implementation=""} : ()->()
    func.func @draw(%arg0: !runtime.scope, %arg1: !r) -> !exec.outcome<(!f, !r)> attributes {no_inline, runtime.origin = ["draw", []]} {
      %0 = "exec.apply"(%arg0, %arg1) <{binding = @random_draw, parameters = [], site = "s"}> : (!runtime.scope, !r) -> !exec.outcome<(!f, !r)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!f, !r)>) -> ()
    ^bb1(%1: !f, %2: !r):  // pred: ^bb0
      %3 = "exec.returned"(%1, %2) : (!f, !r) -> !exec.outcome<(!f, !r)>
      return %3 : !exec.outcome<(!f, !r)>
    ^bb2(%4: !exec.stop):  // pred: ^bb0
      %5 = "exec.failed"(%4) : (!exec.stop) -> !exec.outcome<(!f, !r)>
      return %5 : !exec.outcome<(!f, !r)>
    }
    func.func @inverse(%arg0: !runtime.scope, %arg1: !f) -> !exec.outcome<(!f, i1)> attributes {no_inline, runtime.origin = ["inverse", []]} {
      %0 = "exec.apply"(%arg0) <{binding = @field_constant, parameters = ["0"], site = "zero"}> : (!runtime.scope) -> !exec.outcome<(!f)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb1(%1: !f):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %arg1, %1) <{binding = @field_equal, parameters = [], site = "empty"}> : (!runtime.scope, !f, !f) -> !exec.outcome<(i1)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%3: !exec.stop):  // 10 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!f, i1)>
      return %4 : !exec.outcome<(!f, i1)>
    ^bb3(%5: i1):  // pred: ^bb1
      %6 = "exec.test"(%arg0, %5) <{site = "partial_inverse"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb4(%7: i1):  // pred: ^bb3
      cf.cond_br %7, ^bb5, ^bb6
    ^bb5:  // pred: ^bb4
      %8 = "runtime.enter_scope"(%arg0, %arg1) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "then", site = "partial_inverse"}> : (!runtime.scope, !f) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%8)[^bb8, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %9 = "runtime.enter_scope"(%arg0, %arg1) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "else", site = "partial_inverse"}> : (!runtime.scope, !f) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%9)[^bb11, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7(%10: !f):  // 2 preds: ^bb10, ^bb13
      %11 = "exec.apply"(%arg0, %5) <{binding = @bool_not, parameters = [], site = "ok"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%11)[^bb14, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb8(%12: !runtime.scope):  // pred: ^bb5
      %13 = call @control_0(%12, %arg1) : (!runtime.scope, !f) -> !exec.outcome<(!f)>
      %14 = "runtime.exit_scope"(%12, %13) : (!runtime.scope, !exec.outcome<(!f)>) -> !exec.outcome<(!runtime.transfer<(!f)>)>
      "exec.dispatch"(%14)[^bb9, ^bb2] : (!exec.outcome<(!runtime.transfer<(!f)>)>) -> ()
    ^bb9(%15: !runtime.transfer<(!f)>):  // pred: ^bb8
      %16 = "runtime.accept_transfer"(%arg0, %15) : (!runtime.scope, !runtime.transfer<(!f)>) -> !exec.outcome<(!f)>
      "exec.dispatch"(%16)[^bb10, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb10(%17: !f):  // pred: ^bb9
      cf.br ^bb7(%17 : !f)
    ^bb11(%18: !runtime.scope):  // pred: ^bb6
      %19 = call @control_1(%18, %arg1) : (!runtime.scope, !f) -> !exec.outcome<(!f)>
      %20 = "runtime.exit_scope"(%18, %19) : (!runtime.scope, !exec.outcome<(!f)>) -> !exec.outcome<(!runtime.transfer<(!f)>)>
      "exec.dispatch"(%20)[^bb12, ^bb2] : (!exec.outcome<(!runtime.transfer<(!f)>)>) -> ()
    ^bb12(%21: !runtime.transfer<(!f)>):  // pred: ^bb11
      %22 = "runtime.accept_transfer"(%arg0, %21) : (!runtime.scope, !runtime.transfer<(!f)>) -> !exec.outcome<(!f)>
      "exec.dispatch"(%22)[^bb13, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb13(%23: !f):  // pred: ^bb12
      cf.br ^bb7(%23 : !f)
    ^bb14(%24: i1):  // pred: ^bb7
      %25 = "exec.returned"(%10, %24) : (!f, i1) -> !exec.outcome<(!f, i1)>
      return %25 : !exec.outcome<(!f, i1)>
    }
    func.func private @control_0(%arg0: !runtime.scope, %arg1: !f) -> !exec.outcome<(!f)> attributes {no_inline, runtime.region} {
      %0 = "exec.complete"(%arg0, %arg1) : (!runtime.scope, !f) -> !exec.outcome<(!f)>
      return %0 : !exec.outcome<(!f)>
    }
    func.func private @control_1(%arg0: !runtime.scope, %arg1: !f) -> !exec.outcome<(!f)> attributes {no_inline, runtime.region} {
      %0 = "exec.apply"(%arg0, %arg1) <{binding = @field_inverse, parameters = [], site = "inv"}> : (!runtime.scope, !f) -> !exec.outcome<(!f)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb1(%1: !f):  // pred: ^bb0
      %2 = "exec.complete"(%arg0, %1) : (!runtime.scope, !f) -> !exec.outcome<(!f)>
      return %2 : !exec.outcome<(!f)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!f)>
      return %4 : !exec.outcome<(!f)>
    }
    func.func @scale_vector(%arg0: !runtime.scope, %arg1: !fs, %arg2: !f) -> !exec.outcome<(!fs)> attributes {no_inline, runtime.origin = ["scale_vector", []]} {
      %0 = "exec.apply"(%arg0, %arg1, %arg2) <{binding = @vector_scale, parameters = [], site = "out"}> : (!runtime.scope, !fs, !f) -> !exec.outcome<(!fs)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!fs)>) -> ()
    ^bb1(%1: !fs):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!fs) -> !exec.outcome<(!fs)>
      return %2 : !exec.outcome<(!fs)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!fs)>
      return %4 : !exec.outcome<(!fs)>
    }
    func.func @msm(%arg0: !runtime.scope, %arg1: !fs, %arg2: !gs) -> !exec.outcome<(!g)> attributes {no_inline, runtime.origin = ["msm", []]} {
      %0 = "exec.apply"(%arg0, %arg1, %arg2) <{binding = @curve_msm, parameters = [], site = "out"}> : (!runtime.scope, !fs, !gs) -> !exec.outcome<(!g)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!g)>) -> ()
    ^bb1(%1: !g):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!g) -> !exec.outcome<(!g)>
      return %2 : !exec.outcome<(!g)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!g)>
      return %4 : !exec.outcome<(!g)>
    }
    func.func @append_group(%arg0: !runtime.scope, %arg1: !gs, %arg2: !g) -> !exec.outcome<(!gs)> attributes {no_inline, runtime.origin = ["append_group", []]} {
      %0 = "exec.apply"(%arg0, %arg1, %arg2) <{binding = @curve_append, parameters = [], site = "out"}> : (!runtime.scope, !gs, !g) -> !exec.outcome<(!gs)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!gs)>) -> ()
    ^bb1(%1: !gs):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!gs) -> !exec.outcome<(!gs)>
      return %2 : !exec.outcome<(!gs)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!gs)>
      return %4 : !exec.outcome<(!gs)>
    }
    func.func @append_field(%arg0: !runtime.scope, %arg1: !fs, %arg2: !f) -> !exec.outcome<(!fs)> attributes {no_inline, runtime.origin = ["append_field", []]} {
      %0 = "exec.apply"(%arg0, %arg1, %arg2) <{binding = @vector_append, parameters = [], site = "out"}> : (!runtime.scope, !fs, !f) -> !exec.outcome<(!fs)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!fs)>) -> ()
    ^bb1(%1: !fs):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!fs) -> !exec.outcome<(!fs)>
      return %2 : !exec.outcome<(!fs)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!fs)>
      return %4 : !exec.outcome<(!fs)>
    }
    func.func @get_group(%arg0: !runtime.scope, %arg1: !gs, %arg2: ui64) -> !exec.outcome<(!g)> attributes {no_inline, runtime.origin = ["get_group", []]} {
      %0 = "exec.apply"(%arg0, %arg1, %arg2) <{binding = @curve_get, parameters = [], site = "out"}> : (!runtime.scope, !gs, ui64) -> !exec.outcome<(!g)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!g)>) -> ()
    ^bb1(%1: !g):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!g) -> !exec.outcome<(!g)>
      return %2 : !exec.outcome<(!g)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!g)>
      return %4 : !exec.outcome<(!g)>
    }
    func.func @get_field(%arg0: !runtime.scope, %arg1: !fs, %arg2: ui64) -> !exec.outcome<(!f)> attributes {no_inline, runtime.origin = ["get_field", []]} {
      %0 = "exec.apply"(%arg0, %arg1, %arg2) <{binding = @vector_get, parameters = [], site = "out"}> : (!runtime.scope, !fs, ui64) -> !exec.outcome<(!f)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb1(%1: !f):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!f) -> !exec.outcome<(!f)>
      return %2 : !exec.outcome<(!f)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!f)>
      return %4 : !exec.outcome<(!f)>
    }
    func.func @empty_group(%arg0: !runtime.scope) -> !exec.outcome<(!gs)> attributes {no_inline, runtime.origin = ["empty_group", []]} {
      %0 = "exec.apply"(%arg0) <{binding = @curve_empty, parameters = [], site = "out"}> : (!runtime.scope) -> !exec.outcome<(!gs)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!gs)>) -> ()
    ^bb1(%1: !gs):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!gs) -> !exec.outcome<(!gs)>
      return %2 : !exec.outcome<(!gs)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!gs)>
      return %4 : !exec.outcome<(!gs)>
    }
    func.func @empty_field(%arg0: !runtime.scope) -> !exec.outcome<(!fs)> attributes {no_inline, runtime.origin = ["empty_field", []]} {
      %0 = "exec.apply"(%arg0) <{binding = @vector_empty, parameters = [], site = "out"}> : (!runtime.scope) -> !exec.outcome<(!fs)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!fs)>) -> ()
    ^bb1(%1: !fs):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!fs) -> !exec.outcome<(!fs)>
      return %2 : !exec.outcome<(!fs)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!fs)>
      return %4 : !exec.outcome<(!fs)>
    }
    func.func @cross(%arg0: !runtime.scope, %arg1: !fs, %arg2: !gs) -> !exec.outcome<(!g, !g)> attributes {no_inline, runtime.origin = ["cross", []]} {
      %0 = "exec.apply"(%arg0, %arg1) <{binding = @vector_split, parameters = [], site = "a2"}> : (!runtime.scope, !fs) -> !exec.outcome<(!fs, !fs)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!fs, !fs)>) -> ()
    ^bb1(%1: !fs, %2: !fs):  // pred: ^bb0
      %3 = "exec.apply"(%arg0, %arg2) <{binding = @curve_split, parameters = [], site = "g2"}> : (!runtime.scope, !gs) -> !exec.outcome<(!gs, !gs)>
      "exec.dispatch"(%3)[^bb3, ^bb2] : (!exec.outcome<(!gs, !gs)>) -> ()
    ^bb2(%4: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %5 = "exec.failed"(%4) : (!exec.stop) -> !exec.outcome<(!g, !g)>
      return %5 : !exec.outcome<(!g, !g)>
    ^bb3(%6: !gs, %7: !gs):  // pred: ^bb1
      %8 = "exec.apply"(%arg0, %1, %7) <{binding = @curve_msm, parameters = [], site = "l"}> : (!runtime.scope, !fs, !gs) -> !exec.outcome<(!g)>
      "exec.dispatch"(%8)[^bb4, ^bb2] : (!exec.outcome<(!g)>) -> ()
    ^bb4(%9: !g):  // pred: ^bb3
      %10 = "exec.apply"(%arg0, %2, %6) <{binding = @curve_msm, parameters = [], site = "r"}> : (!runtime.scope, !fs, !gs) -> !exec.outcome<(!g)>
      "exec.dispatch"(%10)[^bb5, ^bb2] : (!exec.outcome<(!g)>) -> ()
    ^bb5(%11: !g):  // pred: ^bb4
      %12 = "exec.returned"(%9, %11) : (!g, !g) -> !exec.outcome<(!g, !g)>
      return %12 : !exec.outcome<(!g, !g)>
    }
    func.func @fold_field(%arg0: !runtime.scope, %arg1: !fs, %arg2: !f, %arg3: !f) -> !exec.outcome<(!fs)> attributes {no_inline, runtime.origin = ["fold_field", []]} {
      %0 = "exec.apply"(%arg0, %arg1) <{binding = @vector_split, parameters = [], site = "s"}> : (!runtime.scope, !fs) -> !exec.outcome<(!fs, !fs)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!fs, !fs)>) -> ()
    ^bb1(%1: !fs, %2: !fs):  // pred: ^bb0
      %3 = "exec.apply"(%arg0, %1, %arg2) <{binding = @vector_scale, parameters = [], site = "l"}> : (!runtime.scope, !fs, !f) -> !exec.outcome<(!fs)>
      "exec.dispatch"(%3)[^bb3, ^bb2] : (!exec.outcome<(!fs)>) -> ()
    ^bb2(%4: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %5 = "exec.failed"(%4) : (!exec.stop) -> !exec.outcome<(!fs)>
      return %5 : !exec.outcome<(!fs)>
    ^bb3(%6: !fs):  // pred: ^bb1
      %7 = "exec.apply"(%arg0, %2, %arg3) <{binding = @vector_scale, parameters = [], site = "r"}> : (!runtime.scope, !fs, !f) -> !exec.outcome<(!fs)>
      "exec.dispatch"(%7)[^bb4, ^bb2] : (!exec.outcome<(!fs)>) -> ()
    ^bb4(%8: !fs):  // pred: ^bb3
      %9 = "exec.apply"(%arg0, %6, %8) <{binding = @vector_add, parameters = [], site = "v"}> : (!runtime.scope, !fs, !fs) -> !exec.outcome<(!fs)>
      "exec.dispatch"(%9)[^bb5, ^bb2] : (!exec.outcome<(!fs)>) -> ()
    ^bb5(%10: !fs):  // pred: ^bb4
      %11 = "exec.returned"(%10) : (!fs) -> !exec.outcome<(!fs)>
      return %11 : !exec.outcome<(!fs)>
    }
    func.func @fold_group(%arg0: !runtime.scope, %arg1: !gs, %arg2: !f, %arg3: !f) -> !exec.outcome<(!gs)> attributes {no_inline, runtime.origin = ["fold_group", []]} {
      %0 = "exec.apply"(%arg0, %arg1) <{binding = @curve_split, parameters = [], site = "s"}> : (!runtime.scope, !gs) -> !exec.outcome<(!gs, !gs)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!gs, !gs)>) -> ()
    ^bb1(%1: !gs, %2: !gs):  // pred: ^bb0
      %3 = "exec.apply"(%arg0, %1, %arg2) <{binding = @curve_vector_scale, parameters = [], site = "l"}> : (!runtime.scope, !gs, !f) -> !exec.outcome<(!gs)>
      "exec.dispatch"(%3)[^bb3, ^bb2] : (!exec.outcome<(!gs)>) -> ()
    ^bb2(%4: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %5 = "exec.failed"(%4) : (!exec.stop) -> !exec.outcome<(!gs)>
      return %5 : !exec.outcome<(!gs)>
    ^bb3(%6: !gs):  // pred: ^bb1
      %7 = "exec.apply"(%arg0, %2, %arg3) <{binding = @curve_vector_scale, parameters = [], site = "r"}> : (!runtime.scope, !gs, !f) -> !exec.outcome<(!gs)>
      "exec.dispatch"(%7)[^bb4, ^bb2] : (!exec.outcome<(!gs)>) -> ()
    ^bb4(%8: !gs):  // pred: ^bb3
      %9 = "exec.apply"(%arg0, %6, %8) <{binding = @curve_vector_add, parameters = [], site = "v"}> : (!runtime.scope, !gs, !gs) -> !exec.outcome<(!gs)>
      "exec.dispatch"(%9)[^bb5, ^bb2] : (!exec.outcome<(!gs)>) -> ()
    ^bb5(%10: !gs):  // pred: ^bb4
      %11 = "exec.returned"(%10) : (!gs) -> !exec.outcome<(!gs)>
      return %11 : !exec.outcome<(!gs)>
    }
    func.func @same_groups(%arg0: !runtime.scope, %arg1: !gs, %arg2: !gs) -> !exec.outcome<(i1)> attributes {no_inline, runtime.origin = ["same_groups", []]} {
      %0 = "exec.apply"(%arg0, %arg1) <{binding = @curve_length, parameters = [], site = "n"}> : (!runtime.scope, !gs) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1: ui64):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %arg2) <{binding = @curve_length, parameters = [], site = "m"}> : (!runtime.scope, !gs) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%3: !exec.stop):  // 10 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb6, ^bb7, ^bb9, ^bb10, ^bb12, ^bb13
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(i1)>
      return %4 : !exec.outcome<(i1)>
    ^bb3(%5: ui64):  // pred: ^bb1
      %6 = "exec.apply"(%arg0, %1, %5) <{binding = @index_equal, parameters = [], site = "same"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb4(%7: i1):  // pred: ^bb3
      %8 = "exec.test"(%arg0, %7) <{site = "lengths"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%8)[^bb5, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb5(%9: i1):  // pred: ^bb4
      cf.cond_br %9, ^bb6, ^bb7
    ^bb6:  // pred: ^bb5
      %10 = "runtime.enter_scope"(%arg0, %arg1, %arg2, %1) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "then", site = "lengths"}> : (!runtime.scope, !gs, !gs, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%10)[^bb9, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // pred: ^bb5
      %11 = "runtime.enter_scope"(%arg0, %arg1, %arg2, %1) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "else", site = "lengths"}> : (!runtime.scope, !gs, !gs, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%11)[^bb12, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb8(%12: i1):  // 2 preds: ^bb11, ^bb14
      %13 = "exec.returned"(%12) : (i1) -> !exec.outcome<(i1)>
      return %13 : !exec.outcome<(i1)>
    ^bb9(%14: !runtime.scope):  // pred: ^bb6
      %15 = call @control_2(%14, %arg1, %arg2, %1) : (!runtime.scope, !gs, !gs, ui64) -> !exec.outcome<(i1)>
      %16 = "runtime.exit_scope"(%14, %15) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%16)[^bb10, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb10(%17: !runtime.transfer<(i1)>):  // pred: ^bb9
      %18 = "runtime.accept_transfer"(%arg0, %17) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%18)[^bb11, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb11(%19: i1):  // pred: ^bb10
      cf.br ^bb8(%19 : i1)
    ^bb12(%20: !runtime.scope):  // pred: ^bb7
      %21 = call @control_4(%20, %arg1, %arg2, %1) : (!runtime.scope, !gs, !gs, ui64) -> !exec.outcome<(i1)>
      %22 = "runtime.exit_scope"(%20, %21) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%22)[^bb13, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb13(%23: !runtime.transfer<(i1)>):  // pred: ^bb12
      %24 = "runtime.accept_transfer"(%arg0, %23) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%24)[^bb14, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb14(%25: i1):  // pred: ^bb13
      cf.br ^bb8(%25 : i1)
    }
    func.func private @control_2(%arg0: !runtime.scope, %arg1: !gs, %arg2: !gs, %arg3: ui64) -> !exec.outcome<(i1)> attributes {no_inline, runtime.region} {
      %0 = "exec.apply"(%arg0) <{binding = @index_constant, parameters = ["0"], site = "zero"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1: ui64):  // pred: ^bb0
      %2 = "exec.boolean"(%arg0) <{site = "yes", value = true}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%3: !exec.stop):  // 5 preds: ^bb0, ^bb1, ^bb3, ^bb7, ^bb9
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(i1)>
      return %4 : !exec.outcome<(i1)>
    ^bb3(%5: i1):  // pred: ^bb1
      %6 = "exec.range"(%arg0, %1, %arg3) <{site = "elements"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<(i64, i64)>) -> ()
    ^bb4(%7: i64, %8: i64):  // pred: ^bb3
      %9 = "runtime.borrow_transfer"(%arg0, %5) : (!runtime.scope, i1) -> !runtime.transfer<(i1)>
      cf.br ^bb5(%7, %9 : i64, !runtime.transfer<(i1)>)
    ^bb5(%10: i64, %11: !runtime.transfer<(i1)>):  // 2 preds: ^bb4, ^bb8
      %12 = arith.cmpi ult, %10, %8 : i64
      cf.cond_br %12, ^bb6, ^bb7(%11 : !runtime.transfer<(i1)>)
    ^bb6:  // pred: ^bb5
      %13 = "runtime.iteration"(%arg0, %10) <{site = "elements"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%13)[^bb10, ^bb9] : (!exec.outcome<(ui64)>) -> ()
    ^bb7(%14: !runtime.transfer<(i1)>):  // pred: ^bb5
      %15 = "runtime.accept_transfer"(%arg0, %14) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%15)[^bb13, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb8(%16: !runtime.transfer<(i1)>):  // pred: ^bb12
      %c1_i64 = arith.constant 1 : i64
      %17 = arith.addi %10, %c1_i64 : i64
      cf.br ^bb5(%17, %16 : i64, !runtime.transfer<(i1)>)
    ^bb9(%18: !exec.stop):  // 3 preds: ^bb6, ^bb10, ^bb11
      "runtime.release_transfer"(%11) : (!runtime.transfer<(i1)>) -> ()
      cf.br ^bb2(%18 : !exec.stop)
    ^bb10(%19: ui64):  // pred: ^bb6
      %20 = "runtime.transfer_values"(%11) : (!runtime.transfer<(i1)>) -> i1
      %21 = "runtime.enter_scope"(%arg0, %10, %19, %20, %arg1, %arg2) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 4>, site = "elements"}> : (!runtime.scope, i64, ui64, i1, !gs, !gs) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%21)[^bb11, ^bb9] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb11(%22: !runtime.scope):  // pred: ^bb10
      %23 = call @control_3(%22, %19, %20, %arg1, %arg2) : (!runtime.scope, ui64, i1, !gs, !gs) -> !exec.outcome<(i1)>
      %24 = "runtime.exit_scope"(%22, %23) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%24)[^bb12, ^bb9] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb12(%25: !runtime.transfer<(i1)>):  // pred: ^bb11
      "runtime.release_transfer"(%11) : (!runtime.transfer<(i1)>) -> ()
      cf.br ^bb8(%25 : !runtime.transfer<(i1)>)
    ^bb13(%26: i1):  // pred: ^bb7
      %27 = "exec.complete"(%arg0, %26) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      return %27 : !exec.outcome<(i1)>
    }
    func.func private @control_3(%arg0: !runtime.scope, %arg1: ui64, %arg2: i1, %arg3: !gs, %arg4: !gs) -> !exec.outcome<(i1)> attributes {no_inline, runtime.region} {
      %0 = "exec.apply"(%arg0, %arg3, %arg1) <{binding = @curve_get, parameters = [], site = "l"}> : (!runtime.scope, !gs, ui64) -> !exec.outcome<(!g)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!g)>) -> ()
    ^bb1(%1: !g):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %arg4, %arg1) <{binding = @curve_get, parameters = [], site = "r"}> : (!runtime.scope, !gs, ui64) -> !exec.outcome<(!g)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(!g)>) -> ()
    ^bb2(%3: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(i1)>
      return %4 : !exec.outcome<(i1)>
    ^bb3(%5: !g):  // pred: ^bb1
      %6 = "exec.apply"(%arg0, %1, %5) <{binding = @curve_equal, parameters = [], site = "eq"}> : (!runtime.scope, !g, !g) -> !exec.outcome<(i1)>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb4(%7: i1):  // pred: ^bb3
      %8 = "exec.apply"(%arg0, %arg2, %7) <{binding = @bool_and, parameters = [], site = "next"}> : (!runtime.scope, i1, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%8)[^bb5, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb5(%9: i1):  // pred: ^bb4
      %10 = "exec.complete"(%arg0, %9) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      return %10 : !exec.outcome<(i1)>
    }
    func.func private @control_4(%arg0: !runtime.scope, %arg1: !gs, %arg2: !gs, %arg3: ui64) -> !exec.outcome<(i1)> attributes {no_inline, runtime.region} {
      %0 = "exec.boolean"(%arg0) <{site = "no", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1: i1):  // pred: ^bb0
      %2 = "exec.complete"(%arg0, %1) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      return %2 : !exec.outcome<(i1)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(i1)>
      return %4 : !exec.outcome<(i1)>
    }














  "protocol.func"() ({ ^entry(%n:ui64,%g:!gs,%commitment:!g,%a:!fs,%rng:!r,%coins:!s):
    %sample:2 = "protocol.local_call"(%rng) {callee=@draw,role="P",site="sample"} : (!r)->(!f,!r)
    %prep:2 = "protocol.local_call"(%sample#0) {callee=@inverse,role="P",site="prep"} : (!f)->(!f,i1)
    %salt = protocol.exchange %sample#0 {sender="P",receiver="V",site="salt"} : !f
    %vprep:2 = "protocol.local_call"(%salt) {callee=@inverse,role="V",site="vprep"} : (!f)->(!f,i1)
    protocol.guard %vprep#1 {owner="V",site="nonzero_salt"}
    %scaled = "protocol.local_call"(%a,%prep#0) {callee=@scale_vector,role="P",site="scaled"} : (!fs,!f)->(!fs)
    %scaled_commitment = algebra.group_scale %commitment,%vprep#0 : (!g,!f)->!g
    %state:6 = "protocol.repeat"(%n,%scaled,%g,%g,%scaled_commitment,%prep#1,%sample#1,%coins) ({
    ^round(%i:ui64,%a0:!fs,%gp:!gs,%gv:!gs,%claim:!g,%complete:i1,%round_rng:!r,%random:!s):
    %cross:2 = "protocol.local_call"(%a0,%gp) {callee=@cross,role="P",site="cross"} : (!fs,!gs)->(!g,!g)
    %left = protocol.exchange %cross#0 {sender="P",receiver="V",site="left"} : !g
    %right = protocol.exchange %cross#1 {sender="P",receiver="V",site="right"} : !g
    %round_sample:2 = "protocol.local_call"(%round_rng) {callee=@draw,role="P",site="round_randomness"} : (!r)->(!f,!r)
    %round_salt = protocol.exchange %round_sample#0 {sender="P",receiver="V",site="round_salt"} : !f
    %c = "protocol.query"(%random) {method="draw",owner="V",site="draw"} : (!s)->!f
    %x = protocol.exchange %c {sender="V",receiver="P",site="challenge"} : !f
    %pi:2 = "protocol.local_call"(%x) {callee=@inverse,role="P",site="pi"} : (!f)->(!f,i1)
    %vi:2 = "protocol.local_call"(%c) {callee=@inverse,role="V",site="vi"} : (!f)->(!f,i1)
    protocol.guard %vi#1 {owner="V",site="nonzero_challenge"}
    %ready = arith.andi %complete,%pi#1 : i1
    %anext = "protocol.local_call"(%a0,%x,%pi#0) {callee=@fold_field,role="P",site="anext"} : (!fs,!f,!f)->(!fs)
    %gnext = "protocol.local_call"(%gp,%pi#0,%x) {callee=@fold_group,role="P",site="gnext"} : (!gs,!f,!f)->(!gs)
    %expected = "protocol.local_call"(%gv,%vi#0,%c) {callee=@fold_group,role="V",site="expected"} : (!gs,!f,!f)->(!gs)
    %received = protocol.exchange %gnext {sender="P",receiver="V",site="received"} : !gs
    %same = "protocol.local_call"(%received,%expected) {callee=@same_groups,role="V",site="same"} : (!gs,!gs)->(i1)
    protocol.guard %same {owner="V",site="received_groups"}
    %xx = algebra.field_multiply %c,%c : (!f,!f)->!f
    %yy = algebra.field_multiply %vi#0,%vi#0 : (!f,!f)->!f
    %lterm = algebra.group_scale %left,%xx : (!g,!f)->!g
    %rterm = algebra.group_scale %right,%yy : (!g,!f)->!g
    %middle = algebra.group_add %claim,%lterm : (!g,!g)->!g
    %next = algebra.group_add %middle,%rterm : (!g,!g)->!g
    "protocol.yield"(%anext,%gnext,%received,%next,%ready,%round_sample#1) : (!fs,!gs,!gs,!g,i1,!r)->()
    }) {site="rounds",carried=6:i64,maximum=8:i64,roles=["P","V"],carried_roles=[["P"],["P"],["V"],["V"],["P"],["P"]]} : (ui64,!fs,!gs,!gs,!g,i1,!r,!s)->(!fs,!gs,!gs,!g,i1,!r)
    %final = protocol.exchange %state#0 {sender="P",receiver="V",site="final"} : !fs
    %actual = "protocol.local_call"(%final,%state#2) {callee=@msm,role="V",site="actual"} : (!fs,!gs)->(!g)
    %accepted = algebra.group_equal %actual,%state#3 : (!g,!g)->i1
    "protocol.return"(%accepted,%state#4,%state#5) : (i1,i1,!r)->()
  }) {sym_name="fold",function_type=(ui64,!gs,!g,!fs,!r,!s)->(i1,i1,!r),roles=["P","V"],input_roles=[["P","V"],["P","V"],["V"],["P"],["P"],["V"]],output_roles=[["V"],["P"],["P"]]} : ()->()
  "protocol.func"() ({ ^entry(%n:ui64,%g:!gs,%commitment:!g,%a:!fs,%rng:!r,%coins:!s):
    %sample:2 = "protocol.local_call"(%rng) {callee=@draw,role="P",site="sample"} : (!r)->(!f,!r)
    %prep:2 = "protocol.local_call"(%sample#0) {callee=@inverse,role="P",site="prep"} : (!f)->(!f,i1)
    %salt = protocol.exchange %sample#0 {sender="P",receiver="V",site="salt"} : !f
    %vprep:2 = "protocol.local_call"(%salt) {callee=@inverse,role="V",site="vprep"} : (!f)->(!f,i1)
    protocol.guard %vprep#1 {owner="V",site="nonzero_salt"}
    %scaled = "protocol.local_call"(%a,%prep#0) {callee=@scale_vector,role="P",site="scaled"} : (!fs,!f)->(!fs)
    %scaled_commitment = algebra.group_scale %commitment,%vprep#0 : (!g,!f)->!g
    %empty_a = "protocol.local_call"() {callee=@empty_field,role="P",site="empty_a"} : ()->(!fs)
    %empty_p = "protocol.local_call"() {callee=@empty_group,role="P",site="empty_p"} : ()->(!gs)
    %empty_v = "protocol.local_call"() {callee=@empty_group,role="V",site="empty_v"} : ()->(!gs)
    %zero = algebra.field_subtract %salt,%salt : (!f,!f)->!f
    %identity = algebra.group_scale %commitment,%zero : (!g,!f)->!g
    %state:6 = "protocol.repeat"(%n,%empty_a,%empty_p,%empty_v,%identity,%identity,%sample#1,%scaled,%g,%coins) ({
    ^round(%i:ui64,%acc:!fs,%gp:!gs,%gv:!gs,%sum:!g,%weighted:!g,%round_rng:!r,%coefficients:!fs,%bases:!gs,%random:!s):
    %ai = "protocol.local_call"(%coefficients,%i) {callee=@get_field,role="P",site="ai"} : (!fs,ui64)->(!f)
    %gi = "protocol.local_call"(%bases,%i) {callee=@get_group,role="P",site="gi"} : (!gs,ui64)->(!g)
    %term = algebra.group_scale %gi,%ai : (!g,!f)->!g
    %contribution = protocol.exchange %term {sender="P",receiver="V",site="contribution"} : !g
    %round_sample:2 = "protocol.local_call"(%round_rng) {callee=@draw,role="P",site="round_randomness"} : (!r)->(!f,!r)
    %round_salt = protocol.exchange %round_sample#0 {sender="P",receiver="V",site="round_salt"} : !f
    %c = "protocol.query"(%random) {method="draw",owner="V",site="draw"} : (!s)->!f
    %x = protocol.exchange %c {sender="V",receiver="P",site="challenge"} : !f
    %weight = algebra.field_multiply %ai,%x : (!f,!f)->!f
    %anext = "protocol.local_call"(%acc,%weight) {callee=@append_field,role="P",site="anext"} : (!fs,!f)->(!fs)
    %gnext = "protocol.local_call"(%gp,%gi) {callee=@append_group,role="P",site="gnext"} : (!gs,!g)->(!gs)
    %base = "protocol.local_call"(%bases,%i) {callee=@get_group,role="V",site="base"} : (!gs,ui64)->(!g)
    %expected = "protocol.local_call"(%gv,%base) {callee=@append_group,role="V",site="expected"} : (!gs,!g)->(!gs)
    %received = protocol.exchange %gnext {sender="P",receiver="V",site="received"} : !gs
    %same = "protocol.local_call"(%received,%expected) {callee=@same_groups,role="V",site="same"} : (!gs,!gs)->(i1)
    protocol.guard %same {owner="V",site="received_groups"}
    %sum_next = algebra.group_add %sum,%contribution : (!g,!g)->!g
    %weighted_term = algebra.group_scale %contribution,%c : (!g,!f)->!g
    %weighted_next = algebra.group_add %weighted,%weighted_term : (!g,!g)->!g
    "protocol.yield"(%anext,%gnext,%received,%sum_next,%weighted_next,%round_sample#1) : (!fs,!gs,!gs,!g,!g,!r)->()
    }) {site="rounds",carried=6:i64,maximum=32:i64,roles=["P","V"],carried_roles=[["P"],["P"],["V"],["V"],["V"],["P"]]} : (ui64,!fs,!gs,!gs,!g,!g,!r,!fs,!gs,!s)->(!fs,!gs,!gs,!g,!g,!r)
    %final = protocol.exchange %state#0 {sender="P",receiver="V",site="final"} : !fs
    %actual = "protocol.local_call"(%final,%state#2) {callee=@msm,role="V",site="actual"} : (!fs,!gs)->(!g)
    %weighted_ok = algebra.group_equal %actual,%state#4 : (!g,!g)->i1
    %claim_ok = algebra.group_equal %state#3,%scaled_commitment : (!g,!g)->i1
    %accepted = arith.andi %weighted_ok,%claim_ok : i1
    "protocol.return"(%accepted,%prep#1,%state#5) : (i1,i1,!r)->()
  }) {sym_name="batch",function_type=(ui64,!gs,!g,!fs,!r,!s)->(i1,i1,!r),roles=["P","V"],input_roles=[["P","V"],["P","V"],["V"],["P"],["P"],["V"]],output_roles=[["V"],["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
