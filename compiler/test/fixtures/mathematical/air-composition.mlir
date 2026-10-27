// A full-trace transition check, extension LDE, opening quotient, fold and Merkle opening.
// This demonstrates composition, not a complete succinct AIR/FRI proof system.
!b = !algebra.field<"koala-bear">
!bv = !algebra.field_vector<"koala-bear">
!e = !algebra.field<"koala-bear.ext8-binomial3">
!ev = !algebra.field_vector<"koala-bear.ext8-binomial3">
!poly = !poly.univariate<"koala-bear.ext8-binomial3">
!root = !commitment.vector<"rows.merkle-keccak256.koala-bear.ext8-binomial3/0","commitment">
!path = !commitment.vector<"rows.merkle-keccak256.koala-bear.ext8-binomial3/0","proof">
!state = !commitment.vector<"rows.merkle-keccak256.koala-bear.ext8-binomial3/0","opening_state">
!rng = !protocol.service_ref<"random.koala-bear.ext8-binomial3/0">
module { "protocol.module"() ({
"runtime.binding"() {sym_name="index_constant",contract="index.constant",arguments=[],implementation=""} : ()->()
"runtime.binding"() {sym_name="field_constant",contract="field.constant",arguments=["koala-bear.ext8-binomial3"],implementation=""} : ()->()
"runtime.binding"() {sym_name="base_vector_length",contract="vector.length",arguments=["koala-bear"],implementation=""} : ()->()
"runtime.binding"() {sym_name="index_equal",contract="index.equal",arguments=[],implementation=""} : ()->()
"runtime.binding"() {sym_name="vector_embed",contract="vector.embed",arguments=["koala-bear.ext8-binomial3"],implementation=""} : ()->()
"runtime.binding"() {sym_name="poly_coset_interpolate",contract="poly.coset_interpolate",arguments=["koala-bear.ext8-binomial3"],implementation=""} : ()->()
"runtime.binding"() {sym_name="index_mul",contract="index.mul",arguments=[],implementation=""} : ()->()
"runtime.binding"() {sym_name="poly_coset_evaluate",contract="poly.coset_evaluate",arguments=["koala-bear.ext8-binomial3"],implementation=""} : ()->()
"runtime.binding"() {sym_name="poly_univariate_evaluate",contract="poly.univariate_evaluate",arguments=["koala-bear.ext8-binomial3"],implementation=""} : ()->()
"runtime.binding"() {sym_name="poly_opening_quotient",contract="poly.opening_quotient",arguments=["koala-bear.ext8-binomial3"],implementation=""} : ()->()
"runtime.binding"() {sym_name="poly_even_odd_fold",contract="poly.even_odd_fold",arguments=["koala-bear.ext8-binomial3"],implementation=""} : ()->()
"runtime.binding"() {sym_name="index_sub",contract="index.sub",arguments=[],implementation=""} : ()->()
"runtime.binding"() {sym_name="base_vector_get",contract="vector.get",arguments=["koala-bear"],implementation=""} : ()->()
"runtime.binding"() {sym_name="base_field_equal",contract="field.equal",arguments=["koala-bear"],implementation=""} : ()->()
"runtime.binding"() {sym_name="base_vector_slice",contract="vector.slice",arguments=["koala-bear"],implementation=""} : ()->()
"runtime.binding"() {sym_name="base_vector_fill",contract="vector.fill",arguments=["koala-bear"],implementation=""} : ()->()
"runtime.binding"() {sym_name="base_vector_add",contract="vector.add",arguments=["koala-bear"],implementation=""} : ()->()
"runtime.binding"() {sym_name="base_vector_equal",contract="vector.equal",arguments=["koala-bear"],implementation=""} : ()->()
"runtime.binding"() {sym_name="bool_and",contract="bool.and",arguments=[],implementation=""} : ()->()
"runtime.binding"() {sym_name="oracle_commit",contract="oracle.commit",arguments=["rows.merkle-keccak256.koala-bear.ext8-binomial3/0"],implementation=""} : ()->()
"runtime.binding"() {sym_name="oracle_open",contract="oracle.open",arguments=["rows.merkle-keccak256.koala-bear.ext8-binomial3/0"],implementation=""} : ()->()
"runtime.binding"() {sym_name="vector_slice",contract="vector.slice",arguments=["koala-bear.ext8-binomial3"],implementation=""} : ()->()
"runtime.binding"() {sym_name="vector_equal",contract="vector.equal",arguments=["koala-bear.ext8-binomial3"],implementation=""} : ()->()
"runtime.binding"() {sym_name="oracle_check",contract="oracle.check",arguments=["rows.merkle-keccak256.koala-bear.ext8-binomial3/0"],implementation=""} : ()->()

    func.func @fold(%arg0: !runtime.scope, %arg1: !bv, %arg2: !e, %arg3: !e, %arg4: ui64) -> !exec.outcome<(!ev)> attributes {no_inline, runtime.origin = ["fold", []]} {
      %0 = "exec.apply"(%arg0) <{binding = @index_constant, parameters = ["2"], site = "two"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1: ui64):  // pred: ^bb0
      %2 = "exec.apply"(%arg0) <{binding = @field_constant, parameters = ["1"], site = "one"}> : (!runtime.scope) -> !exec.outcome<(!e)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(!e)>) -> ()
    ^bb2(%3: !exec.stop):  // 19 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb8, ^bb9, ^bb10, ^bb11, ^bb12, ^bb14, ^bb15, ^bb17, ^bb18, ^bb19, ^bb20, ^bb21, ^bb22
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!ev)>
      return %4 : !exec.outcome<(!ev)>
    ^bb3(%5: !e):  // pred: ^bb1
      %6 = "exec.apply"(%arg0) <{binding = @field_constant, parameters = ["0"], site = "zero"}> : (!runtime.scope) -> !exec.outcome<(!e)>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<(!e)>) -> ()
    ^bb4(%7: !e):  // pred: ^bb3
      %8 = "exec.apply"(%arg0, %arg1) <{binding = @base_vector_length, parameters = [], site = "size"}> : (!runtime.scope, !bv) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%8)[^bb5, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%9: ui64):  // pred: ^bb4
      %10 = "exec.apply"(%arg0, %9, %arg4) <{binding = @index_equal, parameters = [], site = "shape"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%10)[^bb6, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb6(%11: i1):  // pred: ^bb5
      %12 = "exec.test"(%arg0, %11) <{site = "trace_shape"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%12)[^bb7, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb7(%13: i1):  // pred: ^bb6
      cf.cond_br %13, ^bb8, ^bb9
    ^bb8:  // pred: ^bb7
      %14 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "trace_shape"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%14)[^bb11, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb9:  // pred: ^bb7
      %15 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "trace_shape"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%15)[^bb14, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb10:  // 2 preds: ^bb13, ^bb16
      %16 = "exec.apply"(%arg0, %arg1) <{binding = @vector_embed, parameters = [], site = "embedded"}> : (!runtime.scope, !bv) -> !exec.outcome<(!ev)>
      "exec.dispatch"(%16)[^bb17, ^bb2] : (!exec.outcome<(!ev)>) -> ()
    ^bb11(%17: !runtime.scope):  // pred: ^bb8
      %18 = call @control_0(%17) : (!runtime.scope) -> !exec.outcome<>
      %19 = "runtime.exit_scope"(%17, %18) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%19)[^bb12, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb12(%20: !runtime.transfer<>):  // pred: ^bb11
      %21 = "runtime.accept_transfer"(%arg0, %20) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%21)[^bb13, ^bb2] : (!exec.outcome<>) -> ()
    ^bb13:  // pred: ^bb12
      cf.br ^bb10
    ^bb14(%22: !runtime.scope):  // pred: ^bb9
      %23 = call @control_1(%22) : (!runtime.scope) -> !exec.outcome<>
      %24 = "runtime.exit_scope"(%22, %23) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%24)[^bb15, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb15(%25: !runtime.transfer<>):  // pred: ^bb14
      %26 = "runtime.accept_transfer"(%arg0, %25) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%26)[^bb16, ^bb2] : (!exec.outcome<>) -> ()
    ^bb16:  // pred: ^bb15
      cf.br ^bb10
    ^bb17(%27: !ev):  // pred: ^bb10
      %28 = "exec.apply"(%arg0, %27, %5) <{binding = @poly_coset_interpolate, parameters = [], site = "polynomial"}> : (!runtime.scope, !ev, !e) -> !exec.outcome<(!poly)>
      "exec.dispatch"(%28)[^bb18, ^bb2] : (!exec.outcome<(!poly)>) -> ()
    ^bb18(%29: !poly):  // pred: ^bb17
      %30 = "exec.apply"(%arg0, %arg4, %1) <{binding = @index_mul, parameters = [], site = "lde_size"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%30)[^bb19, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb19(%31: ui64):  // pred: ^bb18
      %32 = "exec.apply"(%arg0, %29, %arg2, %31) <{binding = @poly_coset_evaluate, parameters = [], site = "lde"}> : (!runtime.scope, !poly, !e, ui64) -> !exec.outcome<(!ev)>
      "exec.dispatch"(%32)[^bb20, ^bb2] : (!exec.outcome<(!ev)>) -> ()
    ^bb20(%33: !ev):  // pred: ^bb19
      %34 = "exec.apply"(%arg0, %29, %7) <{binding = @poly_univariate_evaluate, parameters = [], site = "at_zero"}> : (!runtime.scope, !poly, !e) -> !exec.outcome<(!e)>
      "exec.dispatch"(%34)[^bb21, ^bb2] : (!exec.outcome<(!e)>) -> ()
    ^bb21(%35: !e):  // pred: ^bb20
      %36 = "exec.apply"(%arg0, %33, %arg2, %7, %35) <{binding = @poly_opening_quotient, parameters = [], site = "quotient"}> : (!runtime.scope, !ev, !e, !e, !e) -> !exec.outcome<(!ev)>
      "exec.dispatch"(%36)[^bb22, ^bb2] : (!exec.outcome<(!ev)>) -> ()
    ^bb22(%37: !ev):  // pred: ^bb21
      %38 = "exec.apply"(%arg0, %37, %arg2, %arg3) <{binding = @poly_even_odd_fold, parameters = [], site = "folded"}> : (!runtime.scope, !ev, !e, !e) -> !exec.outcome<(!ev)>
      "exec.dispatch"(%38)[^bb23, ^bb2] : (!exec.outcome<(!ev)>) -> ()
    ^bb23(%39: !ev):  // pred: ^bb22
      %40 = "exec.returned"(%39) : (!ev) -> !exec.outcome<(!ev)>
      return %40 : !exec.outcome<(!ev)>
    }
    func.func private @control_0(%arg0: !runtime.scope) -> !exec.outcome<> attributes {no_inline, runtime.region} {
      %0 = "exec.complete"(%arg0) : (!runtime.scope) -> !exec.outcome<>
      return %0 : !exec.outcome<>
    }
    func.func private @control_1(%arg0: !runtime.scope) -> !exec.outcome<> attributes {no_inline, runtime.region} {
      %0 = "exec.reject"(%arg0) <{reason = "reject", site = "trace_shape_reject"}> : (!runtime.scope) -> !exec.stop
      cf.br ^bb1(%0 : !exec.stop)
    ^bb1(%1: !exec.stop):  // pred: ^bb0
      %2 = "exec.failed"(%1) : (!exec.stop) -> !exec.outcome<>
      return %2 : !exec.outcome<>
    }
    func.func @transitions(%arg0: !runtime.scope, %arg1: !bv, %arg2: !b, %arg3: !b, %arg4: ui64) -> !exec.outcome<(i1)> attributes {no_inline, runtime.origin = ["transitions", []]} {
      %0 = "exec.apply"(%arg0) <{binding = @index_constant, parameters = ["0"], site = "zero"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1: ui64):  // pred: ^bb0
      %2 = "exec.apply"(%arg0) <{binding = @index_constant, parameters = ["1"], site = "one"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%3: !exec.stop):  // 20 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb7, ^bb8, ^bb9, ^bb10, ^bb11, ^bb13, ^bb14, ^bb16, ^bb17, ^bb18, ^bb19, ^bb20, ^bb21, ^bb22, ^bb23
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(i1)>
      return %4 : !exec.outcome<(i1)>
    ^bb3(%5: ui64):  // pred: ^bb1
      %6 = "exec.apply"(%arg0, %arg1) <{binding = @base_vector_length, parameters = [], site = "length"}> : (!runtime.scope, !bv) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%7: ui64):  // pred: ^bb3
      %8 = "exec.apply"(%arg0, %7, %arg4) <{binding = @index_equal, parameters = [], site = "shape"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%8)[^bb5, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb5(%9: i1):  // pred: ^bb4
      %10 = "exec.test"(%arg0, %9) <{site = "trace_shape"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%10)[^bb6, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb6(%11: i1):  // pred: ^bb5
      cf.cond_br %11, ^bb7, ^bb8
    ^bb7:  // pred: ^bb6
      %12 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "trace_shape"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%12)[^bb10, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb8:  // pred: ^bb6
      %13 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "trace_shape"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%13)[^bb13, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb9:  // 2 preds: ^bb12, ^bb15
      %14 = "exec.apply"(%arg0, %arg4, %5) <{binding = @index_sub, parameters = [], site = "count"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%14)[^bb16, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb10(%15: !runtime.scope):  // pred: ^bb7
      %16 = call @control_2(%15) : (!runtime.scope) -> !exec.outcome<>
      %17 = "runtime.exit_scope"(%15, %16) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%17)[^bb11, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb11(%18: !runtime.transfer<>):  // pred: ^bb10
      %19 = "runtime.accept_transfer"(%arg0, %18) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%19)[^bb12, ^bb2] : (!exec.outcome<>) -> ()
    ^bb12:  // pred: ^bb11
      cf.br ^bb9
    ^bb13(%20: !runtime.scope):  // pred: ^bb8
      %21 = call @control_3(%20) : (!runtime.scope) -> !exec.outcome<>
      %22 = "runtime.exit_scope"(%20, %21) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%22)[^bb14, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb14(%23: !runtime.transfer<>):  // pred: ^bb13
      %24 = "runtime.accept_transfer"(%arg0, %23) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%24)[^bb15, ^bb2] : (!exec.outcome<>) -> ()
    ^bb15:  // pred: ^bb14
      cf.br ^bb9
    ^bb16(%25: ui64):  // pred: ^bb9
      %26 = "exec.apply"(%arg0, %arg1, %1) <{binding = @base_vector_get, parameters = [], site = "first"}> : (!runtime.scope, !bv, ui64) -> !exec.outcome<(!b)>
      "exec.dispatch"(%26)[^bb17, ^bb2] : (!exec.outcome<(!b)>) -> ()
    ^bb17(%27: !b):  // pred: ^bb16
      %28 = "exec.apply"(%arg0, %27, %arg2) <{binding = @base_field_equal, parameters = [], site = "first_valid"}> : (!runtime.scope, !b, !b) -> !exec.outcome<(i1)>
      "exec.dispatch"(%28)[^bb18, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb18(%29: i1):  // pred: ^bb17
      %30 = "exec.apply"(%arg0, %arg1, %1, %25) <{binding = @base_vector_slice, parameters = [], site = "left"}> : (!runtime.scope, !bv, ui64, ui64) -> !exec.outcome<(!bv)>
      "exec.dispatch"(%30)[^bb19, ^bb2] : (!exec.outcome<(!bv)>) -> ()
    ^bb19(%31: !bv):  // pred: ^bb18
      %32 = "exec.apply"(%arg0, %arg1, %5, %25) <{binding = @base_vector_slice, parameters = [], site = "right"}> : (!runtime.scope, !bv, ui64, ui64) -> !exec.outcome<(!bv)>
      "exec.dispatch"(%32)[^bb20, ^bb2] : (!exec.outcome<(!bv)>) -> ()
    ^bb20(%33: !bv):  // pred: ^bb19
      %34 = "exec.apply"(%arg0, %arg3, %25) <{binding = @base_vector_fill, parameters = [], site = "steps"}> : (!runtime.scope, !b, ui64) -> !exec.outcome<(!bv)>
      "exec.dispatch"(%34)[^bb21, ^bb2] : (!exec.outcome<(!bv)>) -> ()
    ^bb21(%35: !bv):  // pred: ^bb20
      %36 = "exec.apply"(%arg0, %31, %35) <{binding = @base_vector_add, parameters = [], site = "expected"}> : (!runtime.scope, !bv, !bv) -> !exec.outcome<(!bv)>
      "exec.dispatch"(%36)[^bb22, ^bb2] : (!exec.outcome<(!bv)>) -> ()
    ^bb22(%37: !bv):  // pred: ^bb21
      %38 = "exec.apply"(%arg0, %37, %33) <{binding = @base_vector_equal, parameters = [], site = "rows_valid"}> : (!runtime.scope, !bv, !bv) -> !exec.outcome<(i1)>
      "exec.dispatch"(%38)[^bb23, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb23(%39: i1):  // pred: ^bb22
      %40 = "exec.apply"(%arg0, %29, %39) <{binding = @bool_and, parameters = [], site = "valid"}> : (!runtime.scope, i1, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%40)[^bb24, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb24(%41: i1):  // pred: ^bb23
      %42 = "exec.returned"(%41) : (i1) -> !exec.outcome<(i1)>
      return %42 : !exec.outcome<(i1)>
    }
    func.func private @control_2(%arg0: !runtime.scope) -> !exec.outcome<> attributes {no_inline, runtime.region} {
      %0 = "exec.complete"(%arg0) : (!runtime.scope) -> !exec.outcome<>
      return %0 : !exec.outcome<>
    }
    func.func private @control_3(%arg0: !runtime.scope) -> !exec.outcome<> attributes {no_inline, runtime.region} {
      %0 = "exec.reject"(%arg0) <{reason = "reject", site = "trace_shape_reject"}> : (!runtime.scope) -> !exec.stop
      cf.br ^bb1(%0 : !exec.stop)
    ^bb1(%1: !exec.stop):  // pred: ^bb0
      %2 = "exec.failed"(%1) : (!exec.stop) -> !exec.outcome<>
      return %2 : !exec.outcome<>
    }
    func.func @open_fold(%arg0: !runtime.scope, %arg1: !ev, %arg2: ui64) -> !exec.outcome<(!commitment.vector<"rows.merkle-keccak256.koala-bear.ext8-binomial3/0", "commitment">, !ev, !commitment.vector<"rows.merkle-keccak256.koala-bear.ext8-binomial3/0", "proof">)> attributes {no_inline, runtime.origin = ["open_fold", []]} {
      %0 = "exec.apply"(%arg0) <{binding = @index_constant, parameters = ["1"], site = "columns"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1: ui64):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %arg1, %1) <{binding = @oracle_commit, parameters = [], site = "tree"}> : (!runtime.scope, !ev, ui64) -> !exec.outcome<(!commitment.vector<"rows.merkle-keccak256.koala-bear.ext8-binomial3/0", "commitment">, !commitment.vector<"rows.merkle-keccak256.koala-bear.ext8-binomial3/0", "opening_state">)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(!commitment.vector<"rows.merkle-keccak256.koala-bear.ext8-binomial3/0", "commitment">, !commitment.vector<"rows.merkle-keccak256.koala-bear.ext8-binomial3/0", "opening_state">)>) -> ()
    ^bb2(%3: !exec.stop):  // 3 preds: ^bb0, ^bb1, ^bb3
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!commitment.vector<"rows.merkle-keccak256.koala-bear.ext8-binomial3/0", "commitment">, !ev, !commitment.vector<"rows.merkle-keccak256.koala-bear.ext8-binomial3/0", "proof">)>
      return %4 : !exec.outcome<(!commitment.vector<"rows.merkle-keccak256.koala-bear.ext8-binomial3/0", "commitment">, !ev, !commitment.vector<"rows.merkle-keccak256.koala-bear.ext8-binomial3/0", "proof">)>
    ^bb3(%5: !commitment.vector<"rows.merkle-keccak256.koala-bear.ext8-binomial3/0", "commitment">, %6: !commitment.vector<"rows.merkle-keccak256.koala-bear.ext8-binomial3/0", "opening_state">):  // pred: ^bb1
      %7 = "exec.apply"(%arg0, %6, %arg2) <{binding = @oracle_open, parameters = [], site = "opening"}> : (!runtime.scope, !commitment.vector<"rows.merkle-keccak256.koala-bear.ext8-binomial3/0", "opening_state">, ui64) -> !exec.outcome<(!ev, !commitment.vector<"rows.merkle-keccak256.koala-bear.ext8-binomial3/0", "proof">)>
      "exec.dispatch"(%7)[^bb4, ^bb2] : (!exec.outcome<(!ev, !commitment.vector<"rows.merkle-keccak256.koala-bear.ext8-binomial3/0", "proof">)>) -> ()
    ^bb4(%8: !ev, %9: !commitment.vector<"rows.merkle-keccak256.koala-bear.ext8-binomial3/0", "proof">):  // pred: ^bb3
      %10 = "exec.returned"(%5, %8, %9) : (!commitment.vector<"rows.merkle-keccak256.koala-bear.ext8-binomial3/0", "commitment">, !ev, !commitment.vector<"rows.merkle-keccak256.koala-bear.ext8-binomial3/0", "proof">) -> !exec.outcome<(!commitment.vector<"rows.merkle-keccak256.koala-bear.ext8-binomial3/0", "commitment">, !ev, !commitment.vector<"rows.merkle-keccak256.koala-bear.ext8-binomial3/0", "proof">)>
      return %10 : !exec.outcome<(!commitment.vector<"rows.merkle-keccak256.koala-bear.ext8-binomial3/0", "commitment">, !ev, !commitment.vector<"rows.merkle-keccak256.koala-bear.ext8-binomial3/0", "proof">)>
    }
    func.func @check_opening(%arg0: !runtime.scope, %arg1: !ev, %arg2: !commitment.vector<"rows.merkle-keccak256.koala-bear.ext8-binomial3/0", "commitment">, %arg3: !ev, %arg4: !commitment.vector<"rows.merkle-keccak256.koala-bear.ext8-binomial3/0", "proof">, %arg5: ui64, %arg6: ui64) -> !exec.outcome<(i1)> attributes {no_inline, runtime.origin = ["check_opening", []]} {
      %0 = "exec.apply"(%arg0) <{binding = @index_constant, parameters = ["1"], site = "one"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1: ui64):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %arg1, %arg5, %1) <{binding = @vector_slice, parameters = [], site = "expected"}> : (!runtime.scope, !ev, ui64, ui64) -> !exec.outcome<(!ev)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(!ev)>) -> ()
    ^bb2(%3: !exec.stop):  // 5 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(i1)>
      return %4 : !exec.outcome<(i1)>
    ^bb3(%5: !ev):  // pred: ^bb1
      %6 = "exec.apply"(%arg0, %5, %arg3) <{binding = @vector_equal, parameters = [], site = "row_valid"}> : (!runtime.scope, !ev, !ev) -> !exec.outcome<(i1)>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb4(%7: i1):  // pred: ^bb3
      %8 = "exec.apply"(%arg0, %arg2, %1, %arg6, %arg5, %arg3, %arg4) <{binding = @oracle_check, parameters = [], site = "path_valid"}> : (!runtime.scope, !commitment.vector<"rows.merkle-keccak256.koala-bear.ext8-binomial3/0", "commitment">, ui64, ui64, ui64, !ev, !commitment.vector<"rows.merkle-keccak256.koala-bear.ext8-binomial3/0", "proof">) -> !exec.outcome<(i1)>
      "exec.dispatch"(%8)[^bb5, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb5(%9: i1):  // pred: ^bb4
      %10 = "exec.apply"(%arg0, %7, %9) <{binding = @bool_and, parameters = [], site = "valid"}> : (!runtime.scope, i1, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%10)[^bb6, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb6(%11: i1):  // pred: ^bb5
      %12 = "exec.returned"(%11) : (i1) -> !exec.outcome<(i1)>
      return %12 : !exec.outcome<(i1)>
    }




"protocol.func"() ({ ^entry(%trace:!bv,%start:!b,%step:!b,%shift:!e,%n:ui64,%query:ui64,%random:!rng):
 %received = protocol.exchange %trace {sender="P",receiver="V",site="trace"} : !bv
 %q = "protocol.query"(%random) {owner="V",method="draw",site="draw"} : (!rng)->!e
 %challenge = protocol.exchange %q {sender="V",receiver="P",site="challenge"} : !e
 %echo = protocol.exchange %challenge {sender="P",receiver="V",site="challenge_echo"} : !e
 %folded = "protocol.local_call"(%trace,%shift,%challenge,%n) {callee=@fold,role="P",site="producer_fold"} : (!bv,!e,!e,ui64)->!ev
 %opened:3 = "protocol.local_call"(%folded,%query) {callee=@open_fold,role="P",site="open"} : (!ev,ui64)->(!root,!ev,!path)
 %root = protocol.exchange %opened#0 {sender="P",receiver="V",site="root"} : !root
 %row = protocol.exchange %opened#1 {sender="P",receiver="V",site="row"} : !ev
 %path = protocol.exchange %opened#2 {sender="P",receiver="V",site="path"} : !path
 %expected = "protocol.local_call"(%received,%shift,%q,%n) {callee=@fold,role="V",site="validator_fold"} : (!bv,!e,!e,ui64)->!ev
 %trace_ok = "protocol.local_call"(%received,%start,%step,%n) {callee=@transitions,role="V",site="transitions"} : (!bv,!b,!b,ui64)->i1
 %opening_ok = "protocol.local_call"(%expected,%root,%row,%path,%query,%n) {callee=@check_opening,role="V",site="opening"} : (!ev,!root,!ev,!path,ui64,ui64)->i1
 %echo_ok = algebra.field_equal %echo,%q : (!e,!e)->i1
 %checks = arith.andi %trace_ok,%opening_ok : i1
 %valid = arith.andi %checks,%echo_ok : i1
 "protocol.return"(%valid) : (i1)->()
}) {sym_name="main",function_type=(!bv,!b,!b,!e,ui64,ui64,!rng)->i1,roles=["P","V"],input_roles=[["P"],["V"],["V"],["P","V"],["P","V"],["P","V"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
