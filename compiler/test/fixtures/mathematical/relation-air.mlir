// Direct constraint checking deliberately discloses the witness in the proof.
!f = !algebra.field<"bls12-381.fr">
!v = !algebra.field_vector<"bls12-381.fr">
!trace = !data.sequence<!v>
!config = !data.variant<"variant:5b227a6b632e76617269616e742f30222c5b226578616d706c652f6169722d646174612f4c696e656172526563757272656e6365222c22636f656666696369656e7473222c226669656c643a626c7331322d3338312e6672222c5b2232222c2232225d2c5b2231222c2233225d2c5b2234225d2c5b2230222c2235225d5d5d">
module { "protocol.module"() ({
"runtime.binding"() {sym_name="index_constant",contract="index.constant",arguments=[],implementation=""} : ()->()
"runtime.binding"() {sym_name="sequence_length",contract="sequence.length",arguments=["vector:bls12-381.fr"],implementation=""} : ()->()
"runtime.binding"() {sym_name="index_less",contract="index.less",arguments=[],implementation=""} : ()->()
"runtime.binding"() {sym_name="vector_length",contract="vector.length",arguments=["bls12-381.fr"],implementation=""} : ()->()
"runtime.binding"() {sym_name="index_equal",contract="index.equal",arguments=[],implementation=""} : ()->()
"runtime.binding"() {sym_name="sequence_at",contract="sequence.at",arguments=["vector:bls12-381.fr"],implementation=""} : ()->()
"runtime.binding"() {sym_name="vector_get",contract="vector.get",arguments=["bls12-381.fr"],implementation=""} : ()->()
"runtime.binding"() {sym_name="field_equal",contract="field.equal",arguments=["bls12-381.fr"],implementation=""} : ()->()
"runtime.binding"() {sym_name="bool_and",contract="bool.and",arguments=[],implementation=""} : ()->()
"runtime.binding"() {sym_name="field_mul",contract="field.mul",arguments=["bls12-381.fr"],implementation=""} : ()->()
"runtime.binding"() {sym_name="field_add",contract="field.add",arguments=["bls12-381.fr"],implementation=""} : ()->()
relation.declare @relation {kind="external",key="example/air-data",revision="0",signature=(!config,!v,!trace)->i1,purposes=["parameter","statement","witness"]}
    func.func @validate(%arg0: !runtime.scope, %arg1: !config, %arg2: !v, %arg3: !trace) -> !exec.outcome<(i1)> attributes {no_inline, runtime.origin = ["validate", []]} {
      "exec.match"(%arg0, %arg1, %arg2, %arg3)[^bb2, ^bb3] <{alternatives = ["coefficients"], site = "configuration"}> : (!runtime.scope, !config, !v, !trace) -> ()
    ^bb1(%0: i1):  // pred: ^bb6
      %1 = "exec.returned"(%0) : (i1) -> !exec.outcome<(i1)>
      return %1 : !exec.outcome<(i1)>
    ^bb2(%2: !exec.stop):  // 4 preds: ^bb0, ^bb3, ^bb4, ^bb5
      %3 = "exec.failed"(%2) : (!exec.stop) -> !exec.outcome<(i1)>
      return %3 : !exec.outcome<(i1)>
    ^bb3(%4: !f, %5: !f, %6: !v, %7: !trace):  // pred: ^bb0
      %8 = "runtime.enter_scope"(%arg0, %4, %5, %6, %7) <{kind = "match", operandSegmentSizes = array<i32: 1, 0, 4>, selection = "coefficients", site = "configuration"}> : (!runtime.scope, !f, !f, !v, !trace) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%8)[^bb4, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb4(%9: !runtime.scope):  // pred: ^bb3
      %10 = call @control_0(%9, %4, %5, %6, %7) : (!runtime.scope, !f, !f, !v, !trace) -> !exec.outcome<(i1)>
      %11 = "runtime.exit_scope"(%9, %10) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%11)[^bb5, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb5(%12: !runtime.transfer<(i1)>):  // pred: ^bb4
      %13 = "runtime.accept_transfer"(%arg0, %12) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%13)[^bb6, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb6(%14: i1):  // pred: ^bb5
      cf.br ^bb1(%14 : i1)
    }
    func.func private @control_0(%arg0: !runtime.scope, %arg1: !f, %arg2: !f, %arg3: !v, %arg4: !trace) -> !exec.outcome<(i1)> attributes {no_inline, runtime.region} {
      %0 = "exec.apply"(%arg0) <{binding = @index_constant, parameters = ["0"], site = "zero"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1: ui64):  // pred: ^bb0
      %2 = "exec.apply"(%arg0) <{binding = @index_constant, parameters = ["1"], site = "one"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%3: !exec.stop):  // 49 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb8, ^bb10, ^bb11, ^bb12, ^bb13, ^bb14, ^bb16, ^bb17, ^bb19, ^bb20, ^bb22, ^bb23, ^bb24, ^bb25, ^bb26, ^bb28, ^bb29, ^bb31, ^bb32, ^bb33, ^bb35, ^bb36, ^bb37, ^bb38, ^bb39, ^bb41, ^bb42, ^bb44, ^bb45, ^bb46, ^bb47, ^bb48, ^bb49, ^bb50, ^bb54, ^bb56, ^bb60, ^bb61, ^bb62, ^bb63, ^bb64, ^bb65
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(i1)>
      return %4 : !exec.outcome<(i1)>
    ^bb3(%5: ui64):  // pred: ^bb1
      %6 = "exec.apply"(%arg0) <{binding = @index_constant, parameters = ["2"], site = "two"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%7: ui64):  // pred: ^bb3
      %8 = "exec.apply"(%arg0) <{binding = @index_constant, parameters = ["3"], site = "three"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%8)[^bb5, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%9: ui64):  // pred: ^bb4
      %10 = "exec.apply"(%arg0) <{binding = @index_constant, parameters = ["4"], site = "four"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%10)[^bb6, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb6(%11: ui64):  // pred: ^bb5
      %12 = "exec.apply"(%arg0, %arg4) <{binding = @sequence_length, parameters = [], site = "height"}> : (!runtime.scope, !trace) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%12)[^bb7, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb7(%13: ui64):  // pred: ^bb6
      %14 = "exec.apply"(%arg0, %1, %13) <{binding = @index_less, parameters = [], site = "nonempty"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%14)[^bb8, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb8(%15: i1):  // pred: ^bb7
      %16 = "exec.test"(%arg0, %15) <{site = "trace_nonempty"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%16)[^bb9, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb9(%17: i1):  // pred: ^bb8
      cf.cond_br %17, ^bb10, ^bb11
    ^bb10:  // pred: ^bb9
      %18 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "trace_nonempty"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%18)[^bb13, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb11:  // pred: ^bb9
      %19 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "trace_nonempty"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%19)[^bb16, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb12:  // 2 preds: ^bb15, ^bb18
      %20 = "exec.apply"(%arg0, %arg3) <{binding = @vector_length, parameters = [], site = "input_count"}> : (!runtime.scope, !v) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%20)[^bb19, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb13(%21: !runtime.scope):  // pred: ^bb10
      %22 = call @control_1(%21) : (!runtime.scope) -> !exec.outcome<>
      %23 = "runtime.exit_scope"(%21, %22) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%23)[^bb14, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb14(%24: !runtime.transfer<>):  // pred: ^bb13
      %25 = "runtime.accept_transfer"(%arg0, %24) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%25)[^bb15, ^bb2] : (!exec.outcome<>) -> ()
    ^bb15:  // pred: ^bb14
      cf.br ^bb12
    ^bb16(%26: !runtime.scope):  // pred: ^bb11
      %27 = call @control_2(%26) : (!runtime.scope) -> !exec.outcome<>
      %28 = "runtime.exit_scope"(%26, %27) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%28)[^bb17, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb17(%29: !runtime.transfer<>):  // pred: ^bb16
      %30 = "runtime.accept_transfer"(%arg0, %29) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%30)[^bb18, ^bb2] : (!exec.outcome<>) -> ()
    ^bb18:  // pred: ^bb17
      cf.br ^bb12
    ^bb19(%31: ui64):  // pred: ^bb12
      %32 = "exec.apply"(%arg0, %31, %11) <{binding = @index_equal, parameters = [], site = "four_inputs"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%32)[^bb20, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb20(%33: i1):  // pred: ^bb19
      %34 = "exec.test"(%arg0, %33) <{site = "boundary_arity"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%34)[^bb21, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb21(%35: i1):  // pred: ^bb20
      cf.cond_br %35, ^bb22, ^bb23
    ^bb22:  // pred: ^bb21
      %36 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "boundary_arity"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%36)[^bb25, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb23:  // pred: ^bb21
      %37 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "boundary_arity"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%37)[^bb28, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb24:  // 2 preds: ^bb27, ^bb30
      %38 = "exec.apply"(%arg0, %arg4, %1) <{binding = @sequence_at, parameters = [], site = "first"}> : (!runtime.scope, !trace, ui64) -> !exec.outcome<(!v)>
      "exec.dispatch"(%38)[^bb31, ^bb2] : (!exec.outcome<(!v)>) -> ()
    ^bb25(%39: !runtime.scope):  // pred: ^bb22
      %40 = call @control_3(%39) : (!runtime.scope) -> !exec.outcome<>
      %41 = "runtime.exit_scope"(%39, %40) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%41)[^bb26, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb26(%42: !runtime.transfer<>):  // pred: ^bb25
      %43 = "runtime.accept_transfer"(%arg0, %42) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%43)[^bb27, ^bb2] : (!exec.outcome<>) -> ()
    ^bb27:  // pred: ^bb26
      cf.br ^bb24
    ^bb28(%44: !runtime.scope):  // pred: ^bb23
      %45 = call @control_4(%44) : (!runtime.scope) -> !exec.outcome<>
      %46 = "runtime.exit_scope"(%44, %45) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%46)[^bb29, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb29(%47: !runtime.transfer<>):  // pred: ^bb28
      %48 = "runtime.accept_transfer"(%arg0, %47) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%48)[^bb30, ^bb2] : (!exec.outcome<>) -> ()
    ^bb30:  // pred: ^bb29
      cf.br ^bb24
    ^bb31(%49: !v):  // pred: ^bb24
      %50 = "exec.apply"(%arg0, %49) <{binding = @vector_length, parameters = [], site = "first_width"}> : (!runtime.scope, !v) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%50)[^bb32, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb32(%51: ui64):  // pred: ^bb31
      %52 = "exec.apply"(%arg0, %51, %7) <{binding = @index_equal, parameters = [], site = "first_shape"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%52)[^bb33, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb33(%53: i1):  // pred: ^bb32
      %54 = "exec.test"(%arg0, %53) <{site = "first_row"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%54)[^bb34, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb34(%55: i1):  // pred: ^bb33
      cf.cond_br %55, ^bb35, ^bb36
    ^bb35:  // pred: ^bb34
      %56 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "first_row"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%56)[^bb38, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb36:  // pred: ^bb34
      %57 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "first_row"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%57)[^bb41, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb37:  // 2 preds: ^bb40, ^bb43
      %58 = "exec.apply"(%arg0, %49, %1) <{binding = @vector_get, parameters = [], site = "initial_x"}> : (!runtime.scope, !v, ui64) -> !exec.outcome<(!f)>
      "exec.dispatch"(%58)[^bb44, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb38(%59: !runtime.scope):  // pred: ^bb35
      %60 = call @control_5(%59) : (!runtime.scope) -> !exec.outcome<>
      %61 = "runtime.exit_scope"(%59, %60) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%61)[^bb39, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb39(%62: !runtime.transfer<>):  // pred: ^bb38
      %63 = "runtime.accept_transfer"(%arg0, %62) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%63)[^bb40, ^bb2] : (!exec.outcome<>) -> ()
    ^bb40:  // pred: ^bb39
      cf.br ^bb37
    ^bb41(%64: !runtime.scope):  // pred: ^bb36
      %65 = call @control_6(%64) : (!runtime.scope) -> !exec.outcome<>
      %66 = "runtime.exit_scope"(%64, %65) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%66)[^bb42, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb42(%67: !runtime.transfer<>):  // pred: ^bb41
      %68 = "runtime.accept_transfer"(%arg0, %67) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%68)[^bb43, ^bb2] : (!exec.outcome<>) -> ()
    ^bb43:  // pred: ^bb42
      cf.br ^bb37
    ^bb44(%69: !f):  // pred: ^bb37
      %70 = "exec.apply"(%arg0, %49, %5) <{binding = @vector_get, parameters = [], site = "initial_y"}> : (!runtime.scope, !v, ui64) -> !exec.outcome<(!f)>
      "exec.dispatch"(%70)[^bb45, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb45(%71: !f):  // pred: ^bb44
      %72 = "exec.apply"(%arg0, %arg3, %1) <{binding = @vector_get, parameters = [], site = "expected_x"}> : (!runtime.scope, !v, ui64) -> !exec.outcome<(!f)>
      "exec.dispatch"(%72)[^bb46, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb46(%73: !f):  // pred: ^bb45
      %74 = "exec.apply"(%arg0, %arg3, %5) <{binding = @vector_get, parameters = [], site = "expected_y"}> : (!runtime.scope, !v, ui64) -> !exec.outcome<(!f)>
      "exec.dispatch"(%74)[^bb47, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb47(%75: !f):  // pred: ^bb46
      %76 = "exec.apply"(%arg0, %69, %73) <{binding = @field_equal, parameters = [], site = "start_x"}> : (!runtime.scope, !f, !f) -> !exec.outcome<(i1)>
      "exec.dispatch"(%76)[^bb48, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb48(%77: i1):  // pred: ^bb47
      %78 = "exec.apply"(%arg0, %71, %75) <{binding = @field_equal, parameters = [], site = "start_y"}> : (!runtime.scope, !f, !f) -> !exec.outcome<(i1)>
      "exec.dispatch"(%78)[^bb49, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb49(%79: i1):  // pred: ^bb48
      %80 = "exec.apply"(%arg0, %77, %79) <{binding = @bool_and, parameters = [], site = "start"}> : (!runtime.scope, i1, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%80)[^bb50, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb50(%81: i1):  // pred: ^bb49
      %82 = "exec.range"(%arg0, %5, %13) <{site = "transitions"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%82)[^bb51, ^bb2] : (!exec.outcome<(i64, i64)>) -> ()
    ^bb51(%83: i64, %84: i64):  // pred: ^bb50
      %85 = "runtime.borrow_transfer"(%arg0, %81, %69, %71) : (!runtime.scope, i1, !f, !f) -> !runtime.transfer<(i1, !f, !f)>
      cf.br ^bb52(%83, %85 : i64, !runtime.transfer<(i1, !f, !f)>)
    ^bb52(%86: i64, %87: !runtime.transfer<(i1, !f, !f)>):  // 2 preds: ^bb51, ^bb55
      %88 = arith.cmpi ult, %86, %84 : i64
      cf.cond_br %88, ^bb53, ^bb54(%87 : !runtime.transfer<(i1, !f, !f)>)
    ^bb53:  // pred: ^bb52
      %89 = "runtime.iteration"(%arg0, %86) <{site = "transitions"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%89)[^bb57, ^bb56] : (!exec.outcome<(ui64)>) -> ()
    ^bb54(%90: !runtime.transfer<(i1, !f, !f)>):  // pred: ^bb52
      %91 = "runtime.accept_transfer"(%arg0, %90) : (!runtime.scope, !runtime.transfer<(i1, !f, !f)>) -> !exec.outcome<(i1, !f, !f)>
      "exec.dispatch"(%91)[^bb60, ^bb2] : (!exec.outcome<(i1, !f, !f)>) -> ()
    ^bb55(%92: !runtime.transfer<(i1, !f, !f)>):  // pred: ^bb59
      %c1_i64 = arith.constant 1 : i64
      %93 = arith.addi %86, %c1_i64 : i64
      cf.br ^bb52(%93, %92 : i64, !runtime.transfer<(i1, !f, !f)>)
    ^bb56(%94: !exec.stop):  // 3 preds: ^bb53, ^bb57, ^bb58
      "runtime.release_transfer"(%87) : (!runtime.transfer<(i1, !f, !f)>) -> ()
      cf.br ^bb2(%94 : !exec.stop)
    ^bb57(%95: ui64):  // pred: ^bb53
      %96:3 = "runtime.transfer_values"(%87) : (!runtime.transfer<(i1, !f, !f)>) -> (i1, !f, !f)
      %97 = "runtime.enter_scope"(%arg0, %86, %95, %96#0, %96#1, %96#2, %arg4, %arg1, %arg2) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 7>, site = "transitions"}> : (!runtime.scope, i64, ui64, i1, !f, !f, !trace, !f, !f) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%97)[^bb58, ^bb56] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb58(%98: !runtime.scope):  // pred: ^bb57
      %99 = call @control_7(%98, %95, %96#0, %96#1, %96#2, %arg4, %arg1, %arg2) : (!runtime.scope, ui64, i1, !f, !f, !trace, !f, !f) -> !exec.outcome<(i1, !f, !f)>
      %100 = "runtime.exit_scope"(%98, %99) : (!runtime.scope, !exec.outcome<(i1, !f, !f)>) -> !exec.outcome<(!runtime.transfer<(i1, !f, !f)>)>
      "exec.dispatch"(%100)[^bb59, ^bb56] : (!exec.outcome<(!runtime.transfer<(i1, !f, !f)>)>) -> ()
    ^bb59(%101: !runtime.transfer<(i1, !f, !f)>):  // pred: ^bb58
      "runtime.release_transfer"(%87) : (!runtime.transfer<(i1, !f, !f)>) -> ()
      cf.br ^bb55(%101 : !runtime.transfer<(i1, !f, !f)>)
    ^bb60(%102: i1, %103: !f, %104: !f):  // pred: ^bb54
      %105 = "exec.apply"(%arg0, %arg3, %7) <{binding = @vector_get, parameters = [], site = "final_x"}> : (!runtime.scope, !v, ui64) -> !exec.outcome<(!f)>
      "exec.dispatch"(%105)[^bb61, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb61(%106: !f):  // pred: ^bb60
      %107 = "exec.apply"(%arg0, %arg3, %9) <{binding = @vector_get, parameters = [], site = "final_y"}> : (!runtime.scope, !v, ui64) -> !exec.outcome<(!f)>
      "exec.dispatch"(%107)[^bb62, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb62(%108: !f):  // pred: ^bb61
      %109 = "exec.apply"(%arg0, %103, %106) <{binding = @field_equal, parameters = [], site = "end_x"}> : (!runtime.scope, !f, !f) -> !exec.outcome<(i1)>
      "exec.dispatch"(%109)[^bb63, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb63(%110: i1):  // pred: ^bb62
      %111 = "exec.apply"(%arg0, %104, %108) <{binding = @field_equal, parameters = [], site = "end_y"}> : (!runtime.scope, !f, !f) -> !exec.outcome<(i1)>
      "exec.dispatch"(%111)[^bb64, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb64(%112: i1):  // pred: ^bb63
      %113 = "exec.apply"(%arg0, %110, %112) <{binding = @bool_and, parameters = [], site = "end"}> : (!runtime.scope, i1, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%113)[^bb65, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb65(%114: i1):  // pred: ^bb64
      %115 = "exec.apply"(%arg0, %102, %114) <{binding = @bool_and, parameters = [], site = "valid"}> : (!runtime.scope, i1, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%115)[^bb66, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb66(%116: i1):  // pred: ^bb65
      %117 = "exec.complete"(%arg0, %116) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      return %117 : !exec.outcome<(i1)>
    }
    func.func private @control_1(%arg0: !runtime.scope) -> !exec.outcome<> attributes {no_inline, runtime.region} {
      %0 = "exec.complete"(%arg0) : (!runtime.scope) -> !exec.outcome<>
      return %0 : !exec.outcome<>
    }
    func.func private @control_2(%arg0: !runtime.scope) -> !exec.outcome<> attributes {no_inline, runtime.region} {
      %0 = "exec.reject"(%arg0) <{reason = "reject", site = "trace_nonempty_reject"}> : (!runtime.scope) -> !exec.stop
      cf.br ^bb1(%0 : !exec.stop)
    ^bb1(%1: !exec.stop):  // pred: ^bb0
      %2 = "exec.failed"(%1) : (!exec.stop) -> !exec.outcome<>
      return %2 : !exec.outcome<>
    }
    func.func private @control_3(%arg0: !runtime.scope) -> !exec.outcome<> attributes {no_inline, runtime.region} {
      %0 = "exec.complete"(%arg0) : (!runtime.scope) -> !exec.outcome<>
      return %0 : !exec.outcome<>
    }
    func.func private @control_4(%arg0: !runtime.scope) -> !exec.outcome<> attributes {no_inline, runtime.region} {
      %0 = "exec.reject"(%arg0) <{reason = "reject", site = "boundary_arity_reject"}> : (!runtime.scope) -> !exec.stop
      cf.br ^bb1(%0 : !exec.stop)
    ^bb1(%1: !exec.stop):  // pred: ^bb0
      %2 = "exec.failed"(%1) : (!exec.stop) -> !exec.outcome<>
      return %2 : !exec.outcome<>
    }
    func.func private @control_5(%arg0: !runtime.scope) -> !exec.outcome<> attributes {no_inline, runtime.region} {
      %0 = "exec.complete"(%arg0) : (!runtime.scope) -> !exec.outcome<>
      return %0 : !exec.outcome<>
    }
    func.func private @control_6(%arg0: !runtime.scope) -> !exec.outcome<> attributes {no_inline, runtime.region} {
      %0 = "exec.reject"(%arg0) <{reason = "reject", site = "first_row_reject"}> : (!runtime.scope) -> !exec.stop
      cf.br ^bb1(%0 : !exec.stop)
    ^bb1(%1: !exec.stop):  // pred: ^bb0
      %2 = "exec.failed"(%1) : (!exec.stop) -> !exec.outcome<>
      return %2 : !exec.outcome<>
    }
    func.func private @control_7(%arg0: !runtime.scope, %arg1: ui64, %arg2: i1, %arg3: !f, %arg4: !f, %arg5: !trace, %arg6: !f, %arg7: !f) -> !exec.outcome<(i1, !f, !f)> attributes {no_inline, runtime.region} {
      %0 = "exec.apply"(%arg0) <{binding = @index_constant, parameters = ["0"], site = "x_column"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1: ui64):  // pred: ^bb0
      %2 = "exec.apply"(%arg0) <{binding = @index_constant, parameters = ["1"], site = "y_column"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%3: !exec.stop):  // 22 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb9, ^bb10, ^bb11, ^bb12, ^bb13, ^bb15, ^bb16, ^bb18, ^bb19, ^bb20, ^bb21, ^bb22, ^bb23, ^bb24, ^bb25
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(i1, !f, !f)>
      return %4 : !exec.outcome<(i1, !f, !f)>
    ^bb3(%5: ui64):  // pred: ^bb1
      %6 = "exec.apply"(%arg0) <{binding = @index_constant, parameters = ["2"], site = "width"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%7: ui64):  // pred: ^bb3
      %8 = "exec.apply"(%arg0, %arg5, %arg1) <{binding = @sequence_at, parameters = [], site = "current"}> : (!runtime.scope, !trace, ui64) -> !exec.outcome<(!v)>
      "exec.dispatch"(%8)[^bb5, ^bb2] : (!exec.outcome<(!v)>) -> ()
    ^bb5(%9: !v):  // pred: ^bb4
      %10 = "exec.apply"(%arg0, %9) <{binding = @vector_length, parameters = [], site = "current_width"}> : (!runtime.scope, !v) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%10)[^bb6, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb6(%11: ui64):  // pred: ^bb5
      %12 = "exec.apply"(%arg0, %11, %7) <{binding = @index_equal, parameters = [], site = "row_shape"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%12)[^bb7, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb7(%13: i1):  // pred: ^bb6
      %14 = "exec.test"(%arg0, %13) <{site = "row_width"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%14)[^bb8, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb8(%15: i1):  // pred: ^bb7
      cf.cond_br %15, ^bb9, ^bb10
    ^bb9:  // pred: ^bb8
      %16 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "row_width"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%16)[^bb12, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb10:  // pred: ^bb8
      %17 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "row_width"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%17)[^bb15, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb11:  // 2 preds: ^bb14, ^bb17
      %18 = "exec.apply"(%arg0, %9, %1) <{binding = @vector_get, parameters = [], site = "next_x"}> : (!runtime.scope, !v, ui64) -> !exec.outcome<(!f)>
      "exec.dispatch"(%18)[^bb18, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb12(%19: !runtime.scope):  // pred: ^bb9
      %20 = call @control_8(%19) : (!runtime.scope) -> !exec.outcome<>
      %21 = "runtime.exit_scope"(%19, %20) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%21)[^bb13, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb13(%22: !runtime.transfer<>):  // pred: ^bb12
      %23 = "runtime.accept_transfer"(%arg0, %22) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%23)[^bb14, ^bb2] : (!exec.outcome<>) -> ()
    ^bb14:  // pred: ^bb13
      cf.br ^bb11
    ^bb15(%24: !runtime.scope):  // pred: ^bb10
      %25 = call @control_9(%24) : (!runtime.scope) -> !exec.outcome<>
      %26 = "runtime.exit_scope"(%24, %25) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%26)[^bb16, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb16(%27: !runtime.transfer<>):  // pred: ^bb15
      %28 = "runtime.accept_transfer"(%arg0, %27) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%28)[^bb17, ^bb2] : (!exec.outcome<>) -> ()
    ^bb17:  // pred: ^bb16
      cf.br ^bb11
    ^bb18(%29: !f):  // pred: ^bb11
      %30 = "exec.apply"(%arg0, %9, %5) <{binding = @vector_get, parameters = [], site = "next_y"}> : (!runtime.scope, !v, ui64) -> !exec.outcome<(!f)>
      "exec.dispatch"(%30)[^bb19, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb19(%31: !f):  // pred: ^bb18
      %32 = "exec.apply"(%arg0, %arg6, %arg3) <{binding = @field_mul, parameters = [], site = "ax"}> : (!runtime.scope, !f, !f) -> !exec.outcome<(!f)>
      "exec.dispatch"(%32)[^bb20, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb20(%33: !f):  // pred: ^bb19
      %34 = "exec.apply"(%arg0, %arg7, %arg4) <{binding = @field_mul, parameters = [], site = "by"}> : (!runtime.scope, !f, !f) -> !exec.outcome<(!f)>
      "exec.dispatch"(%34)[^bb21, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb21(%35: !f):  // pred: ^bb20
      %36 = "exec.apply"(%arg0, %33, %35) <{binding = @field_add, parameters = [], site = "recurrence"}> : (!runtime.scope, !f, !f) -> !exec.outcome<(!f)>
      "exec.dispatch"(%36)[^bb22, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb22(%37: !f):  // pred: ^bb21
      %38 = "exec.apply"(%arg0, %29, %arg4) <{binding = @field_equal, parameters = [], site = "x_ok"}> : (!runtime.scope, !f, !f) -> !exec.outcome<(i1)>
      "exec.dispatch"(%38)[^bb23, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb23(%39: i1):  // pred: ^bb22
      %40 = "exec.apply"(%arg0, %31, %37) <{binding = @field_equal, parameters = [], site = "y_ok"}> : (!runtime.scope, !f, !f) -> !exec.outcome<(i1)>
      "exec.dispatch"(%40)[^bb24, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb24(%41: i1):  // pred: ^bb23
      %42 = "exec.apply"(%arg0, %39, %41) <{binding = @bool_and, parameters = [], site = "step_ok"}> : (!runtime.scope, i1, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%42)[^bb25, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb25(%43: i1):  // pred: ^bb24
      %44 = "exec.apply"(%arg0, %arg2, %43) <{binding = @bool_and, parameters = [], site = "next_ok"}> : (!runtime.scope, i1, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%44)[^bb26, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb26(%45: i1):  // pred: ^bb25
      %46 = "exec.complete"(%arg0, %45, %29, %31) : (!runtime.scope, i1, !f, !f) -> !exec.outcome<(i1, !f, !f)>
      return %46 : !exec.outcome<(i1, !f, !f)>
    }
    func.func private @control_8(%arg0: !runtime.scope) -> !exec.outcome<> attributes {no_inline, runtime.region} {
      %0 = "exec.complete"(%arg0) : (!runtime.scope) -> !exec.outcome<>
      return %0 : !exec.outcome<>
    }
    func.func private @control_9(%arg0: !runtime.scope) -> !exec.outcome<> attributes {no_inline, runtime.region} {
      %0 = "exec.reject"(%arg0) <{reason = "reject", site = "row_width_reject"}> : (!runtime.scope) -> !exec.stop
      cf.br ^bb1(%0 : !exec.stop)
    ^bb1(%1: !exec.stop):  // pred: ^bb0
      %2 = "exec.failed"(%1) : (!exec.stop) -> !exec.outcome<>
      return %2 : !exec.outcome<>
    }

"protocol.func"() ({ ^entry(%configuration:!config,%public:!v,%witness:!trace):
 protocol.statement @relation(%configuration,%public,%witness) {selectors=["V","V","P"],acceptance=1 : i64} : !config,!v,!trace
 %received = protocol.exchange %witness {sender="P",receiver="V",site="witness"} : !trace
 %accepted = "protocol.local_call"(%configuration,%public,%received) {callee=@validate,role="V",site="validate"} : (!config,!v,!trace)->i1
 %unused = arith.constant false
 "protocol.return"(%unused,%accepted) : (i1,i1)->()
}) {sym_name="main",function_type=(!config,!v,!trace)->(i1,i1),roles=["P","V"],input_roles=[["V"],["V"],["P"]],output_roles=[["V"],["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
