// Direct constraint checking deliberately discloses the witness in the proof.
!f = !algebra.field<"bls12-381.fr">
!v = !algebra.field_vector<"bls12-381.fr">
!m = !algebra.field_matrix<"bls12-381.fr">
!ms = !data.sequence<!m>
module { "protocol.module"() ({
"runtime.binding"() {sym_name="index_constant",contract="index.constant",arguments=[],implementation=""} : ()->()
"runtime.binding"() {sym_name="sequence_length",contract="sequence.length",arguments=["matrix:bls12-381.fr"],implementation=""} : ()->()
"runtime.binding"() {sym_name="index_equal",contract="index.equal",arguments=[],implementation=""} : ()->()
"runtime.binding"() {sym_name="vector_length",contract="vector.length",arguments=["bls12-381.fr"],implementation=""} : ()->()
"runtime.binding"() {sym_name="index_less",contract="index.less",arguments=[],implementation=""} : ()->()
"runtime.binding"() {sym_name="sequence_at",contract="sequence.at",arguments=["matrix:bls12-381.fr"],implementation=""} : ()->()
"runtime.binding"() {sym_name="matrix_dimension",contract="matrix.dimension",arguments=["bls12-381.fr"],implementation=""} : ()->()
"runtime.binding"() {sym_name="matrix_mul_vector",contract="matrix.mul_vector",arguments=["bls12-381.fr"],implementation=""} : ()->()
"runtime.binding"() {sym_name="field_constant",contract="field.constant",arguments=["bls12-381.fr"],implementation=""} : ()->()
"runtime.binding"() {sym_name="vector_get",contract="vector.get",arguments=["bls12-381.fr"],implementation=""} : ()->()
"runtime.binding"() {sym_name="field_equal",contract="field.equal",arguments=["bls12-381.fr"],implementation=""} : ()->()
"runtime.binding"() {sym_name="index_add",contract="index.add",arguments=[],implementation=""} : ()->()
"runtime.binding"() {sym_name="bool_and",contract="bool.and",arguments=[],implementation=""} : ()->()
"runtime.binding"() {sym_name="vector_mul",contract="vector.mul",arguments=["bls12-381.fr"],implementation=""} : ()->()
"runtime.binding"() {sym_name="vector_equal",contract="vector.equal",arguments=["bls12-381.fr"],implementation=""} : ()->()
relation.declare @relation {kind="external",key="example/r1cs-data",revision="0",signature=(!ms,!v,!v)->i1,purposes=["parameter","statement","witness"]}
    func.func @validate(%arg0: !runtime.scope, %arg1: !ms, %arg2: !v, %arg3: !v) -> !exec.outcome<(i1)> attributes {no_inline, runtime.origin = ["validate", []]} {
      %0 = "exec.apply"(%arg0) <{binding = @index_constant, parameters = ["0"], site = "zero"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1: ui64):  // pred: ^bb0
      %2 = "exec.apply"(%arg0) <{binding = @index_constant, parameters = ["1"], site = "one_index"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%3: !exec.stop):  // 84 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb9, ^bb10, ^bb11, ^bb12, ^bb13, ^bb15, ^bb16, ^bb18, ^bb19, ^bb20, ^bb22, ^bb23, ^bb24, ^bb25, ^bb26, ^bb28, ^bb29, ^bb31, ^bb32, ^bb33, ^bb35, ^bb36, ^bb37, ^bb38, ^bb39, ^bb41, ^bb42, ^bb44, ^bb45, ^bb46, ^bb47, ^bb48, ^bb50, ^bb51, ^bb52, ^bb53, ^bb54, ^bb56, ^bb57, ^bb59, ^bb60, ^bb61, ^bb62, ^bb63, ^bb65, ^bb66, ^bb67, ^bb68, ^bb69, ^bb71, ^bb72, ^bb74, ^bb75, ^bb76, ^bb78, ^bb79, ^bb80, ^bb81, ^bb82, ^bb84, ^bb85, ^bb87, ^bb89, ^bb90, ^bb91, ^bb92, ^bb93, ^bb95, ^bb96, ^bb98, ^bb99, ^bb100, ^bb104, ^bb106, ^bb110, ^bb111, ^bb112
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(i1)>
      return %4 : !exec.outcome<(i1)>
    ^bb3(%5: ui64):  // pred: ^bb1
      %6 = "exec.apply"(%arg0) <{binding = @index_constant, parameters = ["2"], site = "two"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%7: ui64):  // pred: ^bb3
      %8 = "exec.apply"(%arg0) <{binding = @index_constant, parameters = ["3"], site = "three"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%8)[^bb5, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%9: ui64):  // pred: ^bb4
      %10 = "exec.apply"(%arg0, %arg1) <{binding = @sequence_length, parameters = [], site = "matrix_count"}> : (!runtime.scope, !ms) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%10)[^bb6, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb6(%11: ui64):  // pred: ^bb5
      %12 = "exec.apply"(%arg0, %11, %9) <{binding = @index_equal, parameters = [], site = "three_matrices"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%12)[^bb7, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb7(%13: i1):  // pred: ^bb6
      %14 = "exec.test"(%arg0, %13) <{site = "matrix_arity"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%14)[^bb8, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb8(%15: i1):  // pred: ^bb7
      cf.cond_br %15, ^bb9, ^bb10
    ^bb9:  // pred: ^bb8
      %16 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "matrix_arity"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%16)[^bb12, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb10:  // pred: ^bb8
      %17 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "matrix_arity"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%17)[^bb15, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb11:  // 2 preds: ^bb14, ^bb17
      %18 = "exec.apply"(%arg0, %arg3) <{binding = @vector_length, parameters = [], site = "assignment_count"}> : (!runtime.scope, !v) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%18)[^bb18, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb12(%19: !runtime.scope):  // pred: ^bb9
      %20 = call @control_0(%19) : (!runtime.scope) -> !exec.outcome<>
      %21 = "runtime.exit_scope"(%19, %20) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%21)[^bb13, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb13(%22: !runtime.transfer<>):  // pred: ^bb12
      %23 = "runtime.accept_transfer"(%arg0, %22) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%23)[^bb14, ^bb2] : (!exec.outcome<>) -> ()
    ^bb14:  // pred: ^bb13
      cf.br ^bb11
    ^bb15(%24: !runtime.scope):  // pred: ^bb10
      %25 = call @control_1(%24) : (!runtime.scope) -> !exec.outcome<>
      %26 = "runtime.exit_scope"(%24, %25) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%26)[^bb16, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb16(%27: !runtime.transfer<>):  // pred: ^bb15
      %28 = "runtime.accept_transfer"(%arg0, %27) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%28)[^bb17, ^bb2] : (!exec.outcome<>) -> ()
    ^bb17:  // pred: ^bb16
      cf.br ^bb11
    ^bb18(%29: ui64):  // pred: ^bb11
      %30 = "exec.apply"(%arg0, %arg2) <{binding = @vector_length, parameters = [], site = "public_count"}> : (!runtime.scope, !v) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%30)[^bb19, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb19(%31: ui64):  // pred: ^bb18
      %32 = "exec.apply"(%arg0, %31, %29) <{binding = @index_less, parameters = [], site = "prefix_fits"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%32)[^bb20, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb20(%33: i1):  // pred: ^bb19
      %34 = "exec.test"(%arg0, %33) <{site = "assignment_prefix"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%34)[^bb21, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb21(%35: i1):  // pred: ^bb20
      cf.cond_br %35, ^bb22, ^bb23
    ^bb22:  // pred: ^bb21
      %36 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "assignment_prefix"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%36)[^bb25, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb23:  // pred: ^bb21
      %37 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "assignment_prefix"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%37)[^bb28, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb24:  // 2 preds: ^bb27, ^bb30
      %38 = "exec.apply"(%arg0, %arg1, %1) <{binding = @sequence_at, parameters = [], site = "a"}> : (!runtime.scope, !ms, ui64) -> !exec.outcome<(!m)>
      "exec.dispatch"(%38)[^bb31, ^bb2] : (!exec.outcome<(!m)>) -> ()
    ^bb25(%39: !runtime.scope):  // pred: ^bb22
      %40 = call @control_2(%39) : (!runtime.scope) -> !exec.outcome<>
      %41 = "runtime.exit_scope"(%39, %40) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%41)[^bb26, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb26(%42: !runtime.transfer<>):  // pred: ^bb25
      %43 = "runtime.accept_transfer"(%arg0, %42) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%43)[^bb27, ^bb2] : (!exec.outcome<>) -> ()
    ^bb27:  // pred: ^bb26
      cf.br ^bb24
    ^bb28(%44: !runtime.scope):  // pred: ^bb23
      %45 = call @control_3(%44) : (!runtime.scope) -> !exec.outcome<>
      %46 = "runtime.exit_scope"(%44, %45) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%46)[^bb29, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb29(%47: !runtime.transfer<>):  // pred: ^bb28
      %48 = "runtime.accept_transfer"(%arg0, %47) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%48)[^bb30, ^bb2] : (!exec.outcome<>) -> ()
    ^bb30:  // pred: ^bb29
      cf.br ^bb24
    ^bb31(%49: !m):  // pred: ^bb24
      %50 = "exec.apply"(%arg0, %49) <{binding = @matrix_dimension, parameters = ["1"], site = "acols"}> : (!runtime.scope, !m) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%50)[^bb32, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb32(%51: ui64):  // pred: ^bb31
      %52 = "exec.apply"(%arg0, %51, %29) <{binding = @index_equal, parameters = [], site = "awidth"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%52)[^bb33, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb33(%53: i1):  // pred: ^bb32
      %54 = "exec.test"(%arg0, %53) <{site = "acolumns"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%54)[^bb34, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb34(%55: i1):  // pred: ^bb33
      cf.cond_br %55, ^bb35, ^bb36
    ^bb35:  // pred: ^bb34
      %56 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "acolumns"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%56)[^bb38, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb36:  // pred: ^bb34
      %57 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "acolumns"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%57)[^bb41, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb37:  // 2 preds: ^bb40, ^bb43
      %58 = "exec.apply"(%arg0, %49, %arg3) <{binding = @matrix_mul_vector, parameters = [], site = "az"}> : (!runtime.scope, !m, !v) -> !exec.outcome<(!v)>
      "exec.dispatch"(%58)[^bb44, ^bb2] : (!exec.outcome<(!v)>) -> ()
    ^bb38(%59: !runtime.scope):  // pred: ^bb35
      %60 = call @control_4(%59) : (!runtime.scope) -> !exec.outcome<>
      %61 = "runtime.exit_scope"(%59, %60) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%61)[^bb39, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb39(%62: !runtime.transfer<>):  // pred: ^bb38
      %63 = "runtime.accept_transfer"(%arg0, %62) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%63)[^bb40, ^bb2] : (!exec.outcome<>) -> ()
    ^bb40:  // pred: ^bb39
      cf.br ^bb37
    ^bb41(%64: !runtime.scope):  // pred: ^bb36
      %65 = call @control_5(%64) : (!runtime.scope) -> !exec.outcome<>
      %66 = "runtime.exit_scope"(%64, %65) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%66)[^bb42, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb42(%67: !runtime.transfer<>):  // pred: ^bb41
      %68 = "runtime.accept_transfer"(%arg0, %67) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%68)[^bb43, ^bb2] : (!exec.outcome<>) -> ()
    ^bb43:  // pred: ^bb42
      cf.br ^bb37
    ^bb44(%69: !v):  // pred: ^bb37
      %70 = "exec.apply"(%arg0, %69) <{binding = @vector_length, parameters = [], site = "arows"}> : (!runtime.scope, !v) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%70)[^bb45, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb45(%71: ui64):  // pred: ^bb44
      %72 = "exec.apply"(%arg0, %arg1, %5) <{binding = @sequence_at, parameters = [], site = "b"}> : (!runtime.scope, !ms, ui64) -> !exec.outcome<(!m)>
      "exec.dispatch"(%72)[^bb46, ^bb2] : (!exec.outcome<(!m)>) -> ()
    ^bb46(%73: !m):  // pred: ^bb45
      %74 = "exec.apply"(%arg0, %73) <{binding = @matrix_dimension, parameters = ["1"], site = "bcols"}> : (!runtime.scope, !m) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%74)[^bb47, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb47(%75: ui64):  // pred: ^bb46
      %76 = "exec.apply"(%arg0, %75, %29) <{binding = @index_equal, parameters = [], site = "bwidth"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%76)[^bb48, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb48(%77: i1):  // pred: ^bb47
      %78 = "exec.test"(%arg0, %77) <{site = "bcolumns"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%78)[^bb49, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb49(%79: i1):  // pred: ^bb48
      cf.cond_br %79, ^bb50, ^bb51
    ^bb50:  // pred: ^bb49
      %80 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "bcolumns"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%80)[^bb53, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb51:  // pred: ^bb49
      %81 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "bcolumns"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%81)[^bb56, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb52:  // 2 preds: ^bb55, ^bb58
      %82 = "exec.apply"(%arg0, %73, %arg3) <{binding = @matrix_mul_vector, parameters = [], site = "bz"}> : (!runtime.scope, !m, !v) -> !exec.outcome<(!v)>
      "exec.dispatch"(%82)[^bb59, ^bb2] : (!exec.outcome<(!v)>) -> ()
    ^bb53(%83: !runtime.scope):  // pred: ^bb50
      %84 = call @control_6(%83) : (!runtime.scope) -> !exec.outcome<>
      %85 = "runtime.exit_scope"(%83, %84) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%85)[^bb54, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb54(%86: !runtime.transfer<>):  // pred: ^bb53
      %87 = "runtime.accept_transfer"(%arg0, %86) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%87)[^bb55, ^bb2] : (!exec.outcome<>) -> ()
    ^bb55:  // pred: ^bb54
      cf.br ^bb52
    ^bb56(%88: !runtime.scope):  // pred: ^bb51
      %89 = call @control_7(%88) : (!runtime.scope) -> !exec.outcome<>
      %90 = "runtime.exit_scope"(%88, %89) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%90)[^bb57, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb57(%91: !runtime.transfer<>):  // pred: ^bb56
      %92 = "runtime.accept_transfer"(%arg0, %91) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%92)[^bb58, ^bb2] : (!exec.outcome<>) -> ()
    ^bb58:  // pred: ^bb57
      cf.br ^bb52
    ^bb59(%93: !v):  // pred: ^bb52
      %94 = "exec.apply"(%arg0, %93) <{binding = @vector_length, parameters = [], site = "brows"}> : (!runtime.scope, !v) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%94)[^bb60, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb60(%95: ui64):  // pred: ^bb59
      %96 = "exec.apply"(%arg0, %arg1, %7) <{binding = @sequence_at, parameters = [], site = "c"}> : (!runtime.scope, !ms, ui64) -> !exec.outcome<(!m)>
      "exec.dispatch"(%96)[^bb61, ^bb2] : (!exec.outcome<(!m)>) -> ()
    ^bb61(%97: !m):  // pred: ^bb60
      %98 = "exec.apply"(%arg0, %97) <{binding = @matrix_dimension, parameters = ["1"], site = "ccols"}> : (!runtime.scope, !m) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%98)[^bb62, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb62(%99: ui64):  // pred: ^bb61
      %100 = "exec.apply"(%arg0, %99, %29) <{binding = @index_equal, parameters = [], site = "cwidth"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%100)[^bb63, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb63(%101: i1):  // pred: ^bb62
      %102 = "exec.test"(%arg0, %101) <{site = "ccolumns"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%102)[^bb64, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb64(%103: i1):  // pred: ^bb63
      cf.cond_br %103, ^bb65, ^bb66
    ^bb65:  // pred: ^bb64
      %104 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "ccolumns"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%104)[^bb68, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb66:  // pred: ^bb64
      %105 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "ccolumns"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%105)[^bb71, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb67:  // 2 preds: ^bb70, ^bb73
      %106 = "exec.apply"(%arg0, %97, %arg3) <{binding = @matrix_mul_vector, parameters = [], site = "cz"}> : (!runtime.scope, !m, !v) -> !exec.outcome<(!v)>
      "exec.dispatch"(%106)[^bb74, ^bb2] : (!exec.outcome<(!v)>) -> ()
    ^bb68(%107: !runtime.scope):  // pred: ^bb65
      %108 = call @control_8(%107) : (!runtime.scope) -> !exec.outcome<>
      %109 = "runtime.exit_scope"(%107, %108) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%109)[^bb69, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb69(%110: !runtime.transfer<>):  // pred: ^bb68
      %111 = "runtime.accept_transfer"(%arg0, %110) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%111)[^bb70, ^bb2] : (!exec.outcome<>) -> ()
    ^bb70:  // pred: ^bb69
      cf.br ^bb67
    ^bb71(%112: !runtime.scope):  // pred: ^bb66
      %113 = call @control_9(%112) : (!runtime.scope) -> !exec.outcome<>
      %114 = "runtime.exit_scope"(%112, %113) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%114)[^bb72, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb72(%115: !runtime.transfer<>):  // pred: ^bb71
      %116 = "runtime.accept_transfer"(%arg0, %115) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%116)[^bb73, ^bb2] : (!exec.outcome<>) -> ()
    ^bb73:  // pred: ^bb72
      cf.br ^bb67
    ^bb74(%117: !v):  // pred: ^bb67
      %118 = "exec.apply"(%arg0, %117) <{binding = @vector_length, parameters = [], site = "crows"}> : (!runtime.scope, !v) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%118)[^bb75, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb75(%119: ui64):  // pred: ^bb74
      %120 = "exec.apply"(%arg0, %71, %95) <{binding = @index_equal, parameters = [], site = "bsize"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%120)[^bb76, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb76(%121: i1):  // pred: ^bb75
      %122 = "exec.test"(%arg0, %121) <{site = "bshape"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%122)[^bb77, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb77(%123: i1):  // pred: ^bb76
      cf.cond_br %123, ^bb78, ^bb79
    ^bb78:  // pred: ^bb77
      %124 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "bshape"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%124)[^bb81, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb79:  // pred: ^bb77
      %125 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "bshape"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%125)[^bb84, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb80:  // 2 preds: ^bb83, ^bb86
      %126 = "exec.apply"(%arg0, %71, %119) <{binding = @index_equal, parameters = [], site = "csize"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%126)[^bb87, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb81(%127: !runtime.scope):  // pred: ^bb78
      %128 = call @control_10(%127) : (!runtime.scope) -> !exec.outcome<>
      %129 = "runtime.exit_scope"(%127, %128) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%129)[^bb82, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb82(%130: !runtime.transfer<>):  // pred: ^bb81
      %131 = "runtime.accept_transfer"(%arg0, %130) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%131)[^bb83, ^bb2] : (!exec.outcome<>) -> ()
    ^bb83:  // pred: ^bb82
      cf.br ^bb80
    ^bb84(%132: !runtime.scope):  // pred: ^bb79
      %133 = call @control_11(%132) : (!runtime.scope) -> !exec.outcome<>
      %134 = "runtime.exit_scope"(%132, %133) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%134)[^bb85, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb85(%135: !runtime.transfer<>):  // pred: ^bb84
      %136 = "runtime.accept_transfer"(%arg0, %135) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%136)[^bb86, ^bb2] : (!exec.outcome<>) -> ()
    ^bb86:  // pred: ^bb85
      cf.br ^bb80
    ^bb87(%137: i1):  // pred: ^bb80
      %138 = "exec.test"(%arg0, %137) <{site = "cshape"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%138)[^bb88, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb88(%139: i1):  // pred: ^bb87
      cf.cond_br %139, ^bb89, ^bb90
    ^bb89:  // pred: ^bb88
      %140 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "cshape"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%140)[^bb92, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb90:  // pred: ^bb88
      %141 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "cshape"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%141)[^bb95, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb91:  // 2 preds: ^bb94, ^bb97
      %142 = "exec.apply"(%arg0) <{binding = @field_constant, parameters = ["1"], site = "one"}> : (!runtime.scope) -> !exec.outcome<(!f)>
      "exec.dispatch"(%142)[^bb98, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb92(%143: !runtime.scope):  // pred: ^bb89
      %144 = call @control_12(%143) : (!runtime.scope) -> !exec.outcome<>
      %145 = "runtime.exit_scope"(%143, %144) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%145)[^bb93, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb93(%146: !runtime.transfer<>):  // pred: ^bb92
      %147 = "runtime.accept_transfer"(%arg0, %146) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%147)[^bb94, ^bb2] : (!exec.outcome<>) -> ()
    ^bb94:  // pred: ^bb93
      cf.br ^bb91
    ^bb95(%148: !runtime.scope):  // pred: ^bb90
      %149 = call @control_13(%148) : (!runtime.scope) -> !exec.outcome<>
      %150 = "runtime.exit_scope"(%148, %149) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%150)[^bb96, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb96(%151: !runtime.transfer<>):  // pred: ^bb95
      %152 = "runtime.accept_transfer"(%arg0, %151) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%152)[^bb97, ^bb2] : (!exec.outcome<>) -> ()
    ^bb97:  // pred: ^bb96
      cf.br ^bb91
    ^bb98(%153: !f):  // pred: ^bb91
      %154 = "exec.apply"(%arg0, %arg3, %1) <{binding = @vector_get, parameters = [], site = "assignment_one"}> : (!runtime.scope, !v, ui64) -> !exec.outcome<(!f)>
      "exec.dispatch"(%154)[^bb99, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb99(%155: !f):  // pred: ^bb98
      %156 = "exec.apply"(%arg0, %153, %155) <{binding = @field_equal, parameters = [], site = "one_valid"}> : (!runtime.scope, !f, !f) -> !exec.outcome<(i1)>
      "exec.dispatch"(%156)[^bb100, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb100(%157: i1):  // pred: ^bb99
      %158 = "exec.range"(%arg0, %1, %31) <{site = "public_prefix"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%158)[^bb101, ^bb2] : (!exec.outcome<(i64, i64)>) -> ()
    ^bb101(%159: i64, %160: i64):  // pred: ^bb100
      %161 = "runtime.borrow_transfer"(%arg0, %157) : (!runtime.scope, i1) -> !runtime.transfer<(i1)>
      cf.br ^bb102(%159, %161 : i64, !runtime.transfer<(i1)>)
    ^bb102(%162: i64, %163: !runtime.transfer<(i1)>):  // 2 preds: ^bb101, ^bb105
      %164 = arith.cmpi ult, %162, %160 : i64
      cf.cond_br %164, ^bb103, ^bb104(%163 : !runtime.transfer<(i1)>)
    ^bb103:  // pred: ^bb102
      %165 = "runtime.iteration"(%arg0, %162) <{site = "public_prefix"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%165)[^bb107, ^bb106] : (!exec.outcome<(ui64)>) -> ()
    ^bb104(%166: !runtime.transfer<(i1)>):  // pred: ^bb102
      %167 = "runtime.accept_transfer"(%arg0, %166) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%167)[^bb110, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb105(%168: !runtime.transfer<(i1)>):  // pred: ^bb109
      %c1_i64 = arith.constant 1 : i64
      %169 = arith.addi %162, %c1_i64 : i64
      cf.br ^bb102(%169, %168 : i64, !runtime.transfer<(i1)>)
    ^bb106(%170: !exec.stop):  // 3 preds: ^bb103, ^bb107, ^bb108
      "runtime.release_transfer"(%163) : (!runtime.transfer<(i1)>) -> ()
      cf.br ^bb2(%170 : !exec.stop)
    ^bb107(%171: ui64):  // pred: ^bb103
      %172 = "runtime.transfer_values"(%163) : (!runtime.transfer<(i1)>) -> i1
      %173 = "runtime.enter_scope"(%arg0, %162, %171, %172, %arg2, %arg3) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 4>, site = "public_prefix"}> : (!runtime.scope, i64, ui64, i1, !v, !v) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%173)[^bb108, ^bb106] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb108(%174: !runtime.scope):  // pred: ^bb107
      %175 = call @control_14(%174, %171, %172, %arg2, %arg3) : (!runtime.scope, ui64, i1, !v, !v) -> !exec.outcome<(i1)>
      %176 = "runtime.exit_scope"(%174, %175) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%176)[^bb109, ^bb106] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb109(%177: !runtime.transfer<(i1)>):  // pred: ^bb108
      "runtime.release_transfer"(%163) : (!runtime.transfer<(i1)>) -> ()
      cf.br ^bb105(%177 : !runtime.transfer<(i1)>)
    ^bb110(%178: i1):  // pred: ^bb104
      %179 = "exec.apply"(%arg0, %69, %93) <{binding = @vector_mul, parameters = [], site = "products"}> : (!runtime.scope, !v, !v) -> !exec.outcome<(!v)>
      "exec.dispatch"(%179)[^bb111, ^bb2] : (!exec.outcome<(!v)>) -> ()
    ^bb111(%180: !v):  // pred: ^bb110
      %181 = "exec.apply"(%arg0, %180, %117) <{binding = @vector_equal, parameters = [], site = "rows_valid"}> : (!runtime.scope, !v, !v) -> !exec.outcome<(i1)>
      "exec.dispatch"(%181)[^bb112, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb112(%182: i1):  // pred: ^bb111
      %183 = "exec.apply"(%arg0, %178, %182) <{binding = @bool_and, parameters = [], site = "accepted"}> : (!runtime.scope, i1, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%183)[^bb113, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb113(%184: i1):  // pred: ^bb112
      %185 = "exec.returned"(%184) : (i1) -> !exec.outcome<(i1)>
      return %185 : !exec.outcome<(i1)>
    }
    func.func private @control_0(%arg0: !runtime.scope) -> !exec.outcome<> attributes {no_inline, runtime.region} {
      %0 = "exec.complete"(%arg0) : (!runtime.scope) -> !exec.outcome<>
      return %0 : !exec.outcome<>
    }
    func.func private @control_1(%arg0: !runtime.scope) -> !exec.outcome<> attributes {no_inline, runtime.region} {
      %0 = "exec.reject"(%arg0) <{reason = "reject", site = "matrix_arity_reject"}> : (!runtime.scope) -> !exec.stop
      cf.br ^bb1(%0 : !exec.stop)
    ^bb1(%1: !exec.stop):  // pred: ^bb0
      %2 = "exec.failed"(%1) : (!exec.stop) -> !exec.outcome<>
      return %2 : !exec.outcome<>
    }
    func.func private @control_2(%arg0: !runtime.scope) -> !exec.outcome<> attributes {no_inline, runtime.region} {
      %0 = "exec.complete"(%arg0) : (!runtime.scope) -> !exec.outcome<>
      return %0 : !exec.outcome<>
    }
    func.func private @control_3(%arg0: !runtime.scope) -> !exec.outcome<> attributes {no_inline, runtime.region} {
      %0 = "exec.reject"(%arg0) <{reason = "reject", site = "assignment_prefix_reject"}> : (!runtime.scope) -> !exec.stop
      cf.br ^bb1(%0 : !exec.stop)
    ^bb1(%1: !exec.stop):  // pred: ^bb0
      %2 = "exec.failed"(%1) : (!exec.stop) -> !exec.outcome<>
      return %2 : !exec.outcome<>
    }
    func.func private @control_4(%arg0: !runtime.scope) -> !exec.outcome<> attributes {no_inline, runtime.region} {
      %0 = "exec.complete"(%arg0) : (!runtime.scope) -> !exec.outcome<>
      return %0 : !exec.outcome<>
    }
    func.func private @control_5(%arg0: !runtime.scope) -> !exec.outcome<> attributes {no_inline, runtime.region} {
      %0 = "exec.reject"(%arg0) <{reason = "reject", site = "acolumns_reject"}> : (!runtime.scope) -> !exec.stop
      cf.br ^bb1(%0 : !exec.stop)
    ^bb1(%1: !exec.stop):  // pred: ^bb0
      %2 = "exec.failed"(%1) : (!exec.stop) -> !exec.outcome<>
      return %2 : !exec.outcome<>
    }
    func.func private @control_6(%arg0: !runtime.scope) -> !exec.outcome<> attributes {no_inline, runtime.region} {
      %0 = "exec.complete"(%arg0) : (!runtime.scope) -> !exec.outcome<>
      return %0 : !exec.outcome<>
    }
    func.func private @control_7(%arg0: !runtime.scope) -> !exec.outcome<> attributes {no_inline, runtime.region} {
      %0 = "exec.reject"(%arg0) <{reason = "reject", site = "bcolumns_reject"}> : (!runtime.scope) -> !exec.stop
      cf.br ^bb1(%0 : !exec.stop)
    ^bb1(%1: !exec.stop):  // pred: ^bb0
      %2 = "exec.failed"(%1) : (!exec.stop) -> !exec.outcome<>
      return %2 : !exec.outcome<>
    }
    func.func private @control_8(%arg0: !runtime.scope) -> !exec.outcome<> attributes {no_inline, runtime.region} {
      %0 = "exec.complete"(%arg0) : (!runtime.scope) -> !exec.outcome<>
      return %0 : !exec.outcome<>
    }
    func.func private @control_9(%arg0: !runtime.scope) -> !exec.outcome<> attributes {no_inline, runtime.region} {
      %0 = "exec.reject"(%arg0) <{reason = "reject", site = "ccolumns_reject"}> : (!runtime.scope) -> !exec.stop
      cf.br ^bb1(%0 : !exec.stop)
    ^bb1(%1: !exec.stop):  // pred: ^bb0
      %2 = "exec.failed"(%1) : (!exec.stop) -> !exec.outcome<>
      return %2 : !exec.outcome<>
    }
    func.func private @control_10(%arg0: !runtime.scope) -> !exec.outcome<> attributes {no_inline, runtime.region} {
      %0 = "exec.complete"(%arg0) : (!runtime.scope) -> !exec.outcome<>
      return %0 : !exec.outcome<>
    }
    func.func private @control_11(%arg0: !runtime.scope) -> !exec.outcome<> attributes {no_inline, runtime.region} {
      %0 = "exec.reject"(%arg0) <{reason = "reject", site = "bshape_reject"}> : (!runtime.scope) -> !exec.stop
      cf.br ^bb1(%0 : !exec.stop)
    ^bb1(%1: !exec.stop):  // pred: ^bb0
      %2 = "exec.failed"(%1) : (!exec.stop) -> !exec.outcome<>
      return %2 : !exec.outcome<>
    }
    func.func private @control_12(%arg0: !runtime.scope) -> !exec.outcome<> attributes {no_inline, runtime.region} {
      %0 = "exec.complete"(%arg0) : (!runtime.scope) -> !exec.outcome<>
      return %0 : !exec.outcome<>
    }
    func.func private @control_13(%arg0: !runtime.scope) -> !exec.outcome<> attributes {no_inline, runtime.region} {
      %0 = "exec.reject"(%arg0) <{reason = "reject", site = "cshape_reject"}> : (!runtime.scope) -> !exec.stop
      cf.br ^bb1(%0 : !exec.stop)
    ^bb1(%1: !exec.stop):  // pred: ^bb0
      %2 = "exec.failed"(%1) : (!exec.stop) -> !exec.outcome<>
      return %2 : !exec.outcome<>
    }
    func.func private @control_14(%arg0: !runtime.scope, %arg1: ui64, %arg2: i1, %arg3: !v, %arg4: !v) -> !exec.outcome<(i1)> attributes {no_inline, runtime.region} {
      %0 = "exec.apply"(%arg0) <{binding = @index_constant, parameters = ["1"], site = "offset"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1: ui64):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %arg1, %1) <{binding = @index_add, parameters = [], site = "column"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%3: !exec.stop):  // 6 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(i1)>
      return %4 : !exec.outcome<(i1)>
    ^bb3(%5: ui64):  // pred: ^bb1
      %6 = "exec.apply"(%arg0, %arg3, %arg1) <{binding = @vector_get, parameters = [], site = "expected"}> : (!runtime.scope, !v, ui64) -> !exec.outcome<(!f)>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb4(%7: !f):  // pred: ^bb3
      %8 = "exec.apply"(%arg0, %arg4, %5) <{binding = @vector_get, parameters = [], site = "actual"}> : (!runtime.scope, !v, ui64) -> !exec.outcome<(!f)>
      "exec.dispatch"(%8)[^bb5, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb5(%9: !f):  // pred: ^bb4
      %10 = "exec.apply"(%arg0, %7, %9) <{binding = @field_equal, parameters = [], site = "equal"}> : (!runtime.scope, !f, !f) -> !exec.outcome<(i1)>
      "exec.dispatch"(%10)[^bb6, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb6(%11: i1):  // pred: ^bb5
      %12 = "exec.apply"(%arg0, %arg2, %11) <{binding = @bool_and, parameters = [], site = "prefix_ok"}> : (!runtime.scope, i1, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%12)[^bb7, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb7(%13: i1):  // pred: ^bb6
      %14 = "exec.complete"(%arg0, %13) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      return %14 : !exec.outcome<(i1)>
    }

"protocol.func"() ({ ^entry(%configuration:!ms,%public:!v,%witness:!v):
 protocol.statement @relation(%configuration,%public,%witness) {selectors=["V","V","P"],acceptance=1 : i64} : !ms,!v,!v
 %received = protocol.exchange %witness {sender="P",receiver="V",site="witness"} : !v
 %accepted = "protocol.local_call"(%configuration,%public,%received) {callee=@validate,role="V",site="validate"} : (!ms,!v,!v)->i1
 %unused = arith.constant false
 "protocol.return"(%unused,%accepted) : (i1,i1)->()
}) {sym_name="main",function_type=(!ms,!v,!v)->(i1,i1),roles=["P","V"],input_roles=[["V"],["V"],["P"]],output_roles=[["V"],["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
