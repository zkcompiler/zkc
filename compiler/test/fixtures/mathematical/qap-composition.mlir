// Direct relation checking discloses the witness. This is a composition client.
!f = !algebra.field<"bn254.fr">
!v = !algebra.field_vector<"bn254.fr">
!m = !algebra.field_matrix<"bn254.fr">
!ms = !data.sequence<!m>
!p = !poly.univariate<"bn254.fr">
!g = !algebra.group<"bn254.g1">
!gs = !algebra.group_vector<"bn254.g1">
!g2 = !algebra.group<"bn254.g2">
!gt = !algebra.group<"bn254.gt">
module { "protocol.module"() ({
"runtime.binding"() {sym_name="index_constant",contract="index.constant",arguments=[],implementation="",function_type=(!runtime.scope) -> !exec.outcome<(ui64)>} : ()->()
"runtime.binding"() {sym_name="field_constant",contract="field.constant",arguments=["bn254.fr"],implementation="",function_type=(!runtime.scope) -> !exec.outcome<(!algebra.field<"bn254.fr">)>} : ()->()
"runtime.binding"() {sym_name="sequence_length_2",contract="sequence.length",arguments=[!algebra.field_matrix<"bn254.fr">],implementation="",function_type=(!runtime.scope, !data.sequence<!algebra.field_matrix<"bn254.fr">>) -> !exec.outcome<(ui64)>} : ()->()
"runtime.binding"() {sym_name="index_equal",contract="index.equal",arguments=[],implementation="",function_type=(!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>} : ()->()
"runtime.binding"() {sym_name="index_add",contract="index.add",arguments=[],implementation="",function_type=(!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>} : ()->()
"runtime.binding"() {sym_name="vector_geometric",contract="vector.geometric",arguments=["bn254.fr"],implementation="",function_type=(!runtime.scope, !algebra.field<"bn254.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bn254.fr">)>} : ()->()
"runtime.binding"() {sym_name="vector_get",contract="vector.get",arguments=["bn254.fr"],implementation="",function_type=(!runtime.scope, !algebra.field_vector<"bn254.fr">, ui64) -> !exec.outcome<(!algebra.field<"bn254.fr">)>} : ()->()
"runtime.binding"() {sym_name="field_equal",contract="field.equal",arguments=["bn254.fr"],implementation="",function_type=(!runtime.scope, !algebra.field<"bn254.fr">, !algebra.field<"bn254.fr">) -> !exec.outcome<(i1)>} : ()->()
"runtime.binding"() {sym_name="bool_not",contract="bool.not",arguments=[],implementation="",function_type=(!runtime.scope, i1) -> !exec.outcome<(i1)>} : ()->()
"runtime.binding"() {sym_name="sequence_at_9",contract="sequence.at",arguments=[!algebra.field_matrix<"bn254.fr">],implementation="",function_type=(!runtime.scope, !data.sequence<!algebra.field_matrix<"bn254.fr">>, ui64) -> !exec.outcome<(!algebra.field_matrix<"bn254.fr">)>} : ()->()
"runtime.binding"() {sym_name="matrix_mul_vector",contract="matrix.mul_vector",arguments=["bn254.fr"],implementation="",function_type=(!runtime.scope, !algebra.field_matrix<"bn254.fr">, !algebra.field_vector<"bn254.fr">) -> !exec.outcome<(!algebra.field_vector<"bn254.fr">)>} : ()->()
"runtime.binding"() {sym_name="vector_length",contract="vector.length",arguments=["bn254.fr"],implementation="",function_type=(!runtime.scope, !algebra.field_vector<"bn254.fr">) -> !exec.outcome<(ui64)>} : ()->()
"runtime.binding"() {sym_name="poly_coset_interpolate",contract="poly.coset_interpolate",arguments=["bn254.fr"],implementation="",function_type=(!runtime.scope, !algebra.field_vector<"bn254.fr">, !algebra.field<"bn254.fr">) -> !exec.outcome<(!poly.univariate<"bn254.fr">)>} : ()->()
"runtime.binding"() {sym_name="poly_coset_evaluate",contract="poly.coset_evaluate",arguments=["bn254.fr"],implementation="",function_type=(!runtime.scope, !poly.univariate<"bn254.fr">, !algebra.field<"bn254.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bn254.fr">)>} : ()->()
"runtime.binding"() {sym_name="vector_mul",contract="vector.mul",arguments=["bn254.fr"],implementation="",function_type=(!runtime.scope, !algebra.field_vector<"bn254.fr">, !algebra.field_vector<"bn254.fr">) -> !exec.outcome<(!algebra.field_vector<"bn254.fr">)>} : ()->()
"runtime.binding"() {sym_name="vector_equal",contract="vector.equal",arguments=["bn254.fr"],implementation="",function_type=(!runtime.scope, !algebra.field_vector<"bn254.fr">, !algebra.field_vector<"bn254.fr">) -> !exec.outcome<(i1)>} : ()->()
"runtime.binding"() {sym_name="vector_sub",contract="vector.sub",arguments=["bn254.fr"],implementation="",function_type=(!runtime.scope, !algebra.field_vector<"bn254.fr">, !algebra.field_vector<"bn254.fr">) -> !exec.outcome<(!algebra.field_vector<"bn254.fr">)>} : ()->()
"runtime.binding"() {sym_name="curve_msm_17",contract="curve.msm",arguments=["bn254.g1"],implementation="",function_type=(!runtime.scope, !algebra.field_vector<"bn254.fr">, !algebra.group_vector<"bn254.g1">) -> !exec.outcome<(!algebra.group<"bn254.g1">)>} : ()->()
"runtime.binding"() {sym_name="vector_slice",contract="vector.slice",arguments=["bn254.fr"],implementation="",function_type=(!runtime.scope, !algebra.field_vector<"bn254.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bn254.fr">)>} : ()->()
"runtime.binding"() {sym_name="bool_and",contract="bool.and",arguments=[],implementation="",function_type=(!runtime.scope, i1, i1) -> !exec.outcome<(i1)>} : ()->()
relation.declare @relation {kind="external",key="example/qap-data",revision="0",signature=(!ms,!v,!v,!gs,!g2,!f,ui64)->i1,purposes=["parameter","statement","witness","parameter","parameter","parameter","parameter"]}
    func.func @numerator(%arg0: !runtime.scope, %arg1: !ms, %arg2: !v, %arg3: !f, %arg4: ui64) -> !exec.outcome<(!v, i1)> attributes {no_inline, runtime.origin = ["numerator", []]} {
      %0 = "exec.apply"(%arg0) <{binding = @index_constant, parameters = ["0"], site = "zero"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1: ui64):  // pred: ^bb0
      %2 = "exec.apply"(%arg0) <{binding = @index_constant, parameters = ["1"], site = "one_index"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%3: !exec.stop):  // 69 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb8, ^bb10, ^bb11, ^bb12, ^bb13, ^bb14, ^bb16, ^bb17, ^bb19, ^bb20, ^bb21, ^bb22, ^bb23, ^bb25, ^bb26, ^bb27, ^bb28, ^bb29, ^bb31, ^bb32, ^bb34, ^bb35, ^bb36, ^bb37, ^bb39, ^bb40, ^bb41, ^bb42, ^bb43, ^bb45, ^bb46, ^bb48, ^bb49, ^bb50, ^bb51, ^bb52, ^bb53, ^bb55, ^bb56, ^bb57, ^bb58, ^bb59, ^bb61, ^bb62, ^bb64, ^bb65, ^bb66, ^bb67, ^bb68, ^bb69, ^bb71, ^bb72, ^bb73, ^bb74, ^bb75, ^bb77, ^bb78, ^bb80, ^bb81, ^bb82, ^bb83, ^bb84
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!v, i1)>
      return %4 : !exec.outcome<(!v, i1)>
    ^bb3(%5: ui64):  // pred: ^bb1
      %6 = "exec.apply"(%arg0) <{binding = @index_constant, parameters = ["2"], site = "two"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%7: ui64):  // pred: ^bb3
      %8 = "exec.apply"(%arg0) <{binding = @index_constant, parameters = ["3"], site = "three"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%8)[^bb5, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%9: ui64):  // pred: ^bb4
      %10 = "exec.apply"(%arg0) <{binding = @field_constant, parameters = ["1"], site = "one"}> : (!runtime.scope) -> !exec.outcome<(!f)>
      "exec.dispatch"(%10)[^bb6, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb6(%11: !f):  // pred: ^bb5
      %12 = "exec.apply"(%arg0, %arg1) <{binding = @sequence_length_2, parameters = [], site = "count"}> : (!runtime.scope, !ms) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%12)[^bb7, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb7(%13: ui64):  // pred: ^bb6
      %14 = "exec.apply"(%arg0, %13, %9) <{binding = @index_equal, parameters = [], site = "arity"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%14)[^bb8, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb8(%15: i1):  // pred: ^bb7
      %16 = "exec.test"(%arg0, %15) <{site = "matrix_arity"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%16)[^bb9, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb9(%17: i1):  // pred: ^bb8
      cf.cond_br %17, ^bb10, ^bb11
    ^bb10:  // pred: ^bb9
      %18 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "matrix_arity"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%18)[^bb13, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb11:  // pred: ^bb9
      %19 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "matrix_arity"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%19)[^bb16, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb12:  // 2 preds: ^bb15, ^bb18
      %20 = "exec.apply"(%arg0, %arg4, %5) <{binding = @index_add, parameters = [], site = "nplus"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%20)[^bb19, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb13(%21: !runtime.scope):  // pred: ^bb10
      %22 = call @control_0(%21) : (!runtime.scope) -> !exec.outcome<>
      %23 = "runtime.exit_scope"(%21, %22) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%23)[^bb14, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb14(%24: !runtime.transfer<>):  // pred: ^bb13
      %25 = "runtime.accept_transfer"(%arg0, %24) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%25)[^bb15, ^bb2] : (!exec.outcome<>) -> ()
    ^bb15:  // pred: ^bb14
      cf.br ^bb12
    ^bb16(%26: !runtime.scope):  // pred: ^bb11
      %27 = call @control_1(%26) : (!runtime.scope) -> !exec.outcome<>
      %28 = "runtime.exit_scope"(%26, %27) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%28)[^bb17, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb17(%29: !runtime.transfer<>):  // pred: ^bb16
      %30 = "runtime.accept_transfer"(%arg0, %29) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%30)[^bb18, ^bb2] : (!exec.outcome<>) -> ()
    ^bb18:  // pred: ^bb17
      cf.br ^bb12
    ^bb19(%31: ui64):  // pred: ^bb12
      %32 = "exec.apply"(%arg0, %arg3, %31) <{binding = @vector_geometric, parameters = [], site = "powers"}> : (!runtime.scope, !f, ui64) -> !exec.outcome<(!v)>
      "exec.dispatch"(%32)[^bb20, ^bb2] : (!exec.outcome<(!v)>) -> ()
    ^bb20(%33: !v):  // pred: ^bb19
      %34 = "exec.apply"(%arg0, %33, %arg4) <{binding = @vector_get, parameters = [], site = "shift_power"}> : (!runtime.scope, !v, ui64) -> !exec.outcome<(!f)>
      "exec.dispatch"(%34)[^bb21, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb21(%35: !f):  // pred: ^bb20
      %36 = "exec.apply"(%arg0, %35, %11) <{binding = @field_equal, parameters = [], site = "overlap"}> : (!runtime.scope, !f, !f) -> !exec.outcome<(i1)>
      "exec.dispatch"(%36)[^bb22, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb22(%37: i1):  // pred: ^bb21
      %38 = "exec.apply"(%arg0, %37) <{binding = @bool_not, parameters = [], site = "disjoint"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%38)[^bb23, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb23(%39: i1):  // pred: ^bb22
      %40 = "exec.test"(%arg0, %39) <{site = "disjoint_coset"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%40)[^bb24, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb24(%41: i1):  // pred: ^bb23
      cf.cond_br %41, ^bb25, ^bb26
    ^bb25:  // pred: ^bb24
      %42 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "disjoint_coset"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%42)[^bb28, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb26:  // pred: ^bb24
      %43 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "disjoint_coset"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%43)[^bb31, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb27:  // 2 preds: ^bb30, ^bb33
      %44 = "exec.apply"(%arg0, %arg1, %1) <{binding = @sequence_at_9, parameters = [], site = "a"}> : (!runtime.scope, !ms, ui64) -> !exec.outcome<(!m)>
      "exec.dispatch"(%44)[^bb34, ^bb2] : (!exec.outcome<(!m)>) -> ()
    ^bb28(%45: !runtime.scope):  // pred: ^bb25
      %46 = call @control_2(%45) : (!runtime.scope) -> !exec.outcome<>
      %47 = "runtime.exit_scope"(%45, %46) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%47)[^bb29, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb29(%48: !runtime.transfer<>):  // pred: ^bb28
      %49 = "runtime.accept_transfer"(%arg0, %48) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%49)[^bb30, ^bb2] : (!exec.outcome<>) -> ()
    ^bb30:  // pred: ^bb29
      cf.br ^bb27
    ^bb31(%50: !runtime.scope):  // pred: ^bb26
      %51 = call @control_3(%50) : (!runtime.scope) -> !exec.outcome<>
      %52 = "runtime.exit_scope"(%50, %51) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%52)[^bb32, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb32(%53: !runtime.transfer<>):  // pred: ^bb31
      %54 = "runtime.accept_transfer"(%arg0, %53) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%54)[^bb33, ^bb2] : (!exec.outcome<>) -> ()
    ^bb33:  // pred: ^bb32
      cf.br ^bb27
    ^bb34(%55: !m):  // pred: ^bb27
      %56 = "exec.apply"(%arg0, %55, %arg2) <{binding = @matrix_mul_vector, parameters = [], site = "az"}> : (!runtime.scope, !m, !v) -> !exec.outcome<(!v)>
      "exec.dispatch"(%56)[^bb35, ^bb2] : (!exec.outcome<(!v)>) -> ()
    ^bb35(%57: !v):  // pred: ^bb34
      %58 = "exec.apply"(%arg0, %57) <{binding = @vector_length, parameters = [], site = "arows"}> : (!runtime.scope, !v) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%58)[^bb36, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb36(%59: ui64):  // pred: ^bb35
      %60 = "exec.apply"(%arg0, %59, %arg4) <{binding = @index_equal, parameters = [], site = "ashape"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%60)[^bb37, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb37(%61: i1):  // pred: ^bb36
      %62 = "exec.test"(%arg0, %61) <{site = "a_rows"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%62)[^bb38, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb38(%63: i1):  // pred: ^bb37
      cf.cond_br %63, ^bb39, ^bb40
    ^bb39:  // pred: ^bb38
      %64 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "a_rows"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%64)[^bb42, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb40:  // pred: ^bb38
      %65 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "a_rows"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%65)[^bb45, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb41:  // 2 preds: ^bb44, ^bb47
      %66 = "exec.apply"(%arg0, %57, %11) <{binding = @poly_coset_interpolate, parameters = [], site = "apoly"}> : (!runtime.scope, !v, !f) -> !exec.outcome<(!p)>
      "exec.dispatch"(%66)[^bb48, ^bb2] : (!exec.outcome<(!p)>) -> ()
    ^bb42(%67: !runtime.scope):  // pred: ^bb39
      %68 = call @control_4(%67) : (!runtime.scope) -> !exec.outcome<>
      %69 = "runtime.exit_scope"(%67, %68) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%69)[^bb43, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb43(%70: !runtime.transfer<>):  // pred: ^bb42
      %71 = "runtime.accept_transfer"(%arg0, %70) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%71)[^bb44, ^bb2] : (!exec.outcome<>) -> ()
    ^bb44:  // pred: ^bb43
      cf.br ^bb41
    ^bb45(%72: !runtime.scope):  // pred: ^bb40
      %73 = call @control_5(%72) : (!runtime.scope) -> !exec.outcome<>
      %74 = "runtime.exit_scope"(%72, %73) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%74)[^bb46, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb46(%75: !runtime.transfer<>):  // pred: ^bb45
      %76 = "runtime.accept_transfer"(%arg0, %75) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%76)[^bb47, ^bb2] : (!exec.outcome<>) -> ()
    ^bb47:  // pred: ^bb46
      cf.br ^bb41
    ^bb48(%77: !p):  // pred: ^bb41
      %78 = "exec.apply"(%arg0, %77, %arg3, %arg4) <{binding = @poly_coset_evaluate, parameters = [], site = "acoset"}> : (!runtime.scope, !p, !f, ui64) -> !exec.outcome<(!v)>
      "exec.dispatch"(%78)[^bb49, ^bb2] : (!exec.outcome<(!v)>) -> ()
    ^bb49(%79: !v):  // pred: ^bb48
      %80 = "exec.apply"(%arg0, %arg1, %5) <{binding = @sequence_at_9, parameters = [], site = "b"}> : (!runtime.scope, !ms, ui64) -> !exec.outcome<(!m)>
      "exec.dispatch"(%80)[^bb50, ^bb2] : (!exec.outcome<(!m)>) -> ()
    ^bb50(%81: !m):  // pred: ^bb49
      %82 = "exec.apply"(%arg0, %81, %arg2) <{binding = @matrix_mul_vector, parameters = [], site = "bz"}> : (!runtime.scope, !m, !v) -> !exec.outcome<(!v)>
      "exec.dispatch"(%82)[^bb51, ^bb2] : (!exec.outcome<(!v)>) -> ()
    ^bb51(%83: !v):  // pred: ^bb50
      %84 = "exec.apply"(%arg0, %83) <{binding = @vector_length, parameters = [], site = "brows"}> : (!runtime.scope, !v) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%84)[^bb52, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb52(%85: ui64):  // pred: ^bb51
      %86 = "exec.apply"(%arg0, %85, %arg4) <{binding = @index_equal, parameters = [], site = "bshape"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%86)[^bb53, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb53(%87: i1):  // pred: ^bb52
      %88 = "exec.test"(%arg0, %87) <{site = "b_rows"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%88)[^bb54, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb54(%89: i1):  // pred: ^bb53
      cf.cond_br %89, ^bb55, ^bb56
    ^bb55:  // pred: ^bb54
      %90 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "b_rows"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%90)[^bb58, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb56:  // pred: ^bb54
      %91 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "b_rows"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%91)[^bb61, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb57:  // 2 preds: ^bb60, ^bb63
      %92 = "exec.apply"(%arg0, %83, %11) <{binding = @poly_coset_interpolate, parameters = [], site = "bpoly"}> : (!runtime.scope, !v, !f) -> !exec.outcome<(!p)>
      "exec.dispatch"(%92)[^bb64, ^bb2] : (!exec.outcome<(!p)>) -> ()
    ^bb58(%93: !runtime.scope):  // pred: ^bb55
      %94 = call @control_6(%93) : (!runtime.scope) -> !exec.outcome<>
      %95 = "runtime.exit_scope"(%93, %94) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%95)[^bb59, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb59(%96: !runtime.transfer<>):  // pred: ^bb58
      %97 = "runtime.accept_transfer"(%arg0, %96) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%97)[^bb60, ^bb2] : (!exec.outcome<>) -> ()
    ^bb60:  // pred: ^bb59
      cf.br ^bb57
    ^bb61(%98: !runtime.scope):  // pred: ^bb56
      %99 = call @control_7(%98) : (!runtime.scope) -> !exec.outcome<>
      %100 = "runtime.exit_scope"(%98, %99) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%100)[^bb62, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb62(%101: !runtime.transfer<>):  // pred: ^bb61
      %102 = "runtime.accept_transfer"(%arg0, %101) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%102)[^bb63, ^bb2] : (!exec.outcome<>) -> ()
    ^bb63:  // pred: ^bb62
      cf.br ^bb57
    ^bb64(%103: !p):  // pred: ^bb57
      %104 = "exec.apply"(%arg0, %103, %arg3, %arg4) <{binding = @poly_coset_evaluate, parameters = [], site = "bcoset"}> : (!runtime.scope, !p, !f, ui64) -> !exec.outcome<(!v)>
      "exec.dispatch"(%104)[^bb65, ^bb2] : (!exec.outcome<(!v)>) -> ()
    ^bb65(%105: !v):  // pred: ^bb64
      %106 = "exec.apply"(%arg0, %arg1, %7) <{binding = @sequence_at_9, parameters = [], site = "c"}> : (!runtime.scope, !ms, ui64) -> !exec.outcome<(!m)>
      "exec.dispatch"(%106)[^bb66, ^bb2] : (!exec.outcome<(!m)>) -> ()
    ^bb66(%107: !m):  // pred: ^bb65
      %108 = "exec.apply"(%arg0, %107, %arg2) <{binding = @matrix_mul_vector, parameters = [], site = "cz"}> : (!runtime.scope, !m, !v) -> !exec.outcome<(!v)>
      "exec.dispatch"(%108)[^bb67, ^bb2] : (!exec.outcome<(!v)>) -> ()
    ^bb67(%109: !v):  // pred: ^bb66
      %110 = "exec.apply"(%arg0, %109) <{binding = @vector_length, parameters = [], site = "crows"}> : (!runtime.scope, !v) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%110)[^bb68, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb68(%111: ui64):  // pred: ^bb67
      %112 = "exec.apply"(%arg0, %111, %arg4) <{binding = @index_equal, parameters = [], site = "cshape"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%112)[^bb69, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb69(%113: i1):  // pred: ^bb68
      %114 = "exec.test"(%arg0, %113) <{site = "c_rows"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%114)[^bb70, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb70(%115: i1):  // pred: ^bb69
      cf.cond_br %115, ^bb71, ^bb72
    ^bb71:  // pred: ^bb70
      %116 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "c_rows"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%116)[^bb74, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb72:  // pred: ^bb70
      %117 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "c_rows"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%117)[^bb77, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb73:  // 2 preds: ^bb76, ^bb79
      %118 = "exec.apply"(%arg0, %109, %11) <{binding = @poly_coset_interpolate, parameters = [], site = "cpoly"}> : (!runtime.scope, !v, !f) -> !exec.outcome<(!p)>
      "exec.dispatch"(%118)[^bb80, ^bb2] : (!exec.outcome<(!p)>) -> ()
    ^bb74(%119: !runtime.scope):  // pred: ^bb71
      %120 = call @control_8(%119) : (!runtime.scope) -> !exec.outcome<>
      %121 = "runtime.exit_scope"(%119, %120) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%121)[^bb75, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb75(%122: !runtime.transfer<>):  // pred: ^bb74
      %123 = "runtime.accept_transfer"(%arg0, %122) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%123)[^bb76, ^bb2] : (!exec.outcome<>) -> ()
    ^bb76:  // pred: ^bb75
      cf.br ^bb73
    ^bb77(%124: !runtime.scope):  // pred: ^bb72
      %125 = call @control_9(%124) : (!runtime.scope) -> !exec.outcome<>
      %126 = "runtime.exit_scope"(%124, %125) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%126)[^bb78, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb78(%127: !runtime.transfer<>):  // pred: ^bb77
      %128 = "runtime.accept_transfer"(%arg0, %127) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%128)[^bb79, ^bb2] : (!exec.outcome<>) -> ()
    ^bb79:  // pred: ^bb78
      cf.br ^bb73
    ^bb80(%129: !p):  // pred: ^bb73
      %130 = "exec.apply"(%arg0, %129, %arg3, %arg4) <{binding = @poly_coset_evaluate, parameters = [], site = "ccoset"}> : (!runtime.scope, !p, !f, ui64) -> !exec.outcome<(!v)>
      "exec.dispatch"(%130)[^bb81, ^bb2] : (!exec.outcome<(!v)>) -> ()
    ^bb81(%131: !v):  // pred: ^bb80
      %132 = "exec.apply"(%arg0, %57, %83) <{binding = @vector_mul, parameters = [], site = "products"}> : (!runtime.scope, !v, !v) -> !exec.outcome<(!v)>
      "exec.dispatch"(%132)[^bb82, ^bb2] : (!exec.outcome<(!v)>) -> ()
    ^bb82(%133: !v):  // pred: ^bb81
      %134 = "exec.apply"(%arg0, %133, %109) <{binding = @vector_equal, parameters = [], site = "valid"}> : (!runtime.scope, !v, !v) -> !exec.outcome<(i1)>
      "exec.dispatch"(%134)[^bb83, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb83(%135: i1):  // pred: ^bb82
      %136 = "exec.apply"(%arg0, %79, %105) <{binding = @vector_mul, parameters = [], site = "coset_products"}> : (!runtime.scope, !v, !v) -> !exec.outcome<(!v)>
      "exec.dispatch"(%136)[^bb84, ^bb2] : (!exec.outcome<(!v)>) -> ()
    ^bb84(%137: !v):  // pred: ^bb83
      %138 = "exec.apply"(%arg0, %137, %131) <{binding = @vector_sub, parameters = [], site = "out"}> : (!runtime.scope, !v, !v) -> !exec.outcome<(!v)>
      "exec.dispatch"(%138)[^bb85, ^bb2] : (!exec.outcome<(!v)>) -> ()
    ^bb85(%139: !v):  // pred: ^bb84
      %140 = "exec.returned"(%139, %135) : (!v, i1) -> !exec.outcome<(!v, i1)>
      return %140 : !exec.outcome<(!v, i1)>
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
      %0 = "exec.reject"(%arg0) <{reason = "reject", site = "disjoint_coset_reject"}> : (!runtime.scope) -> !exec.stop
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
      %0 = "exec.reject"(%arg0) <{reason = "reject", site = "a_rows_reject"}> : (!runtime.scope) -> !exec.stop
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
      %0 = "exec.reject"(%arg0) <{reason = "reject", site = "b_rows_reject"}> : (!runtime.scope) -> !exec.stop
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
      %0 = "exec.reject"(%arg0) <{reason = "reject", site = "c_rows_reject"}> : (!runtime.scope) -> !exec.stop
      cf.br ^bb1(%0 : !exec.stop)
    ^bb1(%1: !exec.stop):  // pred: ^bb0
      %2 = "exec.failed"(%1) : (!exec.stop) -> !exec.outcome<>
      return %2 : !exec.outcome<>
    }
    func.func @contract(%arg0: !runtime.scope, %arg1: !v, %arg2: !gs) -> !exec.outcome<(!g)> attributes {no_inline, runtime.origin = ["contract", []]} {
      %0 = "exec.apply"(%arg0, %arg1, %arg2) <{binding = @curve_msm_17, parameters = [], site = "point"}> : (!runtime.scope, !v, !gs) -> !exec.outcome<(!g)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!g)>) -> ()
    ^bb1(%1: !g):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!g) -> !exec.outcome<(!g)>
      return %2 : !exec.outcome<(!g)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!g)>
      return %4 : !exec.outcome<(!g)>
    }
    func.func @public_prefix(%arg0: !runtime.scope, %arg1: !v, %arg2: !v) -> !exec.outcome<(i1)> attributes {no_inline, runtime.origin = ["public_prefix", []]} {
      %0 = "exec.apply"(%arg0) <{binding = @index_constant, parameters = ["0"], site = "zero"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1: ui64):  // pred: ^bb0
      %2 = "exec.apply"(%arg0) <{binding = @index_constant, parameters = ["1"], site = "one_index"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%3: !exec.stop):  // 9 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(i1)>
      return %4 : !exec.outcome<(i1)>
    ^bb3(%5: ui64):  // pred: ^bb1
      %6 = "exec.apply"(%arg0) <{binding = @field_constant, parameters = ["1"], site = "one"}> : (!runtime.scope) -> !exec.outcome<(!f)>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb4(%7: !f):  // pred: ^bb3
      %8 = "exec.apply"(%arg0, %arg1, %1) <{binding = @vector_get, parameters = [], site = "first"}> : (!runtime.scope, !v, ui64) -> !exec.outcome<(!f)>
      "exec.dispatch"(%8)[^bb5, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb5(%9: !f):  // pred: ^bb4
      %10 = "exec.apply"(%arg0, %9, %7) <{binding = @field_equal, parameters = [], site = "one_valid"}> : (!runtime.scope, !f, !f) -> !exec.outcome<(i1)>
      "exec.dispatch"(%10)[^bb6, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb6(%11: i1):  // pred: ^bb5
      %12 = "exec.apply"(%arg0, %arg2) <{binding = @vector_length, parameters = [], site = "count"}> : (!runtime.scope, !v) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%12)[^bb7, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb7(%13: ui64):  // pred: ^bb6
      %14 = "exec.apply"(%arg0, %arg1, %5, %13) <{binding = @vector_slice, parameters = [], site = "prefix"}> : (!runtime.scope, !v, ui64, ui64) -> !exec.outcome<(!v)>
      "exec.dispatch"(%14)[^bb8, ^bb2] : (!exec.outcome<(!v)>) -> ()
    ^bb8(%15: !v):  // pred: ^bb7
      %16 = "exec.apply"(%arg0, %15, %arg2) <{binding = @vector_equal, parameters = [], site = "prefix_valid"}> : (!runtime.scope, !v, !v) -> !exec.outcome<(i1)>
      "exec.dispatch"(%16)[^bb9, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb9(%17: i1):  // pred: ^bb8
      %18 = "exec.apply"(%arg0, %17, %11) <{binding = @bool_and, parameters = [], site = "valid"}> : (!runtime.scope, i1, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%18)[^bb10, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb10(%19: i1):  // pred: ^bb9
      %20 = "exec.returned"(%19) : (i1) -> !exec.outcome<(i1)>
      return %20 : !exec.outcome<(i1)>
    }



"protocol.func"() ({ ^entry(%matrices:!ms,%public:!v,%w:!v,%query:!gs,%g2:!g2,%shift:!f,%n:ui64):
 protocol.statement @relation(%matrices,%public,%w,%query,%g2,%shift,%n) {selectors=["V","V","P","V","V","V","V"],acceptance=0:i64} : !ms,!v,!v,!gs,!g2,!f,ui64
 %computed:2 = "protocol.local_call"(%matrices,%w,%shift,%n) {callee=@numerator,role="P",site="producer_numerator"} : (!ms,!v,!f,ui64)->(!v,i1)
 %point = "protocol.local_call"(%computed#0,%query) {callee=@contract,role="P",site="producer_msm"} : (!v,!gs)->!g
 %target = algebra.pairing %point,%g2 : (!g,!g2)->!gt
 %received = protocol.exchange %w {sender="P",receiver="V",site="witness"} : !v
 %received_point = protocol.exchange %point {sender="P",receiver="V",site="point"} : !g
 %received_target = protocol.exchange %target {sender="P",receiver="V",site="target"} : !gt
 %checked:2 = "protocol.local_call"(%matrices,%received,%shift,%n) {callee=@numerator,role="V",site="validator_numerator"} : (!ms,!v,!f,ui64)->(!v,i1)
 %expected = "protocol.local_call"(%checked#0,%query) {callee=@contract,role="V",site="validator_msm"} : (!v,!gs)->!g
 %prefix = "protocol.local_call"(%received,%public) {callee=@public_prefix,role="V",site="public_prefix"} : (!v,!v)->i1
 %expected_target = algebra.pairing %expected,%g2 : (!g,!g2)->!gt
 %point_ok = algebra.group_equal %expected,%received_point : (!g,!g)->i1
 %target_ok = algebra.group_equal %expected_target,%received_target : (!gt,!gt)->i1
 %a = arith.andi %point_ok,%target_ok : i1
 %b = arith.andi %prefix,%checked#1 : i1
 %valid = arith.andi %a,%b : i1
 "protocol.return"(%valid) : (i1)->()
}) {sym_name="main",function_type=(!ms,!v,!v,!gs,!g2,!f,ui64)->i1,roles=["P","V"],input_roles=[["P","V"],["V"],["P"],["P","V"],["P","V"],["P","V"],["P","V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
