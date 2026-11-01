!F = !algebra.field<"bls12-381.fr">
!V = !data.field_vector<"bls12-381.fr">
!S = !runtime.scope
module {
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "protocol.func"() <{function_type = (!F, !F, !F, !F, ui64, ui64, i1) -> (!F, !F), input_roles = [["Owner"], ["Owner"], ["Owner"], ["Owner"], ["Owner"], ["Owner"], ["Owner"]], origin = ["entry", []], output_roles = [["Owner"], ["Owner"]], roles = ["Owner"], sym_name = "entry"}> ({
    ^bb0(%arg0: !F, %arg1: !F, %arg2: !F, %arg3: !F, %arg4: ui64, %arg5: ui64, %arg6: i1):
      %0:2 = "protocol.local_call"(%arg0, %arg1, %arg2, %arg3, %arg4, %arg5, %arg6) <{callee = @control, role = "Owner", site = "invoke"}> : (!F, !F, !F, !F, ui64, ui64, i1) -> (!F, !F)
      "protocol.return"(%0#0, %0#1) : (!F, !F) -> ()
    }) : () -> ()
    func.func private @swap(%arg0: !S, %arg1: !F, %arg2: !F) -> !exec.outcome<(!F, !F)> attributes {no_inline, runtime.origin = ["original_swap", [["Field", "bls12-381.fr"], ["Group", "bls12-381.g1"]]]} {
      %0 = "exec.returned"(%arg2, %arg1) : (!F, !F) -> !exec.outcome<(!F, !F)>
      return %0 : !exec.outcome<(!F, !F)>
    }
    func.func @control(%arg0: !S, %arg1: !F, %arg2: !F, %arg3: !F, %arg4: !F, %arg5: ui64, %arg6: ui64, %arg7: i1) -> !exec.outcome<(!F, !F)> attributes {no_inline, runtime.origin = ["control", []]} {
      %0 = "exec.range"(%arg0, %arg5, %arg6) <{site = "loop"}> : (!S, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(i64, i64)>) -> ()
    ^bb1(%1: i64, %2: i64):
      %3 = "runtime.borrow_transfer"(%arg0, %arg1, %arg2) : (!S, !F, !F) -> !runtime.transfer<(!F, !F)>
      cf.br ^bb3(%1, %3 : i64, !runtime.transfer<(!F, !F)>)
    ^bb2(%4: !exec.stop):
      %5 = "exec.failed"(%4) : (!exec.stop) -> !exec.outcome<(!F, !F)>
      return %5 : !exec.outcome<(!F, !F)>
    ^bb3(%6: i64, %7: !runtime.transfer<(!F, !F)>):
      %8 = arith.cmpi ult, %6, %2 : i64
      cf.cond_br %8, ^bb4, ^bb5(%7 : !runtime.transfer<(!F, !F)>)
    ^bb4:
      %9 = "runtime.iteration"(%arg0, %6) <{site = "loop"}> : (!S, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%9)[^bb8, ^bb7] : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%10: !runtime.transfer<(!F, !F)>):
      %11 = "runtime.accept_transfer"(%arg0, %10) : (!S, !runtime.transfer<(!F, !F)>) -> !exec.outcome<(!F, !F)>
      "exec.dispatch"(%11)[^bb11, ^bb2] : (!exec.outcome<(!F, !F)>) -> ()
    ^bb6(%12: !runtime.transfer<(!F, !F)>):
      %c1_i64 = arith.constant 1 : i64
      %13 = arith.addi %6, %c1_i64 : i64
      cf.br ^bb3(%13, %12 : i64, !runtime.transfer<(!F, !F)>)
    ^bb7(%14: !exec.stop):
      "runtime.release_transfer"(%7) : (!runtime.transfer<(!F, !F)>) -> ()
      cf.br ^bb2(%14 : !exec.stop)
    ^bb8(%15: ui64):
      %16:2 = "runtime.transfer_values"(%7) : (!runtime.transfer<(!F, !F)>) -> (!F, !F)
      %17 = "runtime.enter_scope"(%arg0, %6, %15, %16#0, %16#1, %arg3, %arg4, %arg7) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 6>, site = "loop"}> : (!S, i64, ui64, !F, !F, !F, !F, i1) -> !exec.outcome<(!S)>
      "exec.dispatch"(%17)[^bb9, ^bb7] : (!exec.outcome<(!S)>) -> ()
    ^bb9(%18: !S):
      %19 = call @control_0(%18, %15, %16#0, %16#1, %arg3, %arg4, %arg7) : (!S, ui64, !F, !F, !F, !F, i1) -> !exec.outcome<(!F, !F)>
      %20 = "runtime.exit_scope"(%18, %19) : (!S, !exec.outcome<(!F, !F)>) -> !exec.outcome<(!runtime.transfer<(!F, !F)>)>
      "exec.dispatch"(%20)[^bb10, ^bb7] : (!exec.outcome<(!runtime.transfer<(!F, !F)>)>) -> ()
    ^bb10(%21: !runtime.transfer<(!F, !F)>):
      "runtime.release_transfer"(%7) : (!runtime.transfer<(!F, !F)>) -> ()
      cf.br ^bb6(%21 : !runtime.transfer<(!F, !F)>)
    ^bb11(%22: !F, %23: !F):
      %24 = "exec.range"(%arg0, %arg5, %arg6) <{site = "empty_loop"}> : (!S, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%24)[^bb12, ^bb2] : (!exec.outcome<(i64, i64)>) -> ()
    ^bb12(%25: i64, %26: i64):
      %27 = "runtime.borrow_transfer"(%arg0) : (!S) -> !runtime.transfer<>
      cf.br ^bb13(%25, %27 : i64, !runtime.transfer<>)
    ^bb13(%28: i64, %29: !runtime.transfer<>):
      %30 = arith.cmpi ult, %28, %26 : i64
      cf.cond_br %30, ^bb14, ^bb15(%29 : !runtime.transfer<>)
    ^bb14:
      %31 = "runtime.iteration"(%arg0, %28) <{site = "empty_loop"}> : (!S, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%31)[^bb18, ^bb17] : (!exec.outcome<(ui64)>) -> ()
    ^bb15(%32: !runtime.transfer<>):
      %33 = "runtime.accept_transfer"(%arg0, %32) : (!S, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%33)[^bb21, ^bb2] : (!exec.outcome<>) -> ()
    ^bb16(%34: !runtime.transfer<>):
      %c1_i64_0 = arith.constant 1 : i64
      %35 = arith.addi %28, %c1_i64_0 : i64
      cf.br ^bb13(%35, %34 : i64, !runtime.transfer<>)
    ^bb17(%36: !exec.stop):
      "runtime.release_transfer"(%29) : (!runtime.transfer<>) -> ()
      cf.br ^bb2(%36 : !exec.stop)
    ^bb18(%37: ui64):
      "runtime.transfer_values"(%29) : (!runtime.transfer<>) -> ()
      %38 = "runtime.enter_scope"(%arg0, %28, %37, %arg7) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 2>, site = "empty_loop"}> : (!S, i64, ui64, i1) -> !exec.outcome<(!S)>
      "exec.dispatch"(%38)[^bb19, ^bb17] : (!exec.outcome<(!S)>) -> ()
    ^bb19(%39: !S):
      %40 = call @control_3(%39, %37, %arg7) : (!S, ui64, i1) -> !exec.outcome<>
      %41 = "runtime.exit_scope"(%39, %40) : (!S, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%41)[^bb20, ^bb17] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb20(%42: !runtime.transfer<>):
      "runtime.release_transfer"(%29) : (!runtime.transfer<>) -> ()
      cf.br ^bb16(%42 : !runtime.transfer<>)
    ^bb21:
      %43 = "exec.range"(%arg0, %arg5, %arg6) <{site = "conditional_loop"}> : (!S, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%43)[^bb22, ^bb2] : (!exec.outcome<(i64, i64)>) -> ()
    ^bb22(%44: i64, %45: i64):
      %46 = "runtime.borrow_transfer"(%arg0, %22, %23) : (!S, !F, !F) -> !runtime.transfer<(!F, !F)>
      cf.br ^bb23(%44, %46 : i64, !runtime.transfer<(!F, !F)>)
    ^bb23(%47: i64, %48: !runtime.transfer<(!F, !F)>):
      %49 = arith.cmpi ult, %47, %45 : i64
      cf.cond_br %49, ^bb24, ^bb25(%48 : !runtime.transfer<(!F, !F)>)
    ^bb24:
      %50 = "runtime.iteration"(%arg0, %47) <{site = "conditional_loop"}> : (!S, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%50)[^bb28, ^bb27] : (!exec.outcome<(ui64)>) -> ()
    ^bb25(%51: !runtime.transfer<(!F, !F)>):
      %52 = "runtime.accept_transfer"(%arg0, %51) : (!S, !runtime.transfer<(!F, !F)>) -> !exec.outcome<(!F, !F)>
      "exec.dispatch"(%52)[^bb32, ^bb2] : (!exec.outcome<(!F, !F)>) -> ()
    ^bb26(%53: !runtime.transfer<(!F, !F)>):
      %c1_i64_1 = arith.constant 1 : i64
      %54 = arith.addi %47, %c1_i64_1 : i64
      cf.br ^bb23(%54, %53 : i64, !runtime.transfer<(!F, !F)>)
    ^bb27(%55: !exec.stop):
      "runtime.release_transfer"(%48) : (!runtime.transfer<(!F, !F)>) -> ()
      cf.br ^bb2(%55 : !exec.stop)
    ^bb28(%56: ui64):
      %57:2 = "runtime.transfer_values"(%48) : (!runtime.transfer<(!F, !F)>) -> (!F, !F)
      %58 = "runtime.enter_scope"(%arg0, %47, %56, %57#0, %57#1, %arg3, %arg4, %arg7) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 6>, site = "conditional_loop"}> : (!S, i64, ui64, !F, !F, !F, !F, i1) -> !exec.outcome<(!S)>
      "exec.dispatch"(%58)[^bb29, ^bb27] : (!exec.outcome<(!S)>) -> ()
    ^bb29(%59: !S):
      %60 = call @control_6(%59, %56, %57#0, %57#1, %arg3, %arg4, %arg7) : (!S, ui64, !F, !F, !F, !F, i1) -> !exec.outcome<(i1, !F, !F)>
      %61 = "runtime.exit_scope"(%59, %60) : (!S, !exec.outcome<(i1, !F, !F)>) -> !exec.outcome<(!runtime.transfer<(i1, !F, !F)>)>
      "exec.dispatch"(%61)[^bb30, ^bb27] : (!exec.outcome<(!runtime.transfer<(i1, !F, !F)>)>) -> ()
    ^bb30(%62: !runtime.transfer<(i1, !F, !F)>):
      "runtime.release_transfer"(%48) : (!runtime.transfer<(!F, !F)>) -> ()
      %63 = "runtime.take_condition"(%62) : (!runtime.transfer<(i1, !F, !F)>) -> !exec.outcome<(i1, !runtime.transfer<(!F, !F)>)>
      "exec.dispatch"(%63)[^bb31, ^bb2] : (!exec.outcome<(i1, !runtime.transfer<(!F, !F)>)>) -> ()
    ^bb31(%64: i1, %65: !runtime.transfer<(!F, !F)>):
      cf.cond_br %64, ^bb26(%65 : !runtime.transfer<(!F, !F)>), ^bb25(%65 : !runtime.transfer<(!F, !F)>)
    ^bb32(%66: !F, %67: !F):
      %68 = call @swap(%arg0, %66, %67) {runtime.site = "first"} : (!S, !F, !F) -> !exec.outcome<(!F, !F)>
      "exec.dispatch"(%68)[^bb33, ^bb2] : (!exec.outcome<(!F, !F)>) -> ()
    ^bb33(%69: !F, %70: !F):
      %71 = call @swap(%arg0, %arg3, %arg4) {runtime.site = "second"} : (!S, !F, !F) -> !exec.outcome<(!F, !F)>
      "exec.dispatch"(%71)[^bb34, ^bb2] : (!exec.outcome<(!F, !F)>) -> ()
    ^bb34(%72: !F, %73: !F):
      %74 = "exec.returned"(%69, %73) : (!F, !F) -> !exec.outcome<(!F, !F)>
      return %74 : !exec.outcome<(!F, !F)>
    }
    func.func private @control_0(%arg0: !S, %arg1: ui64, %arg2: !F, %arg3: !F, %arg4: !F, %arg5: !F, %arg6: i1) -> !exec.outcome<(!F, !F)> attributes {no_inline, runtime.region} {
      %0 = "exec.test"(%arg0, %arg6) <{site = "choose"}> : (!S, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1: i1):
      cf.cond_br %1, ^bb3, ^bb4
    ^bb2(%2: !exec.stop):
      %3 = "exec.failed"(%2) : (!exec.stop) -> !exec.outcome<(!F, !F)>
      return %3 : !exec.outcome<(!F, !F)>
    ^bb3:
      %4 = "runtime.enter_scope"(%arg0, %arg2, %arg3, %arg4, %arg5) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 4>, selection = "then", site = "choose"}> : (!S, !F, !F, !F, !F) -> !exec.outcome<(!S)>
      "exec.dispatch"(%4)[^bb6, ^bb2] : (!exec.outcome<(!S)>) -> ()
    ^bb4:
      %5 = "runtime.enter_scope"(%arg0, %arg2, %arg3, %arg4, %arg5) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 4>, selection = "else", site = "choose"}> : (!S, !F, !F, !F, !F) -> !exec.outcome<(!S)>
      "exec.dispatch"(%5)[^bb9, ^bb2] : (!exec.outcome<(!S)>) -> ()
    ^bb5(%6: !F, %7: !F):
      %8 = "exec.complete"(%arg0, %7, %6) : (!S, !F, !F) -> !exec.outcome<(!F, !F)>
      return %8 : !exec.outcome<(!F, !F)>
    ^bb6(%9: !S):
      %10 = call @control_1(%9, %arg2, %arg3, %arg4, %arg5) : (!S, !F, !F, !F, !F) -> !exec.outcome<(!F, !F)>
      %11 = "runtime.exit_scope"(%9, %10) : (!S, !exec.outcome<(!F, !F)>) -> !exec.outcome<(!runtime.transfer<(!F, !F)>)>
      "exec.dispatch"(%11)[^bb7, ^bb2] : (!exec.outcome<(!runtime.transfer<(!F, !F)>)>) -> ()
    ^bb7(%12: !runtime.transfer<(!F, !F)>):
      %13 = "runtime.accept_transfer"(%arg0, %12) : (!S, !runtime.transfer<(!F, !F)>) -> !exec.outcome<(!F, !F)>
      "exec.dispatch"(%13)[^bb8, ^bb2] : (!exec.outcome<(!F, !F)>) -> ()
    ^bb8(%14: !F, %15: !F):
      cf.br ^bb5(%14, %15 : !F, !F)
    ^bb9(%16: !S):
      %17 = call @control_2(%16, %arg2, %arg3, %arg4, %arg5) : (!S, !F, !F, !F, !F) -> !exec.outcome<(!F, !F)>
      %18 = "runtime.exit_scope"(%16, %17) : (!S, !exec.outcome<(!F, !F)>) -> !exec.outcome<(!runtime.transfer<(!F, !F)>)>
      "exec.dispatch"(%18)[^bb10, ^bb2] : (!exec.outcome<(!runtime.transfer<(!F, !F)>)>) -> ()
    ^bb10(%19: !runtime.transfer<(!F, !F)>):
      %20 = "runtime.accept_transfer"(%arg0, %19) : (!S, !runtime.transfer<(!F, !F)>) -> !exec.outcome<(!F, !F)>
      "exec.dispatch"(%20)[^bb11, ^bb2] : (!exec.outcome<(!F, !F)>) -> ()
    ^bb11(%21: !F, %22: !F):
      cf.br ^bb5(%21, %22 : !F, !F)
    }
    func.func private @control_1(%arg0: !S, %arg1: !F, %arg2: !F, %arg3: !F, %arg4: !F) -> !exec.outcome<(!F, !F)> attributes {no_inline, runtime.region} {
      %0 = "exec.complete"(%arg0, %arg3, %arg2) : (!S, !F, !F) -> !exec.outcome<(!F, !F)>
      return %0 : !exec.outcome<(!F, !F)>
    }
    func.func private @control_2(%arg0: !S, %arg1: !F, %arg2: !F, %arg3: !F, %arg4: !F) -> !exec.outcome<(!F, !F)> attributes {no_inline, runtime.region} {
      %0 = "exec.complete"(%arg0, %arg1, %arg4) : (!S, !F, !F) -> !exec.outcome<(!F, !F)>
      return %0 : !exec.outcome<(!F, !F)>
    }
    func.func private @control_3(%arg0: !S, %arg1: ui64, %arg2: i1) -> !exec.outcome<> attributes {no_inline, runtime.region} {
      %0 = "exec.test"(%arg0, %arg2) <{site = "check"}> : (!S, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1: i1):
      cf.cond_br %1, ^bb3, ^bb4
    ^bb2(%2: !exec.stop):
      %3 = "exec.failed"(%2) : (!exec.stop) -> !exec.outcome<>
      return %3 : !exec.outcome<>
    ^bb3:
      %4 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "check"}> : (!S) -> !exec.outcome<(!S)>
      "exec.dispatch"(%4)[^bb6, ^bb2] : (!exec.outcome<(!S)>) -> ()
    ^bb4:
      %5 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "check"}> : (!S) -> !exec.outcome<(!S)>
      "exec.dispatch"(%5)[^bb9, ^bb2] : (!exec.outcome<(!S)>) -> ()
    ^bb5:
      %6 = "exec.complete"(%arg0) : (!S) -> !exec.outcome<>
      return %6 : !exec.outcome<>
    ^bb6(%7: !S):
      %8 = call @control_4(%7) : (!S) -> !exec.outcome<>
      %9 = "runtime.exit_scope"(%7, %8) : (!S, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%9)[^bb7, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb7(%10: !runtime.transfer<>):
      %11 = "runtime.accept_transfer"(%arg0, %10) : (!S, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%11)[^bb8, ^bb2] : (!exec.outcome<>) -> ()
    ^bb8:
      cf.br ^bb5
    ^bb9(%12: !S):
      %13 = call @control_5(%12) : (!S) -> !exec.outcome<>
      %14 = "runtime.exit_scope"(%12, %13) : (!S, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%14)[^bb10, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb10(%15: !runtime.transfer<>):
      %16 = "runtime.accept_transfer"(%arg0, %15) : (!S, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%16)[^bb11, ^bb2] : (!exec.outcome<>) -> ()
    ^bb11:
      cf.br ^bb5
    }
    func.func private @control_4(%arg0: !S) -> !exec.outcome<> attributes {no_inline, runtime.region} {
      %0 = "exec.complete"(%arg0) : (!S) -> !exec.outcome<>
      return %0 : !exec.outcome<>
    }
    func.func private @control_5(%arg0: !S) -> !exec.outcome<> attributes {no_inline, runtime.region} {
      %0 = "exec.reject"(%arg0) <{reason = "reject", site = "check_failed"}> : (!S) -> !exec.stop
      cf.br ^bb1(%0 : !exec.stop)
    ^bb1(%1: !exec.stop):
      %2 = "exec.failed"(%1) : (!exec.stop) -> !exec.outcome<>
      return %2 : !exec.outcome<>
    }
    func.func private @control_6(%arg0: !S, %arg1: ui64, %arg2: !F, %arg3: !F, %arg4: !F, %arg5: !F, %arg6: i1) -> !exec.outcome<(i1, !F, !F)> attributes {no_inline, runtime.region} {
      %0 = "exec.complete"(%arg0, %arg6, %arg3, %arg2) : (!S, i1, !F, !F) -> !exec.outcome<(i1, !F, !F)>
      return %0 : !exec.outcome<(i1, !F, !F)>
    }
  }) : () -> ()
}
