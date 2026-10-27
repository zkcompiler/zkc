!message = !data.variant<"variant:5b227a6b632e76617269616e742f30222c5b224f70656e696e67222c226e6f6e65222c5b5d2c5b2231222c2232225d2c22736f6d65222c226669656c643a626c7331322d3338312e6672222c2270726f6f663a6d756c74696c696e6561722e6b7a672e626c7331322d3338312f30222c5b2235222c2236225d2c5b2234222c2237225d2c5b2233222c2238225d2c5b2230222c2239225d5d5d">
!pk = !commitment.polynomial<"multilinear.kzg.bls12-381/0", "prover_key">
!vk = !commitment.polynomial<"multilinear.kzg.bls12-381/0", "verifier_key">
!c = !commitment.polynomial<"multilinear.kzg.bls12-381/0", "commitment">
!o = !commitment.polynomial<"multilinear.kzg.bls12-381/0", "opening_state">
!proof = !commitment.polynomial<"multilinear.kzg.bls12-381/0", "proof">
!f = !algebra.field<"bls12-381.fr">
!t = !poly.multilinear<"bls12-381.fr">
!p = !poly.point<"bls12-381.fr">
!batch = !data.sequence<!message>
!fs = !algebra.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
 "runtime.binding"() {sym_name="empty",contract="sequence.empty",arguments=["variant:5b227a6b632e76617269616e742f30222c5b224f70656e696e67222c226e6f6e65222c5b5d2c5b2231222c2232225d2c22736f6d65222c226669656c643a626c7331322d3338312e6672222c2270726f6f663a6d756c74696c696e6561722e6b7a672e626c7331322d3338312f30222c5b2235222c2236225d2c5b2234222c2237225d2c5b2233222c2238225d2c5b2230222c2239225d5d5d"],implementation=""} : ()->()
 "runtime.binding"() {sym_name="append",contract="sequence.append",arguments=["variant:5b227a6b632e76617269616e742f30222c5b224f70656e696e67222c226e6f6e65222c5b5d2c5b2231222c2232225d2c22736f6d65222c226669656c643a626c7331322d3338312e6672222c2270726f6f663a6d756c74696c696e6561722e6b7a672e626c7331322d3338312f30222c5b2235222c2236225d2c5b2234222c2237225d2c5b2233222c2238225d2c5b2230222c2239225d5d5d"],implementation=""} : ()->()
 "runtime.binding"() {sym_name="length",contract="sequence.length",arguments=["variant:5b227a6b632e76617269616e742f30222c5b224f70656e696e67222c226e6f6e65222c5b5d2c5b2231222c2232225d2c22736f6d65222c226669656c643a626c7331322d3338312e6672222c2270726f6f663a6d756c74696c696e6561722e6b7a672e626c7331322d3338312f30222c5b2235222c2236225d2c5b2234222c2237225d2c5b2233222c2238225d2c5b2230222c2239225d5d5d"],implementation=""} : ()->()
 "runtime.binding"() {sym_name="at",contract="sequence.at",arguments=["variant:5b227a6b632e76617269616e742f30222c5b224f70656e696e67222c226e6f6e65222c5b5d2c5b2231222c2232225d2c22736f6d65222c226669656c643a626c7331322d3338312e6672222c2270726f6f663a6d756c74696c696e6561722e6b7a672e626c7331322d3338312f30222c5b2235222c2236225d2c5b2234222c2237225d2c5b2233222c2238225d2c5b2230222c2239225d5d5d"],implementation=""} : ()->()
 "runtime.binding"() {sym_name="constant",contract="index.constant",arguments=[],implementation=""} : ()->()
 "runtime.binding"() {sym_name="equal",contract="index.equal",arguments=[],implementation=""} : ()->()
 "runtime.binding"() {sym_name="and",contract="bool.and",arguments=[],implementation=""} : ()->()
 "runtime.binding"() {sym_name="vlength",contract="vector.length",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "runtime.binding"() {sym_name="get",contract="vector.get",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "runtime.binding"() {sym_name="point",contract="poly.empty_point",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "runtime.binding"() {sym_name="coordinate",contract="poly.append_point",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "runtime.binding"() {sym_name="commit",contract="pcs.commit",arguments=["multilinear.kzg.bls12-381/0"],implementation=""} : ()->()
 "runtime.binding"() {sym_name="open",contract="pcs.open",arguments=["multilinear.kzg.bls12-381/0"],implementation=""} : ()->()
 "runtime.binding"() {sym_name="check",contract="pcs.check",arguments=["multilinear.kzg.bls12-381/0"],implementation=""} : ()->()
    func.func @produce(%arg0: !runtime.scope, %arg1: !t, %arg2: !pk, %arg3: !fs) -> !exec.outcome<(!batch)> attributes {no_inline, runtime.origin = ["produce", []]} {
      %0 = "exec.apply"(%arg0, %arg2, %arg1) <{binding = @commit, parameters = [], site = "commit"}> : (!runtime.scope, !pk, !t) -> !exec.outcome<(!c, !o)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!c, !o)>) -> ()
    ^bb1(%1: !c, %2: !o):  // pred: ^bb0
      %3 = "exec.apply"(%arg0) <{binding = @empty, parameters = [], site = "empty"}> : (!runtime.scope) -> !exec.outcome<(!batch)>
      "exec.dispatch"(%3)[^bb3, ^bb2] : (!exec.outcome<(!batch)>) -> ()
    ^bb2(%4: !exec.stop):  // 7 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb9, ^bb11
      %5 = "exec.failed"(%4) : (!exec.stop) -> !exec.outcome<(!batch)>
      return %5 : !exec.outcome<(!batch)>
    ^bb3(%6: !batch):  // pred: ^bb1
      %7 = "exec.apply"(%arg0, %arg3) <{binding = @vlength, parameters = [], site = "count"}> : (!runtime.scope, !fs) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%7)[^bb4, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%8: ui64):  // pred: ^bb3
      %9 = "exec.apply"(%arg0) <{binding = @constant, parameters = ["0"], site = "zero"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%9)[^bb5, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%10: ui64):  // pred: ^bb4
      %11 = "exec.range"(%arg0, %10, %8) <{site = "openings"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%11)[^bb6, ^bb2] : (!exec.outcome<(i64, i64)>) -> ()
    ^bb6(%12: i64, %13: i64):  // pred: ^bb5
      %14 = "runtime.borrow_transfer"(%arg0, %6) : (!runtime.scope, !batch) -> !runtime.transfer<(!batch)>
      cf.br ^bb7(%12, %14 : i64, !runtime.transfer<(!batch)>)
    ^bb7(%15: i64, %16: !runtime.transfer<(!batch)>):  // 2 preds: ^bb6, ^bb10
      %17 = arith.cmpi ult, %15, %13 : i64
      cf.cond_br %17, ^bb8, ^bb9(%16 : !runtime.transfer<(!batch)>)
    ^bb8:  // pred: ^bb7
      %18 = "runtime.iteration"(%arg0, %15) <{site = "openings"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%18)[^bb12, ^bb11] : (!exec.outcome<(ui64)>) -> ()
    ^bb9(%19: !runtime.transfer<(!batch)>):  // pred: ^bb7
      %20 = "runtime.accept_transfer"(%arg0, %19) : (!runtime.scope, !runtime.transfer<(!batch)>) -> !exec.outcome<(!batch)>
      "exec.dispatch"(%20)[^bb15, ^bb2] : (!exec.outcome<(!batch)>) -> ()
    ^bb10(%21: !runtime.transfer<(!batch)>):  // pred: ^bb14
      %c1_i64 = arith.constant 1 : i64
      %22 = arith.addi %15, %c1_i64 : i64
      cf.br ^bb7(%22, %21 : i64, !runtime.transfer<(!batch)>)
    ^bb11(%23: !exec.stop):  // 3 preds: ^bb8, ^bb12, ^bb13
      "runtime.release_transfer"(%16) : (!runtime.transfer<(!batch)>) -> ()
      cf.br ^bb2(%23 : !exec.stop)
    ^bb12(%24: ui64):  // pred: ^bb8
      %25 = "runtime.transfer_values"(%16) : (!runtime.transfer<(!batch)>) -> !batch
      %26 = "runtime.enter_scope"(%arg0, %15, %24, %25, %2, %arg3) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 4>, site = "openings"}> : (!runtime.scope, i64, ui64, !batch, !o, !fs) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%26)[^bb13, ^bb11] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb13(%27: !runtime.scope):  // pred: ^bb12
      %28 = call @control_0(%27, %24, %25, %2, %arg3) : (!runtime.scope, ui64, !batch, !o, !fs) -> !exec.outcome<(!batch)>
      %29 = "runtime.exit_scope"(%27, %28) : (!runtime.scope, !exec.outcome<(!batch)>) -> !exec.outcome<(!runtime.transfer<(!batch)>)>
      "exec.dispatch"(%29)[^bb14, ^bb11] : (!exec.outcome<(!runtime.transfer<(!batch)>)>) -> ()
    ^bb14(%30: !runtime.transfer<(!batch)>):  // pred: ^bb13
      "runtime.release_transfer"(%16) : (!runtime.transfer<(!batch)>) -> ()
      cf.br ^bb10(%30 : !runtime.transfer<(!batch)>)
    ^bb15(%31: !batch):  // pred: ^bb9
      %32 = "exec.returned"(%31) : (!batch) -> !exec.outcome<(!batch)>
      return %32 : !exec.outcome<(!batch)>
    }
    func.func private @control_0(%arg0: !runtime.scope, %arg1: ui64, %arg2: !batch, %arg3: !o, %arg4: !fs) -> !exec.outcome<(!batch)> attributes {no_inline, runtime.region} {
      %0 = "exec.apply"(%arg0, %arg4, %arg1) <{binding = @get, parameters = [], site = "coordinate"}> : (!runtime.scope, !fs, ui64) -> !exec.outcome<(!f)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb1(%1: !f):  // pred: ^bb0
      %2 = "exec.apply"(%arg0) <{binding = @point, parameters = [], site = "point"}> : (!runtime.scope) -> !exec.outcome<(!p)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(!p)>) -> ()
    ^bb2(%3: !exec.stop):  // 6 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!batch)>
      return %4 : !exec.outcome<(!batch)>
    ^bb3(%5: !p):  // pred: ^bb1
      %6 = "exec.apply"(%arg0, %5, %1) <{binding = @coordinate, parameters = [], site = "point1"}> : (!runtime.scope, !p, !f) -> !exec.outcome<(!p)>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<(!p)>) -> ()
    ^bb4(%7: !p):  // pred: ^bb3
      %8 = "exec.apply"(%arg0, %arg3, %7) <{binding = @open, parameters = [], site = "opening"}> : (!runtime.scope, !o, !p) -> !exec.outcome<(!f, !proof)>
      "exec.dispatch"(%8)[^bb5, ^bb2] : (!exec.outcome<(!f, !proof)>) -> ()
    ^bb5(%9: !f, %10: !proof):  // pred: ^bb4
      %11 = "exec.variant"(%arg0, %9, %10) <{alternative = "some", site = "record"}> : (!runtime.scope, !f, !proof) -> !exec.outcome<(!message)>
      "exec.dispatch"(%11)[^bb6, ^bb2] : (!exec.outcome<(!message)>) -> ()
    ^bb6(%12: !message):  // pred: ^bb5
      %13 = "exec.apply"(%arg0, %arg2, %12) <{binding = @append, parameters = [], site = "append"}> : (!runtime.scope, !batch, !message) -> !exec.outcome<(!batch)>
      "exec.dispatch"(%13)[^bb7, ^bb2] : (!exec.outcome<(!batch)>) -> ()
    ^bb7(%14: !batch):  // pred: ^bb6
      %15 = "exec.complete"(%arg0, %14) : (!runtime.scope, !batch) -> !exec.outcome<(!batch)>
      return %15 : !exec.outcome<(!batch)>
    }
    func.func @validate(%arg0: !runtime.scope, %arg1: !batch, %arg2: !vk, %arg3: !c, %arg4: !fs) -> !exec.outcome<(i1)> attributes {no_inline, runtime.origin = ["validate", []]} {
      %0 = "exec.apply"(%arg0, %arg4) <{binding = @vlength, parameters = [], site = "expected_count"}> : (!runtime.scope, !fs) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1: ui64):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %arg1) <{binding = @length, parameters = [], site = "actual_count"}> : (!runtime.scope, !batch) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%3: !exec.stop):  // 10 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb6, ^bb7, ^bb9, ^bb10, ^bb12, ^bb13
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(i1)>
      return %4 : !exec.outcome<(i1)>
    ^bb3(%5: ui64):  // pred: ^bb1
      %6 = "exec.apply"(%arg0, %1, %5) <{binding = @equal, parameters = [], site = "count_matches"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb4(%7: i1):  // pred: ^bb3
      %8 = "exec.test"(%arg0, %7) <{site = "counts"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%8)[^bb5, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb5(%9: i1):  // pred: ^bb4
      cf.cond_br %9, ^bb6, ^bb7
    ^bb6:  // pred: ^bb5
      %10 = "runtime.enter_scope"(%arg0, %arg1, %arg2, %arg3, %arg4, %1) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 5>, selection = "then", site = "counts"}> : (!runtime.scope, !batch, !vk, !c, !fs, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%10)[^bb9, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // pred: ^bb5
      %11 = "runtime.enter_scope"(%arg0, %arg1, %arg2, %arg3, %arg4, %1) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 5>, selection = "else", site = "counts"}> : (!runtime.scope, !batch, !vk, !c, !fs, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%11)[^bb12, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb8(%12: i1):  // 2 preds: ^bb11, ^bb14
      %13 = "exec.returned"(%12) : (i1) -> !exec.outcome<(i1)>
      return %13 : !exec.outcome<(i1)>
    ^bb9(%14: !runtime.scope):  // pred: ^bb6
      %15 = call @control_1(%14, %arg1, %arg2, %arg3, %arg4, %1) : (!runtime.scope, !batch, !vk, !c, !fs, ui64) -> !exec.outcome<(i1)>
      %16 = "runtime.exit_scope"(%14, %15) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%16)[^bb10, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb10(%17: !runtime.transfer<(i1)>):  // pred: ^bb9
      %18 = "runtime.accept_transfer"(%arg0, %17) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%18)[^bb11, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb11(%19: i1):  // pred: ^bb10
      cf.br ^bb8(%19 : i1)
    ^bb12(%20: !runtime.scope):  // pred: ^bb7
      %21 = call @control_5(%20, %arg1, %arg2, %arg3, %arg4, %1) : (!runtime.scope, !batch, !vk, !c, !fs, ui64) -> !exec.outcome<(i1)>
      %22 = "runtime.exit_scope"(%20, %21) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%22)[^bb13, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb13(%23: !runtime.transfer<(i1)>):  // pred: ^bb12
      %24 = "runtime.accept_transfer"(%arg0, %23) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%24)[^bb14, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb14(%25: i1):  // pred: ^bb13
      cf.br ^bb8(%25 : i1)
    }
    func.func private @control_1(%arg0: !runtime.scope, %arg1: !batch, %arg2: !vk, %arg3: !c, %arg4: !fs, %arg5: ui64) -> !exec.outcome<(i1)> attributes {no_inline, runtime.region} {
      %0 = "exec.boolean"(%arg0) <{site = "yes", value = true}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1: i1):  // pred: ^bb0
      %2 = "exec.apply"(%arg0) <{binding = @constant, parameters = ["0"], site = "zero"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%3: !exec.stop):  // 5 preds: ^bb0, ^bb1, ^bb3, ^bb7, ^bb9
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(i1)>
      return %4 : !exec.outcome<(i1)>
    ^bb3(%5: ui64):  // pred: ^bb1
      %6 = "exec.range"(%arg0, %5, %arg5) <{site = "check_openings"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<(i64, i64)>) -> ()
    ^bb4(%7: i64, %8: i64):  // pred: ^bb3
      %9 = "runtime.borrow_transfer"(%arg0, %1) : (!runtime.scope, i1) -> !runtime.transfer<(i1)>
      cf.br ^bb5(%7, %9 : i64, !runtime.transfer<(i1)>)
    ^bb5(%10: i64, %11: !runtime.transfer<(i1)>):  // 2 preds: ^bb4, ^bb8
      %12 = arith.cmpi ult, %10, %8 : i64
      cf.cond_br %12, ^bb6, ^bb7(%11 : !runtime.transfer<(i1)>)
    ^bb6:  // pred: ^bb5
      %13 = "runtime.iteration"(%arg0, %10) <{site = "check_openings"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
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
      %21 = "runtime.enter_scope"(%arg0, %10, %19, %20, %arg1, %arg2, %arg3, %arg4) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 6>, site = "check_openings"}> : (!runtime.scope, i64, ui64, i1, !batch, !vk, !c, !fs) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%21)[^bb11, ^bb9] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb11(%22: !runtime.scope):  // pred: ^bb10
      %23 = call @control_2(%22, %19, %20, %arg1, %arg2, %arg3, %arg4) : (!runtime.scope, ui64, i1, !batch, !vk, !c, !fs) -> !exec.outcome<(i1)>
      %24 = "runtime.exit_scope"(%22, %23) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%24)[^bb12, ^bb9] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb12(%25: !runtime.transfer<(i1)>):  // pred: ^bb11
      "runtime.release_transfer"(%11) : (!runtime.transfer<(i1)>) -> ()
      cf.br ^bb8(%25 : !runtime.transfer<(i1)>)
    ^bb13(%26: i1):  // pred: ^bb7
      %27 = "exec.complete"(%arg0, %26) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      return %27 : !exec.outcome<(i1)>
    }
    func.func private @control_2(%arg0: !runtime.scope, %arg1: ui64, %arg2: i1, %arg3: !batch, %arg4: !vk, %arg5: !c, %arg6: !fs) -> !exec.outcome<(i1)> attributes {no_inline, runtime.region} {
      %0 = "exec.apply"(%arg0, %arg3, %arg1) <{binding = @at, parameters = [], site = "item"}> : (!runtime.scope, !batch, ui64) -> !exec.outcome<(!message)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!message)>) -> ()
    ^bb1(%1: !message):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %arg6, %arg1) <{binding = @get, parameters = [], site = "coordinate"}> : (!runtime.scope, !fs, ui64) -> !exec.outcome<(!f)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb2(%3: !exec.stop):  // 12 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb10, ^bb12, ^bb13
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(i1)>
      return %4 : !exec.outcome<(i1)>
    ^bb3(%5: !f):  // pred: ^bb1
      %6 = "exec.apply"(%arg0) <{binding = @point, parameters = [], site = "point"}> : (!runtime.scope) -> !exec.outcome<(!p)>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<(!p)>) -> ()
    ^bb4(%7: !p):  // pred: ^bb3
      %8 = "exec.apply"(%arg0, %7, %5) <{binding = @coordinate, parameters = [], site = "point1"}> : (!runtime.scope, !p, !f) -> !exec.outcome<(!p)>
      "exec.dispatch"(%8)[^bb5, ^bb2] : (!exec.outcome<(!p)>) -> ()
    ^bb5(%9: !p):  // pred: ^bb4
      "exec.match"(%arg0, %1, %arg4, %arg5, %9)[^bb2, ^bb7, ^bb8] <{alternatives = ["none", "some"], site = "present"}> : (!runtime.scope, !message, !vk, !c, !p) -> ()
    ^bb6(%10: i1):  // 2 preds: ^bb11, ^bb14
      %11 = "exec.apply"(%arg0, %arg2, %10) <{binding = @and, parameters = [], site = "next"}> : (!runtime.scope, i1, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%11)[^bb15, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb7(%12: !vk, %13: !c, %14: !p):  // pred: ^bb5
      %15 = "runtime.enter_scope"(%arg0, %12, %13, %14) <{kind = "match", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "none", site = "present"}> : (!runtime.scope, !vk, !c, !p) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%15)[^bb9, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb8(%16: !f, %17: !proof, %18: !vk, %19: !c, %20: !p):  // pred: ^bb5
      %21 = "runtime.enter_scope"(%arg0, %16, %17, %18, %19, %20) <{kind = "match", operandSegmentSizes = array<i32: 1, 0, 5>, selection = "some", site = "present"}> : (!runtime.scope, !f, !proof, !vk, !c, !p) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%21)[^bb12, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb9(%22: !runtime.scope):  // pred: ^bb7
      %23 = call @control_3(%22, %12, %13, %14) : (!runtime.scope, !vk, !c, !p) -> !exec.outcome<(i1)>
      %24 = "runtime.exit_scope"(%22, %23) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%24)[^bb10, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb10(%25: !runtime.transfer<(i1)>):  // pred: ^bb9
      %26 = "runtime.accept_transfer"(%arg0, %25) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%26)[^bb11, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb11(%27: i1):  // pred: ^bb10
      cf.br ^bb6(%27 : i1)
    ^bb12(%28: !runtime.scope):  // pred: ^bb8
      %29 = call @control_4(%28, %16, %17, %18, %19, %20) : (!runtime.scope, !f, !proof, !vk, !c, !p) -> !exec.outcome<(i1)>
      %30 = "runtime.exit_scope"(%28, %29) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%30)[^bb13, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb13(%31: !runtime.transfer<(i1)>):  // pred: ^bb12
      %32 = "runtime.accept_transfer"(%arg0, %31) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%32)[^bb14, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb14(%33: i1):  // pred: ^bb13
      cf.br ^bb6(%33 : i1)
    ^bb15(%34: i1):  // pred: ^bb6
      %35 = "exec.complete"(%arg0, %34) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      return %35 : !exec.outcome<(i1)>
    }
    func.func private @control_3(%arg0: !runtime.scope, %arg1: !vk, %arg2: !c, %arg3: !p) -> !exec.outcome<(i1)> attributes {no_inline, runtime.region} {
      %0 = "exec.boolean"(%arg0) <{site = "absent", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1: i1):  // pred: ^bb0
      %2 = "exec.complete"(%arg0, %1) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      return %2 : !exec.outcome<(i1)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(i1)>
      return %4 : !exec.outcome<(i1)>
    }
    func.func private @control_4(%arg0: !runtime.scope, %arg1: !f, %arg2: !proof, %arg3: !vk, %arg4: !c, %arg5: !p) -> !exec.outcome<(i1)> attributes {no_inline, runtime.region} {
      %0 = "exec.apply"(%arg0, %arg3, %arg4, %arg5, %arg1, %arg2) <{binding = @check, parameters = [], site = "check"}> : (!runtime.scope, !vk, !c, !p, !f, !proof) -> !exec.outcome<(i1)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1: i1):  // pred: ^bb0
      %2 = "exec.complete"(%arg0, %1) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      return %2 : !exec.outcome<(i1)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(i1)>
      return %4 : !exec.outcome<(i1)>
    }
    func.func private @control_5(%arg0: !runtime.scope, %arg1: !batch, %arg2: !vk, %arg3: !c, %arg4: !fs, %arg5: ui64) -> !exec.outcome<(i1)> attributes {no_inline, runtime.region} {
      %0 = "exec.boolean"(%arg0) <{site = "count_mismatch", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1: i1):  // pred: ^bb0
      %2 = "exec.complete"(%arg0, %1) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      return %2 : !exec.outcome<(i1)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(i1)>
      return %4 : !exec.outcome<(i1)>
    }


 "protocol.func"() ({ ^entry(%table:!t,%pk:!pk,%vk:!vk,%root:!c,%points:!fs):
   %batch = "protocol.local_call"(%table,%pk,%points) {callee=@produce,role="P",site="produce"} : (!t,!pk,!fs)->!batch
   %received = protocol.exchange %batch {sender="P",receiver="V",site="batch"} : !batch
   %accepted = "protocol.local_call"(%received,%vk,%root,%points) {callee=@validate,role="V",site="validate"} : (!batch,!vk,!c,!fs)->i1
   "protocol.return"(%accepted) : (i1)->()
 }) {sym_name="main",function_type=(!t,!pk,!vk,!c,!fs)->i1,roles=["P","V"],input_roles=[["P"],["P"],["V"],["V"],["P","V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
