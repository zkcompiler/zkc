"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.empty", function_type = (!runtime.scope) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, implementation = "", sym_name = "zkl_binding_10"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "field.equal", function_type = (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>, implementation = "", sym_name = "zkl_binding_9"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.equal", function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(i1)>, implementation = "", sym_name = "zkl_binding_8"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.sum", function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>, implementation = "", sym_name = "zkl_binding_7"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.sub", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_6"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.mod", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_5"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.div", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_4"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.append", function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, implementation = "", sym_name = "zkl_binding_3"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.add", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_2"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.constant", function_type = (!runtime.scope) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_1"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.length", function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_0"}> : () -> ()
    "protocol.func"() <{contracts = [], function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, ui64, !algebra.field<"bls12-381.fr">, i1, i1, !algebra.field_vector<"bls12-381.fr">), input_roles = [["role00000000"], ["role00000000"], ["role00000000"]], origin = ["primitive_examples::Sequence", []], output_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"]], roles = ["role00000000"], sym_name = "s18h7072696d69746976655f6578616d706c65738h53657175656e6365"}> ({
    ^bb0(%arg4: !algebra.field_vector<"bls12-381.fr">, %arg5: !algebra.field<"bls12-381.fr">, %arg6: ui64):
      %27:8 = "protocol.local_call"(%arg4, %arg5, %arg6) <{callee = @s18h7072696d69746976655f6578616d706c657314h617070656e645f73756d6d617279, role = "role00000000", site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, ui64, !algebra.field<"bls12-381.fr">, i1, i1, !algebra.field_vector<"bls12-381.fr">)
      "protocol.return"(%27#0, %27#1, %27#2, %27#3, %27#4, %27#5, %27#6, %27#7) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, ui64, !algebra.field<"bls12-381.fr">, i1, i1, !algebra.field_vector<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64, ui64, !algebra.field<"bls12-381.fr">, i1, i1, !algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "s18h7072696d69746976655f6578616d706c657314h617070656e645f73756d6d617279", sym_visibility = "private"}> ({
    ^bb0(%arg0: !runtime.scope, %arg1: !algebra.field_vector<"bls12-381.fr">, %arg2: !algebra.field<"bls12-381.fr">, %arg3: ui64):
      %0 = "exec.apply"(%arg0, %arg1) <{binding = @zkl_binding_0, parameters = [], site = "s0"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1: ui64):  // pred: ^bb0
      %2 = "exec.apply"(%arg0) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s2"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%2)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%3: !exec.stop):  // 12 preds: ^bb0, ^bb1, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb10, ^bb11, ^bb12
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64, ui64, !algebra.field<"bls12-381.fr">, i1, i1, !algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%4) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64, ui64, !algebra.field<"bls12-381.fr">, i1, i1, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%5: ui64):  // pred: ^bb1
      %6 = "exec.apply"(%arg0, %1, %5) <{binding = @zkl_binding_2, parameters = [], site = "s3"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%6)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%7: ui64):  // pred: ^bb3
      %8 = "exec.apply"(%arg0, %arg1, %arg2) <{binding = @zkl_binding_3, parameters = [], site = "s5"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%8)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb5(%9: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb4
      %10 = "exec.apply"(%arg0, %7, %arg3) <{binding = @zkl_binding_4, parameters = [], site = "s7"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%10)[^bb6, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb6(%11: ui64):  // pred: ^bb5
      %12 = "exec.apply"(%arg0, %7, %arg3) <{binding = @zkl_binding_5, parameters = [], site = "s9"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%12)[^bb7, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb7(%13: ui64):  // pred: ^bb6
      %14 = "exec.apply"(%arg0) <{binding = @zkl_binding_1, parameters = [1 : ui64], site = "s11"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%14)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb8(%15: ui64):  // pred: ^bb7
      %16 = "exec.apply"(%arg0, %7, %15) <{binding = @zkl_binding_6, parameters = [], site = "s12"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%16)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb9(%17: ui64):  // pred: ^bb8
      %18 = "exec.apply"(%arg0, %9) <{binding = @zkl_binding_7, parameters = [], site = "s14"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>
      "exec.dispatch"(%18)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field<"bls12-381.fr">)>) -> ()
    ^bb10(%19: !algebra.field<"bls12-381.fr">):  // pred: ^bb9
      %20 = "exec.apply"(%arg0, %arg1, %9) <{binding = @zkl_binding_8, parameters = [], site = "s16"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(i1)>
      "exec.dispatch"(%20)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb11(%21: i1):  // pred: ^bb10
      %22 = "exec.apply"(%arg0, %19, %arg2) <{binding = @zkl_binding_9, parameters = [], site = "s18"}> : (!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(i1)>
      "exec.dispatch"(%22)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb12(%23: i1):  // pred: ^bb11
      %24 = "exec.apply"(%arg0) <{binding = @zkl_binding_10, parameters = [], site = "s20"}> : (!runtime.scope) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%24)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb13(%25: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb12
      %26 = "exec.returned"(%9, %11, %13, %17, %19, %21, %23, %25) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, ui64, !algebra.field<"bls12-381.fr">, i1, i1, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64, ui64, !algebra.field<"bls12-381.fr">, i1, i1, !algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%26) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64, ui64, !algebra.field<"bls12-381.fr">, i1, i1, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s18h7072696d69746976655f6578616d706c657314h617070656e645f73756d6d617279", []]} : () -> ()
  }) : () -> ()
}) : () -> ()

