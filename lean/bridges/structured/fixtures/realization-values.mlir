"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "runtime.binding"() <{arguments = [], contract = "index.mul", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_6"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.less", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>, implementation = "", sym_name = "zkl_binding_5"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.div", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_4"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.equal", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>, implementation = "", sym_name = "zkl_binding_3"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.mod", function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_2"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.length", function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_1"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.constant", function_type = (!runtime.scope) -> !exec.outcome<(ui64)>, implementation = "", sym_name = "zkl_binding_0"}> : () -> ()
    "protocol.func"() <{contracts = [], function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">, input_roles = [["role00000000"], ["role00000000"], ["role00000000"]], origin = ["map_examples::RealizeValues", []], output_roles = [["role00000000"]], roles = ["role00000000"], sym_name = "s12h6d61705f6578616d706c657313h5265616c697a6556616c756573"}> ({
    ^bb0(%arg45: !algebra.field_vector<"bls12-381.fr">, %arg46: ui64, %arg47: ui64):
      %193:3 = "protocol.local_call"(%arg45, %arg46, %arg47) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a, role = "role00000000", site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      %194 = "protocol.local_call"(%193#0, %193#1, %193#2) <{callee = @s12h6d61705f6578616d706c657314h7265616c697a655f76616c756573, role = "role00000000", site = "s2"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">
      "protocol.return"(%194) : (!algebra.field_vector<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", sym_visibility = "private"}> ({
    ^bb0(%arg41: !runtime.scope, %arg42: !algebra.field_vector<"bls12-381.fr">, %arg43: ui64, %arg44: ui64):
      %174 = "func.call"(%arg41, %arg42, %arg43, %arg44) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655}> {runtime.site = "s0"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%174)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%175: i1):  // pred: ^bb0
      %176 = "exec.test"(%arg41, %175) <{site = "s1"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%176)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%177: !exec.stop):  // 8 preds: ^bb0, ^bb1, ^bb4, ^bb5, ^bb7, ^bb8, ^bb10, ^bb11
      %178 = "exec.failed"(%177) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%178) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb3(%179: i1):  // pred: ^bb1
      "cf.cond_br"(%179)[^bb4, ^bb5] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb4:  // pred: ^bb3
      %180 = "runtime.enter_scope"(%arg41) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%180)[^bb7, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb5:  // pred: ^bb3
      %181 = "runtime.enter_scope"(%arg41) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%181)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // 2 preds: ^bb9, ^bb12
      %182 = "exec.returned"(%arg42, %arg43, %arg44) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%182) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb7(%183: !runtime.scope):  // pred: ^bb4
      %184 = "func.call"(%183) <{callee = @zkl_control_0}> : (!runtime.scope) -> !exec.outcome<>
      %185 = "runtime.exit_scope"(%183, %184) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%185)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb8(%186: !runtime.transfer<>):  // pred: ^bb7
      %187 = "runtime.accept_transfer"(%arg41, %186) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%187)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb9:  // pred: ^bb8
      "cf.br"()[^bb6] : () -> ()
    ^bb10(%188: !runtime.scope):  // pred: ^bb5
      %189 = "func.call"(%188) <{callee = @zkl_control_1}> : (!runtime.scope) -> !exec.outcome<>
      %190 = "runtime.exit_scope"(%188, %189) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%190)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb11(%191: !runtime.transfer<>):  // pred: ^bb10
      %192 = "runtime.accept_transfer"(%arg41, %191) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%192)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb12:  // pred: ^bb11
      "cf.br"()[^bb6] : () -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561725h7461626c65", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_0", sym_visibility = "private"}> ({
    ^bb0(%arg40: !runtime.scope):
      %173 = "exec.complete"(%arg40) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%173) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_1", sym_visibility = "private"}> ({
    ^bb0(%arg39: !runtime.scope):
      %170 = "exec.reject"(%arg39) <{reason = "reject", site = "s1_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%170)[^bb1] : (!exec.stop) -> ()
    ^bb1(%171: !exec.stop):  // pred: ^bb0
      %172 = "exec.failed"(%171) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%172) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", sym_visibility = "private"}> ({
    ^bb0(%arg35: !runtime.scope, %arg36: !algebra.field_vector<"bls12-381.fr">, %arg37: ui64, %arg38: ui64):
      %112 = "exec.apply"(%arg35) <{binding = @zkl_binding_0, parameters = [0 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%112)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%113: ui64):  // pred: ^bb0
      %114 = "func.call"(%arg35, %113, %arg38) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s1"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%114)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%115: !exec.stop):  // 23 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12, ^bb15, ^bb16, ^bb17, ^bb18, ^bb19, ^bb21, ^bb22, ^bb25, ^bb26, ^bb28, ^bb29, ^bb31, ^bb32
      %116 = "exec.failed"(%115) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%116) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%117: i1):  // pred: ^bb1
      %118 = "exec.test"(%arg35, %117) <{site = "s3"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%118)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb4(%119: i1):  // pred: ^bb3
      "cf.cond_br"(%119)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %120 = "runtime.enter_scope"(%arg35, %arg37) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "then", site = "s3"}> : (!runtime.scope, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%120)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %121 = "runtime.enter_scope"(%arg35, %arg37) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "else", site = "s3"}> : (!runtime.scope, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%121)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7(%122: i1):  // 2 preds: ^bb10, ^bb13
      %123 = "exec.test"(%arg35, %122) <{site = "s11"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%123)[^bb14, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb8(%124: !runtime.scope):  // pred: ^bb5
      %125 = "func.call"(%124, %arg37) <{callee = @zkl_control_2}> : (!runtime.scope, ui64) -> !exec.outcome<(i1)>
      %126 = "runtime.exit_scope"(%124, %125) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%126)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb9(%127: !runtime.transfer<(i1)>):  // pred: ^bb8
      %128 = "runtime.accept_transfer"(%arg35, %127) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%128)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb10(%129: i1):  // pred: ^bb9
      "cf.br"(%129)[^bb7] : (i1) -> ()
    ^bb11(%130: !runtime.scope):  // pred: ^bb6
      %131 = "func.call"(%130, %arg37) <{callee = @zkl_control_3}> : (!runtime.scope, ui64) -> !exec.outcome<(i1)>
      %132 = "runtime.exit_scope"(%130, %131) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%132)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb12(%133: !runtime.transfer<(i1)>):  // pred: ^bb11
      %134 = "runtime.accept_transfer"(%arg35, %133) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%134)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb13(%135: i1):  // pred: ^bb12
      "cf.br"(%135)[^bb7] : (i1) -> ()
    ^bb14(%136: i1):  // pred: ^bb7
      "cf.cond_br"(%136)[^bb15, ^bb16] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb15:  // pred: ^bb14
      %137 = "runtime.enter_scope"(%arg35, %arg36, %arg38) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "then", site = "s11"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%137)[^bb18, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb16:  // pred: ^bb14
      %138 = "runtime.enter_scope"(%arg35, %arg36, %arg38) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "else", site = "s11"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%138)[^bb21, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb17(%139: i1):  // 2 preds: ^bb20, ^bb23
      %140 = "exec.test"(%arg35, %139) <{site = "s22"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%140)[^bb24, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb18(%141: !runtime.scope):  // pred: ^bb15
      %142 = "func.call"(%141, %arg36, %arg38) <{callee = @zkl_control_4}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>
      %143 = "runtime.exit_scope"(%141, %142) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%143)[^bb19, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb19(%144: !runtime.transfer<(i1)>):  // pred: ^bb18
      %145 = "runtime.accept_transfer"(%arg35, %144) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%145)[^bb20, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb20(%146: i1):  // pred: ^bb19
      "cf.br"(%146)[^bb17] : (i1) -> ()
    ^bb21(%147: !runtime.scope):  // pred: ^bb16
      %148 = "func.call"(%147, %arg36, %arg38) <{callee = @zkl_control_5}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>
      %149 = "runtime.exit_scope"(%147, %148) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%149)[^bb22, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb22(%150: !runtime.transfer<(i1)>):  // pred: ^bb21
      %151 = "runtime.accept_transfer"(%arg35, %150) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%151)[^bb23, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb23(%152: i1):  // pred: ^bb22
      "cf.br"(%152)[^bb17] : (i1) -> ()
    ^bb24(%153: i1):  // pred: ^bb17
      "cf.cond_br"(%153)[^bb25, ^bb26] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb25:  // pred: ^bb24
      %154 = "runtime.enter_scope"(%arg35, %arg36, %arg37, %arg38) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "then", site = "s22"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%154)[^bb28, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb26:  // pred: ^bb24
      %155 = "runtime.enter_scope"(%arg35, %arg36, %arg37, %arg38) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "else", site = "s22"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%155)[^bb31, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb27(%156: i1):  // 2 preds: ^bb30, ^bb33
      %157 = "exec.returned"(%156) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%157) : (!exec.outcome<(i1)>) -> ()
    ^bb28(%158: !runtime.scope):  // pred: ^bb25
      %159 = "func.call"(%158, %arg36, %arg37, %arg38) <{callee = @zkl_control_6}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      %160 = "runtime.exit_scope"(%158, %159) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%160)[^bb29, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb29(%161: !runtime.transfer<(i1)>):  // pred: ^bb28
      %162 = "runtime.accept_transfer"(%arg35, %161) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%162)[^bb30, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb30(%163: i1):  // pred: ^bb29
      "cf.br"(%163)[^bb27] : (i1) -> ()
    ^bb31(%164: !runtime.scope):  // pred: ^bb26
      %165 = "func.call"(%164, %arg36, %arg37, %arg38) <{callee = @zkl_control_7}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      %166 = "runtime.exit_scope"(%164, %165) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%166)[^bb32, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb32(%167: !runtime.transfer<(i1)>):  // pred: ^bb31
      %168 = "runtime.accept_transfer"(%arg35, %167) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%168)[^bb33, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb33(%169: i1):  // pred: ^bb32
      "cf.br"(%169)[^bb27] : (i1) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_2", sym_visibility = "private"}> ({
    ^bb0(%arg33: !runtime.scope, %arg34: ui64):
      %105 = "exec.apply"(%arg33) <{binding = @zkl_binding_0, parameters = [64 : ui64], site = "s4"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%105)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%106: ui64):  // pred: ^bb0
      %107 = "func.call"(%arg33, %arg34, %106) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s5"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%107)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%108: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %109 = "exec.failed"(%108) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%109) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%110: i1):  // pred: ^bb1
      %111 = "exec.complete"(%arg33, %110) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%111) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_3", sym_visibility = "private"}> ({
    ^bb0(%arg31: !runtime.scope, %arg32: ui64):
      %100 = "exec.boolean"(%arg31) <{site = "s7", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%100)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%101: i1):  // pred: ^bb0
      %102 = "exec.complete"(%arg31, %101) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%102) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%103: !exec.stop):  // pred: ^bb0
      %104 = "exec.failed"(%103) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%104) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_4", sym_visibility = "private"}> ({
    ^bb0(%arg28: !runtime.scope, %arg29: !algebra.field_vector<"bls12-381.fr">, %arg30: ui64):
      %89 = "exec.apply"(%arg28, %arg29) <{binding = @zkl_binding_1, parameters = [], site = "s12"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%89)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%90: ui64):  // pred: ^bb0
      %91 = "exec.apply"(%arg28, %90, %arg30) <{binding = @zkl_binding_2, parameters = [], site = "s13"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%91)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%92: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %93 = "exec.failed"(%92) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%93) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%94: ui64):  // pred: ^bb1
      %95 = "exec.apply"(%arg28) <{binding = @zkl_binding_0, parameters = [0 : ui64], site = "s14"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%95)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%96: ui64):  // pred: ^bb3
      %97 = "exec.apply"(%arg28, %94, %96) <{binding = @zkl_binding_3, parameters = [], site = "s15"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%97)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb5(%98: i1):  // pred: ^bb4
      %99 = "exec.complete"(%arg28, %98) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%99) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_5", sym_visibility = "private"}> ({
    ^bb0(%arg25: !runtime.scope, %arg26: !algebra.field_vector<"bls12-381.fr">, %arg27: ui64):
      %84 = "exec.boolean"(%arg25) <{site = "s17", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%84)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%85: i1):  // pred: ^bb0
      %86 = "exec.complete"(%arg25, %85) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%86) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%87: !exec.stop):  // pred: ^bb0
      %88 = "exec.failed"(%87) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%88) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_6", sym_visibility = "private"}> ({
    ^bb0(%arg21: !runtime.scope, %arg22: !algebra.field_vector<"bls12-381.fr">, %arg23: ui64, %arg24: ui64):
      %73 = "exec.apply"(%arg21, %arg22) <{binding = @zkl_binding_1, parameters = [], site = "s23"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%73)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%74: ui64):  // pred: ^bb0
      %75 = "exec.apply"(%arg21, %74, %arg24) <{binding = @zkl_binding_4, parameters = [], site = "s24"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%75)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%76: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %77 = "exec.failed"(%76) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%77) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%78: ui64):  // pred: ^bb1
      %79 = "func.call"(%arg21, %arg23) <{callee = @s3h7a6b6311h6d756c74696c696e6561724h726f7773}> {runtime.site = "s25"} : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%79)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%80: ui64):  // pred: ^bb3
      %81 = "exec.apply"(%arg21, %78, %80) <{binding = @zkl_binding_3, parameters = [], site = "s26"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%81)[^bb5, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb5(%82: i1):  // pred: ^bb4
      %83 = "exec.complete"(%arg21, %82) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%83) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_7", sym_visibility = "private"}> ({
    ^bb0(%arg17: !runtime.scope, %arg18: !algebra.field_vector<"bls12-381.fr">, %arg19: ui64, %arg20: ui64):
      %68 = "exec.boolean"(%arg17) <{site = "s28", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%68)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%69: i1):  // pred: ^bb0
      %70 = "exec.complete"(%arg17, %69) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%70) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%71: !exec.stop):  // pred: ^bb0
      %72 = "exec.failed"(%71) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%72) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "s3h7a6b637h696e64696365734h6c657373", sym_visibility = "private"}> ({
    ^bb0(%arg14: !runtime.scope, %arg15: ui64, %arg16: ui64):
      %63 = "exec.apply"(%arg14, %arg15, %arg16) <{binding = @zkl_binding_5, parameters = [], site = "s0"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%63)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb1(%64: i1):  // pred: ^bb0
      %65 = "exec.returned"(%64) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%65) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%66: !exec.stop):  // pred: ^bb0
      %67 = "exec.failed"(%66) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%67) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.origin = ["s3h7a6b637h696e64696365734h6c657373", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "s3h7a6b6311h6d756c74696c696e6561724h726f7773", sym_visibility = "private"}> ({
    ^bb0(%arg12: !runtime.scope, %arg13: ui64):
      %16 = "exec.apply"(%arg12) <{binding = @zkl_binding_0, parameters = [64 : ui64], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%16)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%17: ui64):  // pred: ^bb0
      %18 = "func.call"(%arg12, %arg13, %17) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s1"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%18)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb2(%19: !exec.stop):  // 14 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12, ^bb14, ^bb15, ^bb19, ^bb21
      %20 = "exec.failed"(%19) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%20) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%21: i1):  // pred: ^bb1
      %22 = "exec.test"(%arg12, %21) <{site = "s2"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%22)[^bb4, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i1)>) -> ()
    ^bb4(%23: i1):  // pred: ^bb3
      "cf.cond_br"(%23)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %24 = "runtime.enter_scope"(%arg12) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s2"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%24)[^bb8, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %25 = "runtime.enter_scope"(%arg12) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s2"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%25)[^bb11, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // 2 preds: ^bb10, ^bb13
      %26 = "exec.apply"(%arg12) <{binding = @zkl_binding_0, parameters = [1 : ui64], site = "s3"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%26)[^bb14, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb8(%27: !runtime.scope):  // pred: ^bb5
      %28 = "func.call"(%27) <{callee = @zkl_control_8}> : (!runtime.scope) -> !exec.outcome<>
      %29 = "runtime.exit_scope"(%27, %28) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%29)[^bb9, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb9(%30: !runtime.transfer<>):  // pred: ^bb8
      %31 = "runtime.accept_transfer"(%arg12, %30) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%31)[^bb10, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb10:  // pred: ^bb9
      "cf.br"()[^bb7] : () -> ()
    ^bb11(%32: !runtime.scope):  // pred: ^bb6
      %33 = "func.call"(%32) <{callee = @zkl_control_9}> : (!runtime.scope) -> !exec.outcome<>
      %34 = "runtime.exit_scope"(%32, %33) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%34)[^bb12, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb12(%35: !runtime.transfer<>):  // pred: ^bb11
      %36 = "runtime.accept_transfer"(%arg12, %35) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%36)[^bb13, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<>) -> ()
    ^bb13:  // pred: ^bb12
      "cf.br"()[^bb7] : () -> ()
    ^bb14(%37: ui64):  // pred: ^bb7
      %38 = "exec.apply"(%arg12) <{binding = @zkl_binding_0, parameters = [0 : ui64], site = "s5"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%38)[^bb15, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb15(%39: ui64):  // pred: ^bb14
      %40 = "exec.range"(%arg12, %39, %arg13) <{site = "s6"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%40)[^bb16, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(i64, i64)>) -> ()
    ^bb16(%41: i64, %42: i64):  // pred: ^bb15
      %43 = "runtime.borrow_transfer"(%arg12, %37) : (!runtime.scope, ui64) -> !runtime.transfer<(ui64)>
      "cf.br"(%41, %43)[^bb17] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb17(%44: i64, %45: !runtime.transfer<(ui64)>):  // 2 preds: ^bb16, ^bb20
      %46 = "arith.cmpi"(%44, %42) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%46, %45)[^bb18, ^bb19] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(ui64)>) -> ()
    ^bb18:  // pred: ^bb17
      %47 = "runtime.iteration"(%arg12, %44) <{site = "s6"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%47)[^bb22, ^bb21] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb19(%48: !runtime.transfer<(ui64)>):  // pred: ^bb17
      %49 = "runtime.accept_transfer"(%arg12, %48) : (!runtime.scope, !runtime.transfer<(ui64)>) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%49)[^bb25, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb20(%50: !runtime.transfer<(ui64)>):  // pred: ^bb24
      %51 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %52 = "arith.addi"(%44, %51) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%52, %50)[^bb17] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb21(%53: !exec.stop):  // 3 preds: ^bb18, ^bb22, ^bb23
      "runtime.release_transfer"(%45) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%53)[^bb2] : (!exec.stop) -> ()
    ^bb22(%54: ui64):  // pred: ^bb18
      %55 = "runtime.transfer_values"(%45) : (!runtime.transfer<(ui64)>) -> ui64
      %56 = "runtime.enter_scope"(%arg12, %44, %54, %55) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 2>, site = "s6"}> : (!runtime.scope, i64, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%56)[^bb23, ^bb21] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb23(%57: !runtime.scope):  // pred: ^bb22
      %58 = "func.call"(%57, %54, %55) <{callee = @zkl_control_10}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      %59 = "runtime.exit_scope"(%57, %58) : (!runtime.scope, !exec.outcome<(ui64)>) -> !exec.outcome<(!runtime.transfer<(ui64)>)>
      "exec.dispatch"(%59)[^bb24, ^bb21] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!runtime.transfer<(ui64)>)>) -> ()
    ^bb24(%60: !runtime.transfer<(ui64)>):  // pred: ^bb23
      "runtime.release_transfer"(%45) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%60)[^bb20] : (!runtime.transfer<(ui64)>) -> ()
    ^bb25(%61: ui64):  // pred: ^bb19
      %62 = "exec.returned"(%61) : (ui64) -> !exec.outcome<(ui64)>
      "func.return"(%62) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561724h726f7773", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_8", sym_visibility = "private"}> ({
    ^bb0(%arg11: !runtime.scope):
      %15 = "exec.complete"(%arg11) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%15) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_9", sym_visibility = "private"}> ({
    ^bb0(%arg10: !runtime.scope):
      %12 = "exec.reject"(%arg10) <{reason = "reject", site = "s2_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%12)[^bb1] : (!exec.stop) -> ()
    ^bb1(%13: !exec.stop):  // pred: ^bb0
      %14 = "exec.failed"(%13) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%14) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "zkl_control_10", sym_visibility = "private"}> ({
    ^bb0(%arg7: !runtime.scope, %arg8: ui64, %arg9: ui64):
      %5 = "exec.apply"(%arg7) <{binding = @zkl_binding_0, parameters = [2 : ui64], site = "s7"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%5)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%6: ui64):  // pred: ^bb0
      %7 = "exec.apply"(%arg7, %arg9, %6) <{binding = @zkl_binding_6, parameters = [], site = "s8"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%7)[^bb3, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%8: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %9 = "exec.failed"(%8) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%9) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%10: ui64):  // pred: ^bb1
      %11 = "exec.complete"(%arg7, %10) : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "func.return"(%11) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "s12h6d61705f6578616d706c657314h7265616c697a655f76616c756573", sym_visibility = "private"}> ({
    ^bb0(%arg3: !runtime.scope, %arg4: !algebra.field_vector<"bls12-381.fr">, %arg5: ui64, %arg6: ui64):
      %0 = "exec.compute"(%arg3, %arg4, %arg5, %arg6) <{callee = @zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33, site = "s0"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%0)[^bb1, ^bb2] <{successor_operand_segments = array<i32: 0, 0>}> : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%1: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%2) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%4) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s12h6d61705f6578616d706c657314h7265616c697a655f76616c756573", []]} : () -> ()
    "func.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !algebra.field_vector<"bls12-381.fr">, sym_name = "zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", sym_visibility = "private"}> ({
    ^bb0(%arg0: !algebra.field_vector<"bls12-381.fr">, %arg1: ui64, %arg2: ui64):
      "func.return"(%arg0) : (!algebra.field_vector<"bls12-381.fr">) -> ()
    }) : () -> ()
  }) : () -> ()
}) : () -> ()

