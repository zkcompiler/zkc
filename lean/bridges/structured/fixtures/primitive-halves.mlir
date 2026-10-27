"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.split", implementation = "", sym_name = "zkl_binding_7"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.mul", implementation = "", sym_name = "zkl_binding_6"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.less", implementation = "", sym_name = "zkl_binding_5"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.div", implementation = "", sym_name = "zkl_binding_4"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.equal", implementation = "", sym_name = "zkl_binding_3"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.mod", implementation = "", sym_name = "zkl_binding_2"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.length", implementation = "", sym_name = "zkl_binding_1"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.constant", implementation = "", sym_name = "zkl_binding_0"}> : () -> ()
    "protocol.func"() <{contracts = [], function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">), input_roles = [["role00000000"], ["role00000000"], ["role00000000"]], origin = ["primitive_examples::TableHalves", []], output_roles = [["role00000000"], ["role00000000"]], roles = ["role00000000"], sym_name = "s18h7072696d69746976655f6578616d706c657311h5461626c6548616c766573"}> ({
    ^bb0(%arg44: !algebra.field_vector<"bls12-381.fr">, %arg45: ui64, %arg46: ui64):
      %216:3 = "protocol.local_call"(%arg44, %arg45, %arg46) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a, role = "role00000000", site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      %217:2 = "protocol.local_call"(%216#0, %216#1, %216#2) <{callee = @zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087, role = "role00000000", site = "s2"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)
      "protocol.return"(%217#0, %217#1) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>, no_inline, sym_name = "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", sym_visibility = "private"}> ({
    ^bb0(%arg40: !runtime.scope, %arg41: !algebra.field_vector<"bls12-381.fr">, %arg42: ui64, %arg43: ui64):
      %197 = "func.call"(%arg40, %arg41, %arg42, %arg43) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655}> {runtime.site = "s0"} : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%197)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%198: i1):  // pred: ^bb0
      %199 = "exec.test"(%arg40, %198) <{site = "s1"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%199)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%200: !exec.stop):  // 8 preds: ^bb0, ^bb1, ^bb4, ^bb5, ^bb7, ^bb8, ^bb10, ^bb11
      %201 = "exec.failed"(%200) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%201) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb3(%202: i1):  // pred: ^bb1
      "cf.cond_br"(%202)[^bb4, ^bb5] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb4:  // pred: ^bb3
      %203 = "runtime.enter_scope"(%arg40) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%203)[^bb7, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb5:  // pred: ^bb3
      %204 = "runtime.enter_scope"(%arg40) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s1"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%204)[^bb10, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // 2 preds: ^bb9, ^bb12
      %205 = "exec.returned"(%arg41, %arg42, %arg43) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>
      "func.return"(%205) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, ui64, ui64)>) -> ()
    ^bb7(%206: !runtime.scope):  // pred: ^bb4
      %207 = "func.call"(%206) <{callee = @zkl_control_0}> : (!runtime.scope) -> !exec.outcome<>
      %208 = "runtime.exit_scope"(%206, %207) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%208)[^bb8, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb8(%209: !runtime.transfer<>):  // pred: ^bb7
      %210 = "runtime.accept_transfer"(%arg40, %209) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%210)[^bb9, ^bb2] : (!exec.outcome<>) -> ()
    ^bb9:  // pred: ^bb8
      "cf.br"()[^bb6] : () -> ()
    ^bb10(%211: !runtime.scope):  // pred: ^bb5
      %212 = "func.call"(%211) <{callee = @zkl_control_1}> : (!runtime.scope) -> !exec.outcome<>
      %213 = "runtime.exit_scope"(%211, %212) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%213)[^bb11, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb11(%214: !runtime.transfer<>):  // pred: ^bb10
      %215 = "runtime.accept_transfer"(%arg40, %214) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%215)[^bb12, ^bb2] : (!exec.outcome<>) -> ()
    ^bb12:  // pred: ^bb11
      "cf.br"()[^bb6] : () -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561725h7461626c65", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_0", sym_visibility = "private"}> ({
    ^bb0(%arg39: !runtime.scope):
      %196 = "exec.complete"(%arg39) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%196) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_1", sym_visibility = "private"}> ({
    ^bb0(%arg38: !runtime.scope):
      %193 = "exec.reject"(%arg38) <{reason = "reject", site = "s1_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%193)[^bb1] : (!exec.stop) -> ()
    ^bb1(%194: !exec.stop):  // pred: ^bb0
      %195 = "exec.failed"(%194) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%195) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", sym_visibility = "private"}> ({
    ^bb0(%arg34: !runtime.scope, %arg35: !algebra.field_vector<"bls12-381.fr">, %arg36: ui64, %arg37: ui64):
      %135 = "exec.apply"(%arg34) <{binding = @zkl_binding_0, parameters = ["0"], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%135)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%136: ui64):  // pred: ^bb0
      %137 = "func.call"(%arg34, %136, %arg37) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s1"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%137)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%138: !exec.stop):  // 23 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12, ^bb15, ^bb16, ^bb17, ^bb18, ^bb19, ^bb21, ^bb22, ^bb25, ^bb26, ^bb28, ^bb29, ^bb31, ^bb32
      %139 = "exec.failed"(%138) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%139) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%140: i1):  // pred: ^bb1
      %141 = "exec.test"(%arg34, %140) <{site = "s3"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%141)[^bb4, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb4(%142: i1):  // pred: ^bb3
      "cf.cond_br"(%142)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %143 = "runtime.enter_scope"(%arg34, %arg36) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "then", site = "s3"}> : (!runtime.scope, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%143)[^bb8, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %144 = "runtime.enter_scope"(%arg34, %arg36) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "else", site = "s3"}> : (!runtime.scope, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%144)[^bb11, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7(%145: i1):  // 2 preds: ^bb10, ^bb13
      %146 = "exec.test"(%arg34, %145) <{site = "s11"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%146)[^bb14, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb8(%147: !runtime.scope):  // pred: ^bb5
      %148 = "func.call"(%147, %arg36) <{callee = @zkl_control_2}> : (!runtime.scope, ui64) -> !exec.outcome<(i1)>
      %149 = "runtime.exit_scope"(%147, %148) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%149)[^bb9, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb9(%150: !runtime.transfer<(i1)>):  // pred: ^bb8
      %151 = "runtime.accept_transfer"(%arg34, %150) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%151)[^bb10, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb10(%152: i1):  // pred: ^bb9
      "cf.br"(%152)[^bb7] : (i1) -> ()
    ^bb11(%153: !runtime.scope):  // pred: ^bb6
      %154 = "func.call"(%153, %arg36) <{callee = @zkl_control_3}> : (!runtime.scope, ui64) -> !exec.outcome<(i1)>
      %155 = "runtime.exit_scope"(%153, %154) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%155)[^bb12, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb12(%156: !runtime.transfer<(i1)>):  // pred: ^bb11
      %157 = "runtime.accept_transfer"(%arg34, %156) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%157)[^bb13, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb13(%158: i1):  // pred: ^bb12
      "cf.br"(%158)[^bb7] : (i1) -> ()
    ^bb14(%159: i1):  // pred: ^bb7
      "cf.cond_br"(%159)[^bb15, ^bb16] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb15:  // pred: ^bb14
      %160 = "runtime.enter_scope"(%arg34, %arg35, %arg37) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "then", site = "s11"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%160)[^bb18, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb16:  // pred: ^bb14
      %161 = "runtime.enter_scope"(%arg34, %arg35, %arg37) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "else", site = "s11"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%161)[^bb21, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb17(%162: i1):  // 2 preds: ^bb20, ^bb23
      %163 = "exec.test"(%arg34, %162) <{site = "s22"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%163)[^bb24, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb18(%164: !runtime.scope):  // pred: ^bb15
      %165 = "func.call"(%164, %arg35, %arg37) <{callee = @zkl_control_4}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>
      %166 = "runtime.exit_scope"(%164, %165) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%166)[^bb19, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb19(%167: !runtime.transfer<(i1)>):  // pred: ^bb18
      %168 = "runtime.accept_transfer"(%arg34, %167) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%168)[^bb20, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb20(%169: i1):  // pred: ^bb19
      "cf.br"(%169)[^bb17] : (i1) -> ()
    ^bb21(%170: !runtime.scope):  // pred: ^bb16
      %171 = "func.call"(%170, %arg35, %arg37) <{callee = @zkl_control_5}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>
      %172 = "runtime.exit_scope"(%170, %171) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%172)[^bb22, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb22(%173: !runtime.transfer<(i1)>):  // pred: ^bb21
      %174 = "runtime.accept_transfer"(%arg34, %173) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%174)[^bb23, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb23(%175: i1):  // pred: ^bb22
      "cf.br"(%175)[^bb17] : (i1) -> ()
    ^bb24(%176: i1):  // pred: ^bb17
      "cf.cond_br"(%176)[^bb25, ^bb26] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb25:  // pred: ^bb24
      %177 = "runtime.enter_scope"(%arg34, %arg35, %arg36, %arg37) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "then", site = "s22"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%177)[^bb28, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb26:  // pred: ^bb24
      %178 = "runtime.enter_scope"(%arg34, %arg35, %arg36, %arg37) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "else", site = "s22"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%178)[^bb31, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb27(%179: i1):  // 2 preds: ^bb30, ^bb33
      %180 = "exec.returned"(%179) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%180) : (!exec.outcome<(i1)>) -> ()
    ^bb28(%181: !runtime.scope):  // pred: ^bb25
      %182 = "func.call"(%181, %arg35, %arg36, %arg37) <{callee = @zkl_control_6}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      %183 = "runtime.exit_scope"(%181, %182) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%183)[^bb29, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb29(%184: !runtime.transfer<(i1)>):  // pred: ^bb28
      %185 = "runtime.accept_transfer"(%arg34, %184) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%185)[^bb30, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb30(%186: i1):  // pred: ^bb29
      "cf.br"(%186)[^bb27] : (i1) -> ()
    ^bb31(%187: !runtime.scope):  // pred: ^bb26
      %188 = "func.call"(%187, %arg35, %arg36, %arg37) <{callee = @zkl_control_7}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      %189 = "runtime.exit_scope"(%187, %188) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%189)[^bb32, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb32(%190: !runtime.transfer<(i1)>):  // pred: ^bb31
      %191 = "runtime.accept_transfer"(%arg34, %190) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%191)[^bb33, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb33(%192: i1):  // pred: ^bb32
      "cf.br"(%192)[^bb27] : (i1) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_2", sym_visibility = "private"}> ({
    ^bb0(%arg32: !runtime.scope, %arg33: ui64):
      %128 = "exec.apply"(%arg32) <{binding = @zkl_binding_0, parameters = ["64"], site = "s4"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%128)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%129: ui64):  // pred: ^bb0
      %130 = "func.call"(%arg32, %arg33, %129) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s5"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%130)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%131: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %132 = "exec.failed"(%131) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%132) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%133: i1):  // pred: ^bb1
      %134 = "exec.complete"(%arg32, %133) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%134) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_3", sym_visibility = "private"}> ({
    ^bb0(%arg30: !runtime.scope, %arg31: ui64):
      %123 = "exec.boolean"(%arg30) <{site = "s7", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%123)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%124: i1):  // pred: ^bb0
      %125 = "exec.complete"(%arg30, %124) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%125) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%126: !exec.stop):  // pred: ^bb0
      %127 = "exec.failed"(%126) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%127) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_4", sym_visibility = "private"}> ({
    ^bb0(%arg27: !runtime.scope, %arg28: !algebra.field_vector<"bls12-381.fr">, %arg29: ui64):
      %112 = "exec.apply"(%arg27, %arg28) <{binding = @zkl_binding_1, parameters = [], site = "s12"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%112)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%113: ui64):  // pred: ^bb0
      %114 = "exec.apply"(%arg27, %113, %arg29) <{binding = @zkl_binding_2, parameters = [], site = "s13"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%114)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%115: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %116 = "exec.failed"(%115) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%116) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%117: ui64):  // pred: ^bb1
      %118 = "exec.apply"(%arg27) <{binding = @zkl_binding_0, parameters = ["0"], site = "s14"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%118)[^bb4, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%119: ui64):  // pred: ^bb3
      %120 = "exec.apply"(%arg27, %117, %119) <{binding = @zkl_binding_3, parameters = [], site = "s15"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%120)[^bb5, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb5(%121: i1):  // pred: ^bb4
      %122 = "exec.complete"(%arg27, %121) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%122) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_5", sym_visibility = "private"}> ({
    ^bb0(%arg24: !runtime.scope, %arg25: !algebra.field_vector<"bls12-381.fr">, %arg26: ui64):
      %107 = "exec.boolean"(%arg24) <{site = "s17", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%107)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%108: i1):  // pred: ^bb0
      %109 = "exec.complete"(%arg24, %108) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%109) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%110: !exec.stop):  // pred: ^bb0
      %111 = "exec.failed"(%110) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%111) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_6", sym_visibility = "private"}> ({
    ^bb0(%arg20: !runtime.scope, %arg21: !algebra.field_vector<"bls12-381.fr">, %arg22: ui64, %arg23: ui64):
      %96 = "exec.apply"(%arg20, %arg21) <{binding = @zkl_binding_1, parameters = [], site = "s23"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%96)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%97: ui64):  // pred: ^bb0
      %98 = "exec.apply"(%arg20, %97, %arg23) <{binding = @zkl_binding_4, parameters = [], site = "s24"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%98)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%99: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %100 = "exec.failed"(%99) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%100) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%101: ui64):  // pred: ^bb1
      %102 = "func.call"(%arg20, %arg22) <{callee = @s3h7a6b6311h6d756c74696c696e6561724h726f7773}> {runtime.site = "s25"} : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%102)[^bb4, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%103: ui64):  // pred: ^bb3
      %104 = "exec.apply"(%arg20, %101, %103) <{binding = @zkl_binding_3, parameters = [], site = "s26"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%104)[^bb5, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb5(%105: i1):  // pred: ^bb4
      %106 = "exec.complete"(%arg20, %105) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%106) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_7", sym_visibility = "private"}> ({
    ^bb0(%arg16: !runtime.scope, %arg17: !algebra.field_vector<"bls12-381.fr">, %arg18: ui64, %arg19: ui64):
      %91 = "exec.boolean"(%arg16) <{site = "s28", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%91)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%92: i1):  // pred: ^bb0
      %93 = "exec.complete"(%arg16, %92) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%93) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%94: !exec.stop):  // pred: ^bb0
      %95 = "exec.failed"(%94) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%95) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "s3h7a6b637h696e64696365734h6c657373", sym_visibility = "private"}> ({
    ^bb0(%arg13: !runtime.scope, %arg14: ui64, %arg15: ui64):
      %86 = "exec.apply"(%arg13, %arg14, %arg15) <{binding = @zkl_binding_5, parameters = [], site = "s0"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%86)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%87: i1):  // pred: ^bb0
      %88 = "exec.returned"(%87) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%88) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%89: !exec.stop):  // pred: ^bb0
      %90 = "exec.failed"(%89) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%90) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.origin = ["s3h7a6b637h696e64696365734h6c657373", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "s3h7a6b6311h6d756c74696c696e6561724h726f7773", sym_visibility = "private"}> ({
    ^bb0(%arg11: !runtime.scope, %arg12: ui64):
      %39 = "exec.apply"(%arg11) <{binding = @zkl_binding_0, parameters = ["64"], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%39)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%40: ui64):  // pred: ^bb0
      %41 = "func.call"(%arg11, %arg12, %40) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s1"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%41)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%42: !exec.stop):  // 14 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12, ^bb14, ^bb15, ^bb19, ^bb21
      %43 = "exec.failed"(%42) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%43) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%44: i1):  // pred: ^bb1
      %45 = "exec.test"(%arg11, %44) <{site = "s2"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%45)[^bb4, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb4(%46: i1):  // pred: ^bb3
      "cf.cond_br"(%46)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %47 = "runtime.enter_scope"(%arg11) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s2"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%47)[^bb8, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %48 = "runtime.enter_scope"(%arg11) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s2"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%48)[^bb11, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // 2 preds: ^bb10, ^bb13
      %49 = "exec.apply"(%arg11) <{binding = @zkl_binding_0, parameters = ["1"], site = "s3"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%49)[^bb14, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb8(%50: !runtime.scope):  // pred: ^bb5
      %51 = "func.call"(%50) <{callee = @zkl_control_8}> : (!runtime.scope) -> !exec.outcome<>
      %52 = "runtime.exit_scope"(%50, %51) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%52)[^bb9, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb9(%53: !runtime.transfer<>):  // pred: ^bb8
      %54 = "runtime.accept_transfer"(%arg11, %53) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%54)[^bb10, ^bb2] : (!exec.outcome<>) -> ()
    ^bb10:  // pred: ^bb9
      "cf.br"()[^bb7] : () -> ()
    ^bb11(%55: !runtime.scope):  // pred: ^bb6
      %56 = "func.call"(%55) <{callee = @zkl_control_9}> : (!runtime.scope) -> !exec.outcome<>
      %57 = "runtime.exit_scope"(%55, %56) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%57)[^bb12, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb12(%58: !runtime.transfer<>):  // pred: ^bb11
      %59 = "runtime.accept_transfer"(%arg11, %58) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%59)[^bb13, ^bb2] : (!exec.outcome<>) -> ()
    ^bb13:  // pred: ^bb12
      "cf.br"()[^bb7] : () -> ()
    ^bb14(%60: ui64):  // pred: ^bb7
      %61 = "exec.apply"(%arg11) <{binding = @zkl_binding_0, parameters = ["0"], site = "s5"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%61)[^bb15, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb15(%62: ui64):  // pred: ^bb14
      %63 = "exec.range"(%arg11, %62, %arg12) <{site = "s6"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%63)[^bb16, ^bb2] : (!exec.outcome<(i64, i64)>) -> ()
    ^bb16(%64: i64, %65: i64):  // pred: ^bb15
      %66 = "runtime.borrow_transfer"(%arg11, %60) : (!runtime.scope, ui64) -> !runtime.transfer<(ui64)>
      "cf.br"(%64, %66)[^bb17] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb17(%67: i64, %68: !runtime.transfer<(ui64)>):  // 2 preds: ^bb16, ^bb20
      %69 = "arith.cmpi"(%67, %65) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%69, %68)[^bb18, ^bb19] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(ui64)>) -> ()
    ^bb18:  // pred: ^bb17
      %70 = "runtime.iteration"(%arg11, %67) <{site = "s6"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%70)[^bb22, ^bb21] : (!exec.outcome<(ui64)>) -> ()
    ^bb19(%71: !runtime.transfer<(ui64)>):  // pred: ^bb17
      %72 = "runtime.accept_transfer"(%arg11, %71) : (!runtime.scope, !runtime.transfer<(ui64)>) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%72)[^bb25, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb20(%73: !runtime.transfer<(ui64)>):  // pred: ^bb24
      %74 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %75 = "arith.addi"(%67, %74) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%75, %73)[^bb17] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb21(%76: !exec.stop):  // 3 preds: ^bb18, ^bb22, ^bb23
      "runtime.release_transfer"(%68) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%76)[^bb2] : (!exec.stop) -> ()
    ^bb22(%77: ui64):  // pred: ^bb18
      %78 = "runtime.transfer_values"(%68) : (!runtime.transfer<(ui64)>) -> ui64
      %79 = "runtime.enter_scope"(%arg11, %67, %77, %78) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 2>, site = "s6"}> : (!runtime.scope, i64, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%79)[^bb23, ^bb21] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb23(%80: !runtime.scope):  // pred: ^bb22
      %81 = "func.call"(%80, %77, %78) <{callee = @zkl_control_10}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      %82 = "runtime.exit_scope"(%80, %81) : (!runtime.scope, !exec.outcome<(ui64)>) -> !exec.outcome<(!runtime.transfer<(ui64)>)>
      "exec.dispatch"(%82)[^bb24, ^bb21] : (!exec.outcome<(!runtime.transfer<(ui64)>)>) -> ()
    ^bb24(%83: !runtime.transfer<(ui64)>):  // pred: ^bb23
      "runtime.release_transfer"(%68) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%83)[^bb20] : (!runtime.transfer<(ui64)>) -> ()
    ^bb25(%84: ui64):  // pred: ^bb19
      %85 = "exec.returned"(%84) : (ui64) -> !exec.outcome<(ui64)>
      "func.return"(%85) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561724h726f7773", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_8", sym_visibility = "private"}> ({
    ^bb0(%arg10: !runtime.scope):
      %38 = "exec.complete"(%arg10) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%38) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_9", sym_visibility = "private"}> ({
    ^bb0(%arg9: !runtime.scope):
      %35 = "exec.reject"(%arg9) <{reason = "reject", site = "s2_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%35)[^bb1] : (!exec.stop) -> ()
    ^bb1(%36: !exec.stop):  // pred: ^bb0
      %37 = "exec.failed"(%36) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%37) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "zkl_control_10", sym_visibility = "private"}> ({
    ^bb0(%arg6: !runtime.scope, %arg7: ui64, %arg8: ui64):
      %28 = "exec.apply"(%arg6) <{binding = @zkl_binding_0, parameters = ["2"], site = "s7"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%28)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%29: ui64):  // pred: ^bb0
      %30 = "exec.apply"(%arg6, %arg8, %29) <{binding = @zkl_binding_6, parameters = [], site = "s8"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%30)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%31: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %32 = "exec.failed"(%31) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%32) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%33: ui64):  // pred: ^bb1
      %34 = "exec.complete"(%arg6, %33) : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "func.return"(%34) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>, no_inline, sym_name = "zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087", sym_visibility = "private"}> ({
    ^bb0(%arg2: !runtime.scope, %arg3: !algebra.field_vector<"bls12-381.fr">, %arg4: ui64, %arg5: ui64):
      %4 = "exec.apply"(%arg2) <{binding = @zkl_binding_0, parameters = ["0"], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%4)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%5: ui64):  // pred: ^bb0
      %6 = "func.call"(%arg2, %5, %arg4) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s2"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%6)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%7: !exec.stop):  // 10 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12
      %8 = "exec.failed"(%7) : (!exec.stop) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%8) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb3(%9: i1):  // pred: ^bb1
      %10 = "exec.test"(%arg2, %9) <{site = "s3"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%10)[^bb4, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb4(%11: i1):  // pred: ^bb3
      "cf.cond_br"(%11)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %12 = "runtime.enter_scope"(%arg2) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s3"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%12)[^bb8, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %13 = "runtime.enter_scope"(%arg2) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s3"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%13)[^bb11, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // 2 preds: ^bb10, ^bb13
      %14 = "exec.apply"(%arg2, %arg3) <{binding = @zkl_binding_7, parameters = [], site = "s5"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%14)[^bb14, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb8(%15: !runtime.scope):  // pred: ^bb5
      %16 = "func.call"(%15) <{callee = @zkl_control_11}> : (!runtime.scope) -> !exec.outcome<>
      %17 = "runtime.exit_scope"(%15, %16) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%17)[^bb9, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb9(%18: !runtime.transfer<>):  // pred: ^bb8
      %19 = "runtime.accept_transfer"(%arg2, %18) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%19)[^bb10, ^bb2] : (!exec.outcome<>) -> ()
    ^bb10:  // pred: ^bb9
      "cf.br"()[^bb7] : () -> ()
    ^bb11(%20: !runtime.scope):  // pred: ^bb6
      %21 = "func.call"(%20) <{callee = @zkl_control_12}> : (!runtime.scope) -> !exec.outcome<>
      %22 = "runtime.exit_scope"(%20, %21) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%22)[^bb12, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb12(%23: !runtime.transfer<>):  // pred: ^bb11
      %24 = "runtime.accept_transfer"(%arg2, %23) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%24)[^bb13, ^bb2] : (!exec.outcome<>) -> ()
    ^bb13:  // pred: ^bb12
      "cf.br"()[^bb7] : () -> ()
    ^bb14(%25: !algebra.field_vector<"bls12-381.fr">, %26: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb7
      %27 = "exec.returned"(%25, %26) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>
      "func.return"(%27) : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561726h68616c766573", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_11", sym_visibility = "private"}> ({
    ^bb0(%arg1: !runtime.scope):
      %3 = "exec.complete"(%arg1) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%3) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_12", sym_visibility = "private"}> ({
    ^bb0(%arg0: !runtime.scope):
      %0 = "exec.reject"(%arg0) <{reason = "reject", site = "s3_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%0)[^bb1] : (!exec.stop) -> ()
    ^bb1(%1: !exec.stop):  // pred: ^bb0
      %2 = "exec.failed"(%1) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%2) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
  }) : () -> ()
}) : () -> ()

