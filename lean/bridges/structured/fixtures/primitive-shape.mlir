"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "runtime.binding"() <{arguments = [], contract = "index.mul", implementation = "", sym_name = "zkl_binding_6"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.less", implementation = "", sym_name = "zkl_binding_5"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.div", implementation = "", sym_name = "zkl_binding_4"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.equal", implementation = "", sym_name = "zkl_binding_3"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.mod", implementation = "", sym_name = "zkl_binding_2"}> : () -> ()
    "runtime.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.length", implementation = "", sym_name = "zkl_binding_1"}> : () -> ()
    "runtime.binding"() <{arguments = [], contract = "index.constant", implementation = "", sym_name = "zkl_binding_0"}> : () -> ()
    "protocol.func"() <{contracts = [], function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1, input_roles = [["role00000000"], ["role00000000"], ["role00000000"]], origin = ["primitive_examples::Shape", []], output_roles = [["role00000000"]], roles = ["role00000000"], sym_name = "s18h7072696d69746976655f6578616d706c65735h5368617065"}> ({
    ^bb0(%arg32: !algebra.field_vector<"bls12-381.fr">, %arg33: ui64, %arg34: ui64):
      %165 = "protocol.local_call"(%arg32, %arg33, %arg34) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655, role = "role00000000", site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1
      "protocol.return"(%165) : (i1) -> ()
    }) : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", sym_visibility = "private"}> ({
    ^bb0(%arg28: !runtime.scope, %arg29: !algebra.field_vector<"bls12-381.fr">, %arg30: ui64, %arg31: ui64):
      %107 = "exec.apply"(%arg28) <{binding = @zkl_binding_0, parameters = ["0"], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%107)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%108: ui64):  // pred: ^bb0
      %109 = "func.call"(%arg28, %108, %arg31) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s1"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%109)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%110: !exec.stop):  // 23 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12, ^bb15, ^bb16, ^bb17, ^bb18, ^bb19, ^bb21, ^bb22, ^bb25, ^bb26, ^bb28, ^bb29, ^bb31, ^bb32
      %111 = "exec.failed"(%110) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%111) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%112: i1):  // pred: ^bb1
      %113 = "exec.test"(%arg28, %112) <{site = "s3"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%113)[^bb4, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb4(%114: i1):  // pred: ^bb3
      "cf.cond_br"(%114)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %115 = "runtime.enter_scope"(%arg28, %arg30) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "then", site = "s3"}> : (!runtime.scope, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%115)[^bb8, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %116 = "runtime.enter_scope"(%arg28, %arg30) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "else", site = "s3"}> : (!runtime.scope, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%116)[^bb11, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7(%117: i1):  // 2 preds: ^bb10, ^bb13
      %118 = "exec.test"(%arg28, %117) <{site = "s11"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%118)[^bb14, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb8(%119: !runtime.scope):  // pred: ^bb5
      %120 = "func.call"(%119, %arg30) <{callee = @zkl_control_0}> : (!runtime.scope, ui64) -> !exec.outcome<(i1)>
      %121 = "runtime.exit_scope"(%119, %120) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%121)[^bb9, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb9(%122: !runtime.transfer<(i1)>):  // pred: ^bb8
      %123 = "runtime.accept_transfer"(%arg28, %122) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%123)[^bb10, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb10(%124: i1):  // pred: ^bb9
      "cf.br"(%124)[^bb7] : (i1) -> ()
    ^bb11(%125: !runtime.scope):  // pred: ^bb6
      %126 = "func.call"(%125, %arg30) <{callee = @zkl_control_1}> : (!runtime.scope, ui64) -> !exec.outcome<(i1)>
      %127 = "runtime.exit_scope"(%125, %126) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%127)[^bb12, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb12(%128: !runtime.transfer<(i1)>):  // pred: ^bb11
      %129 = "runtime.accept_transfer"(%arg28, %128) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%129)[^bb13, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb13(%130: i1):  // pred: ^bb12
      "cf.br"(%130)[^bb7] : (i1) -> ()
    ^bb14(%131: i1):  // pred: ^bb7
      "cf.cond_br"(%131)[^bb15, ^bb16] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb15:  // pred: ^bb14
      %132 = "runtime.enter_scope"(%arg28, %arg29, %arg31) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "then", site = "s11"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%132)[^bb18, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb16:  // pred: ^bb14
      %133 = "runtime.enter_scope"(%arg28, %arg29, %arg31) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "else", site = "s11"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%133)[^bb21, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb17(%134: i1):  // 2 preds: ^bb20, ^bb23
      %135 = "exec.test"(%arg28, %134) <{site = "s22"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%135)[^bb24, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb18(%136: !runtime.scope):  // pred: ^bb15
      %137 = "func.call"(%136, %arg29, %arg31) <{callee = @zkl_control_2}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>
      %138 = "runtime.exit_scope"(%136, %137) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%138)[^bb19, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb19(%139: !runtime.transfer<(i1)>):  // pred: ^bb18
      %140 = "runtime.accept_transfer"(%arg28, %139) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%140)[^bb20, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb20(%141: i1):  // pred: ^bb19
      "cf.br"(%141)[^bb17] : (i1) -> ()
    ^bb21(%142: !runtime.scope):  // pred: ^bb16
      %143 = "func.call"(%142, %arg29, %arg31) <{callee = @zkl_control_3}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>
      %144 = "runtime.exit_scope"(%142, %143) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%144)[^bb22, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb22(%145: !runtime.transfer<(i1)>):  // pred: ^bb21
      %146 = "runtime.accept_transfer"(%arg28, %145) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%146)[^bb23, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb23(%147: i1):  // pred: ^bb22
      "cf.br"(%147)[^bb17] : (i1) -> ()
    ^bb24(%148: i1):  // pred: ^bb17
      "cf.cond_br"(%148)[^bb25, ^bb26] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb25:  // pred: ^bb24
      %149 = "runtime.enter_scope"(%arg28, %arg29, %arg30, %arg31) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "then", site = "s22"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%149)[^bb28, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb26:  // pred: ^bb24
      %150 = "runtime.enter_scope"(%arg28, %arg29, %arg30, %arg31) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 3>, selection = "else", site = "s22"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%150)[^bb31, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb27(%151: i1):  // 2 preds: ^bb30, ^bb33
      %152 = "exec.returned"(%151) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%152) : (!exec.outcome<(i1)>) -> ()
    ^bb28(%153: !runtime.scope):  // pred: ^bb25
      %154 = "func.call"(%153, %arg29, %arg30, %arg31) <{callee = @zkl_control_4}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      %155 = "runtime.exit_scope"(%153, %154) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%155)[^bb29, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb29(%156: !runtime.transfer<(i1)>):  // pred: ^bb28
      %157 = "runtime.accept_transfer"(%arg28, %156) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%157)[^bb30, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb30(%158: i1):  // pred: ^bb29
      "cf.br"(%158)[^bb27] : (i1) -> ()
    ^bb31(%159: !runtime.scope):  // pred: ^bb26
      %160 = "func.call"(%159, %arg29, %arg30, %arg31) <{callee = @zkl_control_5}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>
      %161 = "runtime.exit_scope"(%159, %160) : (!runtime.scope, !exec.outcome<(i1)>) -> !exec.outcome<(!runtime.transfer<(i1)>)>
      "exec.dispatch"(%161)[^bb32, ^bb2] : (!exec.outcome<(!runtime.transfer<(i1)>)>) -> ()
    ^bb32(%162: !runtime.transfer<(i1)>):  // pred: ^bb31
      %163 = "runtime.accept_transfer"(%arg28, %162) : (!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(i1)>
      "exec.dispatch"(%163)[^bb33, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb33(%164: i1):  // pred: ^bb32
      "cf.br"(%164)[^bb27] : (i1) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_0", sym_visibility = "private"}> ({
    ^bb0(%arg26: !runtime.scope, %arg27: ui64):
      %100 = "exec.apply"(%arg26) <{binding = @zkl_binding_0, parameters = ["64"], site = "s4"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%100)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%101: ui64):  // pred: ^bb0
      %102 = "func.call"(%arg26, %arg27, %101) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s5"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%102)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%103: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %104 = "exec.failed"(%103) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%104) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%105: i1):  // pred: ^bb1
      %106 = "exec.complete"(%arg26, %105) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%106) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_1", sym_visibility = "private"}> ({
    ^bb0(%arg24: !runtime.scope, %arg25: ui64):
      %95 = "exec.boolean"(%arg24) <{site = "s7", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%95)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%96: i1):  // pred: ^bb0
      %97 = "exec.complete"(%arg24, %96) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%97) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%98: !exec.stop):  // pred: ^bb0
      %99 = "exec.failed"(%98) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%99) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_2", sym_visibility = "private"}> ({
    ^bb0(%arg21: !runtime.scope, %arg22: !algebra.field_vector<"bls12-381.fr">, %arg23: ui64):
      %84 = "exec.apply"(%arg21, %arg22) <{binding = @zkl_binding_1, parameters = [], site = "s12"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%84)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%85: ui64):  // pred: ^bb0
      %86 = "exec.apply"(%arg21, %85, %arg23) <{binding = @zkl_binding_2, parameters = [], site = "s13"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%86)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%87: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %88 = "exec.failed"(%87) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%88) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%89: ui64):  // pred: ^bb1
      %90 = "exec.apply"(%arg21) <{binding = @zkl_binding_0, parameters = ["0"], site = "s14"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%90)[^bb4, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%91: ui64):  // pred: ^bb3
      %92 = "exec.apply"(%arg21, %89, %91) <{binding = @zkl_binding_3, parameters = [], site = "s15"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%92)[^bb5, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb5(%93: i1):  // pred: ^bb4
      %94 = "exec.complete"(%arg21, %93) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%94) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_3", sym_visibility = "private"}> ({
    ^bb0(%arg18: !runtime.scope, %arg19: !algebra.field_vector<"bls12-381.fr">, %arg20: ui64):
      %79 = "exec.boolean"(%arg18) <{site = "s17", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%79)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%80: i1):  // pred: ^bb0
      %81 = "exec.complete"(%arg18, %80) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%81) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%82: !exec.stop):  // pred: ^bb0
      %83 = "exec.failed"(%82) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%83) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_4", sym_visibility = "private"}> ({
    ^bb0(%arg14: !runtime.scope, %arg15: !algebra.field_vector<"bls12-381.fr">, %arg16: ui64, %arg17: ui64):
      %68 = "exec.apply"(%arg14, %arg15) <{binding = @zkl_binding_1, parameters = [], site = "s23"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%68)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%69: ui64):  // pred: ^bb0
      %70 = "exec.apply"(%arg14, %69, %arg17) <{binding = @zkl_binding_4, parameters = [], site = "s24"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%70)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%71: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %72 = "exec.failed"(%71) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%72) : (!exec.outcome<(i1)>) -> ()
    ^bb3(%73: ui64):  // pred: ^bb1
      %74 = "func.call"(%arg14, %arg16) <{callee = @s3h7a6b6311h6d756c74696c696e6561724h726f7773}> {runtime.site = "s25"} : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%74)[^bb4, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%75: ui64):  // pred: ^bb3
      %76 = "exec.apply"(%arg14, %73, %75) <{binding = @zkl_binding_3, parameters = [], site = "s26"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%76)[^bb5, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb5(%77: i1):  // pred: ^bb4
      %78 = "exec.complete"(%arg14, %77) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%78) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "zkl_control_5", sym_visibility = "private"}> ({
    ^bb0(%arg10: !runtime.scope, %arg11: !algebra.field_vector<"bls12-381.fr">, %arg12: ui64, %arg13: ui64):
      %63 = "exec.boolean"(%arg10) <{site = "s28", value = false}> : (!runtime.scope) -> !exec.outcome<(i1)>
      "exec.dispatch"(%63)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%64: i1):  // pred: ^bb0
      %65 = "exec.complete"(%arg10, %64) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "func.return"(%65) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%66: !exec.stop):  // pred: ^bb0
      %67 = "exec.failed"(%66) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%67) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>, no_inline, sym_name = "s3h7a6b637h696e64696365734h6c657373", sym_visibility = "private"}> ({
    ^bb0(%arg7: !runtime.scope, %arg8: ui64, %arg9: ui64):
      %58 = "exec.apply"(%arg7, %arg8, %arg9) <{binding = @zkl_binding_5, parameters = [], site = "s0"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%58)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%59: i1):  // pred: ^bb0
      %60 = "exec.returned"(%59) : (i1) -> !exec.outcome<(i1)>
      "func.return"(%60) : (!exec.outcome<(i1)>) -> ()
    ^bb2(%61: !exec.stop):  // pred: ^bb0
      %62 = "exec.failed"(%61) : (!exec.stop) -> !exec.outcome<(i1)>
      "func.return"(%62) : (!exec.outcome<(i1)>) -> ()
    }) {runtime.origin = ["s3h7a6b637h696e64696365734h6c657373", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "s3h7a6b6311h6d756c74696c696e6561724h726f7773", sym_visibility = "private"}> ({
    ^bb0(%arg5: !runtime.scope, %arg6: ui64):
      %11 = "exec.apply"(%arg5) <{binding = @zkl_binding_0, parameters = ["64"], site = "s0"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%11)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%12: ui64):  // pred: ^bb0
      %13 = "func.call"(%arg5, %arg6, %12) <{callee = @s3h7a6b637h696e64696365734h6c657373}> {runtime.site = "s1"} : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i1)>
      "exec.dispatch"(%13)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%14: !exec.stop):  // 14 preds: ^bb0, ^bb1, ^bb3, ^bb5, ^bb6, ^bb7, ^bb8, ^bb9, ^bb11, ^bb12, ^bb14, ^bb15, ^bb19, ^bb21
      %15 = "exec.failed"(%14) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%15) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%16: i1):  // pred: ^bb1
      %17 = "exec.test"(%arg5, %16) <{site = "s2"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%17)[^bb4, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb4(%18: i1):  // pred: ^bb3
      "cf.cond_br"(%18)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb5:  // pred: ^bb4
      %19 = "runtime.enter_scope"(%arg5) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "s2"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%19)[^bb8, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6:  // pred: ^bb4
      %20 = "runtime.enter_scope"(%arg5) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "s2"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%20)[^bb11, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb7:  // 2 preds: ^bb10, ^bb13
      %21 = "exec.apply"(%arg5) <{binding = @zkl_binding_0, parameters = ["1"], site = "s3"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%21)[^bb14, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb8(%22: !runtime.scope):  // pred: ^bb5
      %23 = "func.call"(%22) <{callee = @zkl_control_6}> : (!runtime.scope) -> !exec.outcome<>
      %24 = "runtime.exit_scope"(%22, %23) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%24)[^bb9, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb9(%25: !runtime.transfer<>):  // pred: ^bb8
      %26 = "runtime.accept_transfer"(%arg5, %25) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%26)[^bb10, ^bb2] : (!exec.outcome<>) -> ()
    ^bb10:  // pred: ^bb9
      "cf.br"()[^bb7] : () -> ()
    ^bb11(%27: !runtime.scope):  // pred: ^bb6
      %28 = "func.call"(%27) <{callee = @zkl_control_7}> : (!runtime.scope) -> !exec.outcome<>
      %29 = "runtime.exit_scope"(%27, %28) : (!runtime.scope, !exec.outcome<>) -> !exec.outcome<(!runtime.transfer<>)>
      "exec.dispatch"(%29)[^bb12, ^bb2] : (!exec.outcome<(!runtime.transfer<>)>) -> ()
    ^bb12(%30: !runtime.transfer<>):  // pred: ^bb11
      %31 = "runtime.accept_transfer"(%arg5, %30) : (!runtime.scope, !runtime.transfer<>) -> !exec.outcome<>
      "exec.dispatch"(%31)[^bb13, ^bb2] : (!exec.outcome<>) -> ()
    ^bb13:  // pred: ^bb12
      "cf.br"()[^bb7] : () -> ()
    ^bb14(%32: ui64):  // pred: ^bb7
      %33 = "exec.apply"(%arg5) <{binding = @zkl_binding_0, parameters = ["0"], site = "s5"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%33)[^bb15, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb15(%34: ui64):  // pred: ^bb14
      %35 = "exec.range"(%arg5, %34, %arg6) <{site = "s6"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(i64, i64)>
      "exec.dispatch"(%35)[^bb16, ^bb2] : (!exec.outcome<(i64, i64)>) -> ()
    ^bb16(%36: i64, %37: i64):  // pred: ^bb15
      %38 = "runtime.borrow_transfer"(%arg5, %32) : (!runtime.scope, ui64) -> !runtime.transfer<(ui64)>
      "cf.br"(%36, %38)[^bb17] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb17(%39: i64, %40: !runtime.transfer<(ui64)>):  // 2 preds: ^bb16, ^bb20
      %41 = "arith.cmpi"(%39, %37) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "cf.cond_br"(%41, %40)[^bb18, ^bb19] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, !runtime.transfer<(ui64)>) -> ()
    ^bb18:  // pred: ^bb17
      %42 = "runtime.iteration"(%arg5, %39) <{site = "s6"}> : (!runtime.scope, i64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%42)[^bb22, ^bb21] : (!exec.outcome<(ui64)>) -> ()
    ^bb19(%43: !runtime.transfer<(ui64)>):  // pred: ^bb17
      %44 = "runtime.accept_transfer"(%arg5, %43) : (!runtime.scope, !runtime.transfer<(ui64)>) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%44)[^bb25, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb20(%45: !runtime.transfer<(ui64)>):  // pred: ^bb24
      %46 = "arith.constant"() <{value = 1 : i64}> : () -> i64
      %47 = "arith.addi"(%39, %46) <{overflowFlags = #arith.overflow<none>}> : (i64, i64) -> i64
      "cf.br"(%47, %45)[^bb17] : (i64, !runtime.transfer<(ui64)>) -> ()
    ^bb21(%48: !exec.stop):  // 3 preds: ^bb18, ^bb22, ^bb23
      "runtime.release_transfer"(%40) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%48)[^bb2] : (!exec.stop) -> ()
    ^bb22(%49: ui64):  // pred: ^bb18
      %50 = "runtime.transfer_values"(%40) : (!runtime.transfer<(ui64)>) -> ui64
      %51 = "runtime.enter_scope"(%arg5, %39, %49, %50) <{kind = "iteration", operandSegmentSizes = array<i32: 1, 1, 2>, site = "s6"}> : (!runtime.scope, i64, ui64, ui64) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%51)[^bb23, ^bb21] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb23(%52: !runtime.scope):  // pred: ^bb22
      %53 = "func.call"(%52, %49, %50) <{callee = @zkl_control_8}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      %54 = "runtime.exit_scope"(%52, %53) : (!runtime.scope, !exec.outcome<(ui64)>) -> !exec.outcome<(!runtime.transfer<(ui64)>)>
      "exec.dispatch"(%54)[^bb24, ^bb21] : (!exec.outcome<(!runtime.transfer<(ui64)>)>) -> ()
    ^bb24(%55: !runtime.transfer<(ui64)>):  // pred: ^bb23
      "runtime.release_transfer"(%40) : (!runtime.transfer<(ui64)>) -> ()
      "cf.br"(%55)[^bb20] : (!runtime.transfer<(ui64)>) -> ()
    ^bb25(%56: ui64):  // pred: ^bb19
      %57 = "exec.returned"(%56) : (ui64) -> !exec.outcome<(ui64)>
      "func.return"(%57) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.origin = ["s3h7a6b6311h6d756c74696c696e6561724h726f7773", []]} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_6", sym_visibility = "private"}> ({
    ^bb0(%arg4: !runtime.scope):
      %10 = "exec.complete"(%arg4) : (!runtime.scope) -> !exec.outcome<>
      "func.return"(%10) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope) -> !exec.outcome<>, no_inline, sym_name = "zkl_control_7", sym_visibility = "private"}> ({
    ^bb0(%arg3: !runtime.scope):
      %7 = "exec.reject"(%arg3) <{reason = "reject", site = "s2_reject"}> : (!runtime.scope) -> !exec.stop
      "cf.br"(%7)[^bb1] : (!exec.stop) -> ()
    ^bb1(%8: !exec.stop):  // pred: ^bb0
      %9 = "exec.failed"(%8) : (!exec.stop) -> !exec.outcome<>
      "func.return"(%9) : (!exec.outcome<>) -> ()
    }) {runtime.region} : () -> ()
    "func.func"() <{function_type = (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>, no_inline, sym_name = "zkl_control_8", sym_visibility = "private"}> ({
    ^bb0(%arg0: !runtime.scope, %arg1: ui64, %arg2: ui64):
      %0 = "exec.apply"(%arg0) <{binding = @zkl_binding_0, parameters = ["2"], site = "s7"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1: ui64):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %arg2, %1) <{binding = @zkl_binding_6, parameters = [], site = "s8"}> : (!runtime.scope, ui64, ui64) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb2(%3: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(ui64)>
      "func.return"(%4) : (!exec.outcome<(ui64)>) -> ()
    ^bb3(%5: ui64):  // pred: ^bb1
      %6 = "exec.complete"(%arg0, %5) : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      "func.return"(%6) : (!exec.outcome<(ui64)>) -> ()
    }) {runtime.region} : () -> ()
  }) : () -> ()
}) : () -> ()

