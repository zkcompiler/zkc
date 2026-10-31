!f = !algebra.field<"bls12-381.fr">
!v = !algebra.field_vector<"bls12-381.fr">
!mode = !data.variant<#data.identity<["atom", "Batch"]>, [#data.alternative<"none">, #data.alternative<"plain", [!algebra.field_vector<"bls12-381.fr">]>, #data.alternative<"scaled", [!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">]>]>
!packet = !data.variant<#data.identity<["atom", "Announcement"]>, [#data.alternative<"record", [!algebra.group<"bls12-381.g1">, !data.variant<#data.identity<["atom", "Batch"]>, [#data.alternative<"none">, #data.alternative<"plain", [!algebra.field_vector<"bls12-381.fr">]>, #data.alternative<"scaled", [!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">]>]>]>]>
module {
"protocol.module"() ({
"runtime.binding"() {sym_name="index",contract="index.constant",arguments=[],implementation="",function_type=(!runtime.scope) -> !exec.outcome<(ui64)>} : ()->()
"runtime.binding"() {sym_name="constant",contract="field.constant",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>} : ()->()
"runtime.binding"() {sym_name="length",contract="vector.length",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(ui64)>} : ()->()
"runtime.binding"() {sym_name="sum",contract="vector.sum",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>} : ()->()
"runtime.binding"() {sym_name="multiply",contract="field.mul",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>} : ()->()
    func.func @inspect(%arg0: !runtime.scope, %arg1: !mode) -> !exec.outcome<(ui64, !f, ui64)> attributes {no_inline, runtime.origin = ["inspect", []]} {
      "exec.match"(%arg0, %arg1)[^bb2, ^bb3, ^bb4, ^bb5] <{alternatives = ["none", "plain", "scaled"], site = "mode_10", successor_operand_segments = array<i32: 0, 0, 0, 0 >}> : (!runtime.scope, !mode) -> ()
    ^bb1(%0: ui64, %1: !f, %2: ui64):  // 3 preds: ^bb8, ^bb11, ^bb14
      %3 = "exec.returned"(%0, %1, %2) : (ui64, !f, ui64) -> !exec.outcome<(ui64, !f, ui64)>
      return %3 : !exec.outcome<(ui64, !f, ui64)>
    ^bb2(%4: !exec.stop):  // 10 preds: ^bb0, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb9, ^bb10, ^bb12, ^bb13
      %5 = "exec.failed"(%4) : (!exec.stop) -> !exec.outcome<(ui64, !f, ui64)>
      return %5 : !exec.outcome<(ui64, !f, ui64)>
    ^bb3:  // pred: ^bb0
      %6 = "runtime.enter_scope"(%arg0) <{kind = "match", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "none", site = "mode_10"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%6)[^bb6, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb4(%7: !v):  // pred: ^bb0
      %8 = "runtime.enter_scope"(%arg0, %7) <{kind = "match", operandSegmentSizes = array<i32: 1, 0, 1>, selection = "plain", site = "mode_10"}> : (!runtime.scope, !v) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%8)[^bb9, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb5(%9: !v, %10: !f):  // pred: ^bb0
      %11 = "runtime.enter_scope"(%arg0, %9, %10) <{kind = "match", operandSegmentSizes = array<i32: 1, 0, 2>, selection = "scaled", site = "mode_10"}> : (!runtime.scope, !v, !f) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%11)[^bb12, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb6(%12: !runtime.scope):  // pred: ^bb3
      %13 = call @control_0(%12) : (!runtime.scope) -> !exec.outcome<(ui64, !f, ui64)>
      %14 = "runtime.exit_scope"(%12, %13) : (!runtime.scope, !exec.outcome<(ui64, !f, ui64)>) -> !exec.outcome<(!runtime.transfer<(ui64, !f, ui64)>)>
      "exec.dispatch"(%14)[^bb7, ^bb2] : (!exec.outcome<(!runtime.transfer<(ui64, !f, ui64)>)>) -> ()
    ^bb7(%15: !runtime.transfer<(ui64, !f, ui64)>):  // pred: ^bb6
      %16 = "runtime.accept_transfer"(%arg0, %15) : (!runtime.scope, !runtime.transfer<(ui64, !f, ui64)>) -> !exec.outcome<(ui64, !f, ui64)>
      "exec.dispatch"(%16)[^bb8, ^bb2] : (!exec.outcome<(ui64, !f, ui64)>) -> ()
    ^bb8(%17: ui64, %18: !f, %19: ui64):  // pred: ^bb7
      cf.br ^bb1(%17, %18, %19 : ui64, !f, ui64)
    ^bb9(%20: !runtime.scope):  // pred: ^bb4
      %21 = call @control_1(%20, %7) : (!runtime.scope, !v) -> !exec.outcome<(ui64, !f, ui64)>
      %22 = "runtime.exit_scope"(%20, %21) : (!runtime.scope, !exec.outcome<(ui64, !f, ui64)>) -> !exec.outcome<(!runtime.transfer<(ui64, !f, ui64)>)>
      "exec.dispatch"(%22)[^bb10, ^bb2] : (!exec.outcome<(!runtime.transfer<(ui64, !f, ui64)>)>) -> ()
    ^bb10(%23: !runtime.transfer<(ui64, !f, ui64)>):  // pred: ^bb9
      %24 = "runtime.accept_transfer"(%arg0, %23) : (!runtime.scope, !runtime.transfer<(ui64, !f, ui64)>) -> !exec.outcome<(ui64, !f, ui64)>
      "exec.dispatch"(%24)[^bb11, ^bb2] : (!exec.outcome<(ui64, !f, ui64)>) -> ()
    ^bb11(%25: ui64, %26: !f, %27: ui64):  // pred: ^bb10
      cf.br ^bb1(%25, %26, %27 : ui64, !f, ui64)
    ^bb12(%28: !runtime.scope):  // pred: ^bb5
      %29 = call @control_2(%28, %9, %10) : (!runtime.scope, !v, !f) -> !exec.outcome<(ui64, !f, ui64)>
      %30 = "runtime.exit_scope"(%28, %29) : (!runtime.scope, !exec.outcome<(ui64, !f, ui64)>) -> !exec.outcome<(!runtime.transfer<(ui64, !f, ui64)>)>
      "exec.dispatch"(%30)[^bb13, ^bb2] : (!exec.outcome<(!runtime.transfer<(ui64, !f, ui64)>)>) -> ()
    ^bb13(%31: !runtime.transfer<(ui64, !f, ui64)>):  // pred: ^bb12
      %32 = "runtime.accept_transfer"(%arg0, %31) : (!runtime.scope, !runtime.transfer<(ui64, !f, ui64)>) -> !exec.outcome<(ui64, !f, ui64)>
      "exec.dispatch"(%32)[^bb14, ^bb2] : (!exec.outcome<(ui64, !f, ui64)>) -> ()
    ^bb14(%33: ui64, %34: !f, %35: ui64):  // pred: ^bb13
      cf.br ^bb1(%33, %34, %35 : ui64, !f, ui64)
    }
    func.func private @control_0(%arg0: !runtime.scope) -> !exec.outcome<(ui64, !f, ui64)> attributes {no_inline, runtime.region} {
      %0 = "exec.apply"(%arg0) <{binding = @index, parameters = [0 : ui64], site = "count_1"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1: ui64):  // pred: ^bb0
      %2 = "exec.apply"(%arg0) <{binding = @constant, parameters = [#algebra.literal<!algebra.field<"bls12-381.fr">, 0 : ui255>], site = "value_2"}> : (!runtime.scope) -> !exec.outcome<(!f)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb2(%3: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(ui64, !f, ui64)>
      return %4 : !exec.outcome<(ui64, !f, ui64)>
    ^bb3(%5: !f):  // pred: ^bb1
      %6 = "exec.complete"(%arg0, %1, %5, %1) : (!runtime.scope, ui64, !f, ui64) -> !exec.outcome<(ui64, !f, ui64)>
      return %6 : !exec.outcome<(ui64, !f, ui64)>
    }
    func.func private @control_1(%arg0: !runtime.scope, %arg1: !v) -> !exec.outcome<(ui64, !f, ui64)> attributes {no_inline, runtime.region} {
      %0 = "exec.apply"(%arg0, %arg1) <{binding = @length, parameters = [], site = "count_3"}> : (!runtime.scope, !v) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1: ui64):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %arg1) <{binding = @sum, parameters = [], site = "value_4"}> : (!runtime.scope, !v) -> !exec.outcome<(!f)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb2(%3: !exec.stop):  // 3 preds: ^bb0, ^bb1, ^bb3
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(ui64, !f, ui64)>
      return %4 : !exec.outcome<(ui64, !f, ui64)>
    ^bb3(%5: !f):  // pred: ^bb1
      %6 = "exec.apply"(%arg0) <{binding = @index, parameters = [1 : ui64], site = "tag_5"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb4(%7: ui64):  // pred: ^bb3
      %8 = "exec.complete"(%arg0, %1, %5, %7) : (!runtime.scope, ui64, !f, ui64) -> !exec.outcome<(ui64, !f, ui64)>
      return %8 : !exec.outcome<(ui64, !f, ui64)>
    }
    func.func private @control_2(%arg0: !runtime.scope, %arg1: !v, %arg2: !f) -> !exec.outcome<(ui64, !f, ui64)> attributes {no_inline, runtime.region} {
      %0 = "exec.apply"(%arg0, %arg1) <{binding = @length, parameters = [], site = "count_6"}> : (!runtime.scope, !v) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1: ui64):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %arg1) <{binding = @sum, parameters = [], site = "sum_7"}> : (!runtime.scope, !v) -> !exec.outcome<(!f)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb2(%3: !exec.stop):  // 4 preds: ^bb0, ^bb1, ^bb3, ^bb4
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(ui64, !f, ui64)>
      return %4 : !exec.outcome<(ui64, !f, ui64)>
    ^bb3(%5: !f):  // pred: ^bb1
      %6 = "exec.apply"(%arg0, %5, %arg2) <{binding = @multiply, parameters = [], site = "value_8"}> : (!runtime.scope, !f, !f) -> !exec.outcome<(!f)>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<(!f)>) -> ()
    ^bb4(%7: !f):  // pred: ^bb3
      %8 = "exec.apply"(%arg0) <{binding = @index, parameters = [2 : ui64], site = "tag_9"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%8)[^bb5, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb5(%9: ui64):  // pred: ^bb4
      %10 = "exec.complete"(%arg0, %1, %7, %9) : (!runtime.scope, ui64, !f, ui64) -> !exec.outcome<(ui64, !f, ui64)>
      return %10 : !exec.outcome<(ui64, !f, ui64)>
    }


relation.declare @schnorr_relation {kind="external", key="example/schnorr", revision="0", signature=(!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> i1, purposes=["parameter", "statement", "witness"]}
"protocol.func"() ({
^entry(%g: !algebra.group<"bls12-381.g1">, %x: !algebra.field<"bls12-381.fr">, %y: !algebra.group<"bls12-381.g1">, %nonce: !protocol.service_ref<"random.bls12-381.fr/0">, %challenge_service: !protocol.service_ref<"random.bls12-381.fr/0">, %mode:!mode, %count:ui64, %expected:!f, %tag:ui64):
protocol.statement @schnorr_relation(%g, %y, %x) {selectors=["Bob","Bob","Alice"], acceptance=0 : i64} : !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">
%k = "protocol.query"(%nonce) {method="draw", owner="Alice", site="nonce"} : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
%r = algebra.group_scale %g, %k : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
%packet = "data.make"(%r,%mode) {alternative="record"} : (!algebra.group<"bls12-381.g1">,!mode)->!packet
%received = protocol.exchange %packet {site="commitment",sender="Alice",receiver="Bob"} : !packet
%commitment = "data.get"(%received) {index=0:i64} : (!packet)->!algebra.group<"bls12-381.g1">
%batch = "data.get"(%received) {index=1:i64} : (!packet)->!mode
%checked:3 = "protocol.local_call"(%batch) {callee=@inspect,role="Bob",site="batch"} : (!mode)->(ui64,!f,ui64)
%count_ok = "data.index_equal"(%checked#0,%count) : (ui64,ui64)->i1
%tag_ok = "data.index_equal"(%checked#2,%tag) : (ui64,ui64)->i1
%value_ok = algebra.field_equal %checked#1,%expected : (!f,!f)->i1
protocol.guard %count_ok {owner="Bob",site="count_check"}
protocol.guard %tag_ok {owner="Bob",site="tag_check"}
protocol.guard %value_ok {owner="Bob",site="value_check"}
%c = "protocol.query"(%challenge_service) {method="draw", owner="Bob", site="draw_challenge"} : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
%challenge = protocol.exchange %c {site="challenge",sender="Bob",receiver="Alice"} : !algebra.field<"bls12-381.fr">
%cx = algebra.field_multiply %challenge, %x : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
%z = algebra.field_add %k, %cx : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
%response = protocol.exchange %z {site="response",sender="Alice",receiver="Bob"} : !algebra.field<"bls12-381.fr">
%lhs = algebra.group_scale %g, %response : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
%cy = algebra.group_scale %y, %challenge : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
%rhs = algebra.group_add %commitment, %cy : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> !algebra.group<"bls12-381.g1">
%ok = algebra.group_equal %lhs, %rhs : (!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> i1
"protocol.return"(%ok) : (i1) -> ()
}) {sym_name="main", function_type=(!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">, !algebra.group<"bls12-381.g1">, !protocol.service_ref<"random.bls12-381.fr/0">, !protocol.service_ref<"random.bls12-381.fr/0">,!mode,ui64,!f,ui64) -> (i1), roles=["Alice", "Bob"], input_roles=[["Alice", "Bob"], ["Alice"], ["Alice", "Bob"], ["Alice"], ["Bob"],["Alice"],["Bob"],["Bob"],["Bob"]], output_roles=[["Bob"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> ()
}
