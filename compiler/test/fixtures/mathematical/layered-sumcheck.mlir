!f = !algebra.field<"bls12-381.fr">
!t = !poly.multilinear<"bls12-381.fr">
!p = !poly.point<"bls12-381.fr">
!a = !algebra.field_array<"bls12-381.fr", 3>
!q = !poly.polynomial<"bls12-381.fr", 1>
!rng = !protocol.service_ref<"random.bls12-381.fr/0">
!state = !data.variant<#data.identity<["atom", "poly.residual.product"]>, [#data.alternative<"state", [!poly.point<"bls12-381.fr">, !poly.multilinear<"bls12-381.fr">, !poly.multilinear<"bls12-381.fr">]>]>
module { "protocol.module"() ({
 "poly.recipe"() ({ ^slots(%a:!f,%b:!f):
   %p = algebra.field_multiply %a, %b : (!f,!f)->!f
   "poly.recipe_yield"(%p) : (!f)->()
 }) {sym_name="product",degree=2:i64} : ()->()
 "poly.realize"() {sym_name="init",recipe=@product,kind="init",function_type=(ui64,!t,!t)->!state} : ()->()
 "poly.realize"() {sym_name="bind",recipe=@product,kind="bind",function_type=(!state,!f)->!state} : ()->()
 "poly.realize"() {sym_name="round",recipe=@product,kind="round",function_type=(!state)->!a} : ()->()
 "poly.realize"() {sym_name="finish",recipe=@product,kind="finish",function_type=(!state)->(!p,!f)} : ()->()
 "poly.realize"() {sym_name="evaluate",recipe=@product,kind="evaluate",function_type=(!p,!t,!t)->!f} : ()->()
 "runtime.binding"() {sym_name="arity_kernel",contract="poly.table_arity",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope, !poly.multilinear<"bls12-381.fr">) -> !exec.outcome<(ui64)>} : ()->()
    func.func @table_arity(%arg0: !runtime.scope, %arg1: !t) -> !exec.outcome<(ui64)> attributes {no_inline, runtime.origin = ["table_arity", []]} {
      %0 = "exec.apply"(%arg0, %arg1) <{binding = @arity_kernel, parameters = [], site = "arity"}> : (!runtime.scope, !t) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1: ui64):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (ui64) -> !exec.outcome<(ui64)>
      return %2 : !exec.outcome<(ui64)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(ui64)>
      return %4 : !exec.outcome<(ui64)>
    }
    func.func @empty_point(%arg0: !runtime.scope) -> !exec.outcome<(!p)> attributes {no_inline, runtime.origin = ["empty_point", []]} {
      %0 = "exec.apply"(%arg0) <{binding = @empty, parameters = [], site = "empty"}> : (!runtime.scope) -> !exec.outcome<(!p)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!p)>) -> ()
    ^bb1(%1: !p):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!p) -> !exec.outcome<(!p)>
      return %2 : !exec.outcome<(!p)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!p)>
      return %4 : !exec.outcome<(!p)>
    }
    func.func @append_point(%arg0: !runtime.scope, %arg1: !p, %arg2: !f) -> !exec.outcome<(!p)> attributes {no_inline, runtime.origin = ["append_point", []]} {
      %0 = "exec.apply"(%arg0, %arg1, %arg2) <{binding = @append, parameters = [], site = "append"}> : (!runtime.scope, !p, !f) -> !exec.outcome<(!p)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!p)>) -> ()
    ^bb1(%1: !p):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (!p) -> !exec.outcome<(!p)>
      return %2 : !exec.outcome<(!p)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!p)>
      return %4 : !exec.outcome<(!p)>
    }
    func.func @equality_table(%arg0: !runtime.scope, %arg1: !p) -> !exec.outcome<(!t)> attributes {no_inline, runtime.origin = ["equality_table", []]} {
      %0 = "exec.apply"(%arg0, %arg1) <{binding = @weights, parameters = [], site = "weights"}> : (!runtime.scope, !p) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>) -> ()
    ^bb1(%1: !algebra.field_vector<"bls12-381.fr">):  // pred: ^bb0
      %2 = "exec.apply"(%arg0, %1) <{binding = @table, parameters = [], site = "table"}> : (!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!t)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(!t)>) -> ()
    ^bb2(%3: !exec.stop):  // 2 preds: ^bb0, ^bb1
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(!t)>
      return %4 : !exec.outcome<(!t)>
    ^bb3(%5: !t):  // pred: ^bb1
      %6 = "exec.returned"(%5) : (!t) -> !exec.outcome<(!t)>
      return %6 : !exec.outcome<(!t)>
    }

 "runtime.binding"() {sym_name="empty",contract="poly.empty_point",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope) -> !exec.outcome<(!poly.point<"bls12-381.fr">)>} : ()->()
 "runtime.binding"() {sym_name="append",contract="poly.append_point",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope, !poly.point<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!poly.point<"bls12-381.fr">)>} : ()->()


 "protocol.func"() ({ ^entry(%n:ui64,%T:!t,%U:!t,%TV:!t,%UV:!t,%claim:!f,%coins:!rng):
   %count = protocol.exchange %n {sender="P",receiver="V",site="arity"} : ui64
   %initial = "protocol.local_call"(%n,%T,%U) {callee=@init,role="P",site="initialize"} : (ui64,!t,!t)->!state
   %expected_count = "protocol.local_call"(%TV) {callee=@table_arity,role="V",site="expected_arity"} : (!t)->ui64
   %count_ok = "data.index_equal"(%count,%expected_count) : (ui64,ui64)->i1
   protocol.guard %count_ok {owner="V",site="arity_check"}
   %empty = "protocol.local_call"() {callee=@empty_point,role="V",site="empty_point"} : ()->!p
   %done:3 = "protocol.repeat"(%count,%initial,%empty,%claim,%coins) ({
   ^body(%i:ui64,%state:!state,%point:!p,%current:!f,%random:!rng):
     %coeffs = "protocol.local_call"(%state) {callee=@round,role="P",site="round_coefficients"} : (!state)->!a
     %received = protocol.exchange %coeffs {sender="P",receiver="V",site="round_message"} : !a
     %q = "poly.from_coefficients"(%received) : (!a)->!q
     %zero = "algebra.constant"() {value="0"} : ()->!f
     %one = "algebra.constant"() {value="1"} : ()->!f
     %q0 = "poly.evaluate"(%q,%zero) : (!q,!f)->!f
     %q1 = "poly.evaluate"(%q,%one) : (!q,!f)->!f
     %sum = algebra.field_add %q0,%q1 : (!f,!f)->!f
     %ok = algebra.field_equal %sum,%current : (!f,!f)->i1
     protocol.guard %ok {owner="V",site="boundary"}
     %r = "protocol.query"(%random) {method="draw",owner="V",site="draw"} : (!rng)->!f
     %rP = protocol.exchange %r {sender="V",receiver="P",site="challenge"} : !f
     %next_state = "protocol.local_call"(%state,%rP) {callee=@bind,role="P",site="bind"} : (!state,!f)->!state
     %next_point = "protocol.local_call"(%point,%r) {callee=@append_point,role="V",site="append_point"} : (!p,!f)->!p
     %next_claim = "poly.evaluate"(%q,%r) : (!q,!f)->!f
     "protocol.yield"(%next_state,%next_point,%next_claim) : (!state,!p,!f)->()
   }) {site="rounds",carried=3:i64,maximum=8:i64,roles=["P","V"],carried_roles=[["P"],["V"],["V"]]} : (ui64,!state,!p,!f,!rng)->(!state,!p,!f)
   %finished:2 = "protocol.local_call"(%done#0) {callee=@finish,role="P",site="finish"} : (!state)->(!p,!f)
   %actual = "protocol.local_call"(%done#1,%TV,%UV) {callee=@evaluate,role="V",site="terminal"} : (!p,!t,!t)->!f
   %accepted = algebra.field_equal %actual,%done#2 : (!f,!f)->i1
   "protocol.return"(%accepted,%finished#0,%finished#1) : (i1,!p,!f)->()
 }) {sym_name="sumcheck",function_type=(ui64,!t,!t,!t,!t,!f,!rng)->(i1,!p,!f),roles=["P","V"],input_roles=[["P"],["P"],["P"],["V"],["V"],["V"],["V"]],output_roles=[["V"],["P"],["P"]]} : ()->()

 "runtime.binding"() {sym_name="weights",contract="poly.equality_weights",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope, !poly.point<"bls12-381.fr">) -> !exec.outcome<(!algebra.field_vector<"bls12-381.fr">)>} : ()->()
 "runtime.binding"() {sym_name="table",contract="vector.to_table",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!poly.multilinear<"bls12-381.fr">)>} : ()->()

 "protocol.func"() ({ ^entry(%layers:ui64,%coins:!rng):
   %pP = "protocol.local_call"() {callee=@empty_point,role="P",site="emptyP"} : ()->!p
   %pV = "protocol.local_call"() {callee=@empty_point,role="V",site="emptyV"} : ()->!p
   %yes = arith.constant true
   %done:3 = "protocol.repeat"(%layers,%pP,%pV,%yes,%coins) ({
   ^layer(%i:ui64,%pointP:!p,%pointV:!p,%prior:i1,%rng:!rng):
     %tableP = "protocol.local_call"(%pointP) {callee=@equality_table,role="P",site="tableP"} : (!p)->!t
     %tableV = "protocol.local_call"(%pointV) {callee=@equality_table,role="V",site="tableV"} : (!p)->!t
     %one = "algebra.constant"() {value="1"} : ()->!f
     %out:3 = protocol.apply @sumcheck(%i,%tableP,%tableP,%tableV,%tableV,%one,%rng) {roles=["P","V"],site="reduce"} : (ui64,!t,!t,!t,!t,!f,!rng)->(i1,!p,!f)
     %accepted = arith.andi %prior,%out#0 : i1
     %zero = "algebra.constant"() {value="0"} : ()->!f
     %nextP = "protocol.local_call"(%pointP,%zero) {callee=@append_point,role="P",site="advanceP"} : (!p,!f)->!p
     %nextV = "protocol.local_call"(%pointV,%zero) {callee=@append_point,role="V",site="advanceV"} : (!p,!f)->!p
     "protocol.yield"(%nextP,%nextV,%accepted) : (!p,!p,i1)->()
   }) {site="layers",carried=3:i64,maximum=4:i64,roles=["P","V"],carried_roles=[["P"],["V"],["V"]]} : (ui64,!p,!p,i1,!rng)->(!p,!p,i1)
   "protocol.return"(%done#2) : (i1)->()
 }) {sym_name="main",function_type=(ui64,!rng)->i1,roles=["P","V"],input_roles=[["P","V"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
