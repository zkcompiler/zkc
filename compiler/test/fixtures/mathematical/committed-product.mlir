!pk = !commitment.polynomial<"multilinear.kzg.bls12-381/0", "prover_key">
!vk = !commitment.polynomial<"multilinear.kzg.bls12-381/0", "verifier_key">
!c = !commitment.polynomial<"multilinear.kzg.bls12-381/0", "commitment">
!o = !commitment.polynomial<"multilinear.kzg.bls12-381/0", "opening_state">
!proof = !commitment.polynomial<"multilinear.kzg.bls12-381/0", "proof">
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
    func.func @commit(%arg0: !runtime.scope, %arg1: !pk, %arg2: !t) -> !exec.outcome<(!c, !o)> attributes {no_inline, runtime.origin = ["commit", []]} {
      %0 = "exec.apply"(%arg0, %arg1, %arg2) <{binding = @commit_kernel, parameters = [], site = "commit"}> : (!runtime.scope, !pk, !t) -> !exec.outcome<(!c, !o)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!c, !o)>) -> ()
    ^bb1(%1: !c, %2: !o):  // pred: ^bb0
      %3 = "exec.returned"(%1, %2) : (!c, !o) -> !exec.outcome<(!c, !o)>
      return %3 : !exec.outcome<(!c, !o)>
    ^bb2(%4: !exec.stop):  // pred: ^bb0
      %5 = "exec.failed"(%4) : (!exec.stop) -> !exec.outcome<(!c, !o)>
      return %5 : !exec.outcome<(!c, !o)>
    }
    func.func @open(%arg0: !runtime.scope, %arg1: !o, %arg2: !p) -> !exec.outcome<(!f, !proof)> attributes {no_inline, runtime.origin = ["open", []]} {
      %0 = "exec.apply"(%arg0, %arg1, %arg2) <{binding = @open_kernel, parameters = [], site = "open"}> : (!runtime.scope, !o, !p) -> !exec.outcome<(!f, !proof)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(!f, !proof)>) -> ()
    ^bb1(%1: !f, %2: !proof):  // pred: ^bb0
      %3 = "exec.returned"(%1, %2) : (!f, !proof) -> !exec.outcome<(!f, !proof)>
      return %3 : !exec.outcome<(!f, !proof)>
    ^bb2(%4: !exec.stop):  // pred: ^bb0
      %5 = "exec.failed"(%4) : (!exec.stop) -> !exec.outcome<(!f, !proof)>
      return %5 : !exec.outcome<(!f, !proof)>
    }
    func.func @check(%arg0: !runtime.scope, %arg1: !vk, %arg2: !c, %arg3: !p, %arg4: !f, %arg5: !proof) -> !exec.outcome<(i1)> attributes {no_inline, runtime.origin = ["check", []]} {
      %0 = "exec.apply"(%arg0, %arg1, %arg2, %arg3, %arg4, %arg5) <{binding = @check_kernel, parameters = [], site = "check"}> : (!runtime.scope, !vk, !c, !p, !f, !proof) -> !exec.outcome<(i1)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1: i1):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (i1) -> !exec.outcome<(i1)>
      return %2 : !exec.outcome<(i1)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(i1)>
      return %4 : !exec.outcome<(i1)>
    }
    func.func @same_root(%arg0: !runtime.scope, %arg1: !c, %arg2: !c) -> !exec.outcome<(i1)> attributes {no_inline, runtime.origin = ["same_root", []]} {
      %0 = "exec.apply"(%arg0, %arg1, %arg2) <{binding = @equal_kernel, parameters = [], site = "equal"}> : (!runtime.scope, !c, !c) -> !exec.outcome<(i1)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1: i1):  // pred: ^bb0
      %2 = "exec.returned"(%1) : (i1) -> !exec.outcome<(i1)>
      return %2 : !exec.outcome<(i1)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(i1)>
      return %4 : !exec.outcome<(i1)>
    }

 "runtime.binding"() {sym_name="empty",contract="poly.empty_point",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope) -> !exec.outcome<(!poly.point<"bls12-381.fr">)>} : ()->()
 "runtime.binding"() {sym_name="append",contract="poly.append_point",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope, !poly.point<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!poly.point<"bls12-381.fr">)>} : ()->()



 "runtime.binding"() {sym_name="commit_kernel",contract="pcs.commit",arguments=["multilinear.kzg.bls12-381/0"],implementation="",function_type=(!runtime.scope, !commitment.polynomial<"multilinear.kzg.bls12-381/0", "prover_key">, !poly.multilinear<"bls12-381.fr">) -> !exec.outcome<(!commitment.polynomial<"multilinear.kzg.bls12-381/0", "commitment">, !commitment.polynomial<"multilinear.kzg.bls12-381/0", "opening_state">)>} : ()->()
 "runtime.binding"() {sym_name="open_kernel",contract="pcs.open",arguments=["multilinear.kzg.bls12-381/0"],implementation="",function_type=(!runtime.scope, !commitment.polynomial<"multilinear.kzg.bls12-381/0", "opening_state">, !poly.point<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">, !commitment.polynomial<"multilinear.kzg.bls12-381/0", "proof">)>} : ()->()
 "runtime.binding"() {sym_name="check_kernel",contract="pcs.check",arguments=["multilinear.kzg.bls12-381/0"],implementation="",function_type=(!runtime.scope, !commitment.polynomial<"multilinear.kzg.bls12-381/0", "verifier_key">, !commitment.polynomial<"multilinear.kzg.bls12-381/0", "commitment">, !poly.point<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !commitment.polynomial<"multilinear.kzg.bls12-381/0", "proof">) -> !exec.outcome<(i1)>} : ()->()
 "runtime.binding"() {sym_name="equal_kernel",contract="pcs.equal",arguments=["multilinear.kzg.bls12-381/0"],implementation="",function_type=(!runtime.scope, !commitment.polynomial<"multilinear.kzg.bls12-381/0", "commitment">, !commitment.polynomial<"multilinear.kzg.bls12-381/0", "commitment">) -> !exec.outcome<(i1)>} : ()->()




 "protocol.func"() ({ ^entry(%state:!o,%pointP:!p,%pointV:!p,%key:!vk,%root:!c):
   %opened:2 = "protocol.local_call"(%state,%pointP) {callee=@open,role="P",site="open"} : (!o,!p)->(!f,!proof)
   %value = protocol.exchange %opened#0 {sender="P",receiver="V",site="value"} : !f
   %proof = protocol.exchange %opened#1 {sender="P",receiver="V",site="proof"} : !proof
   %valid = "protocol.local_call"(%key,%root,%pointV,%value,%proof) {callee=@check,role="V",site="check"} : (!vk,!c,!p,!f,!proof)->i1
   protocol.guard %valid {owner="V",site="opening_check"}
   "protocol.return"(%value) : (!f)->()
 }) {sym_name="opening",function_type=(!o,!p,!p,!vk,!c)->!f,roles=["P","V"],input_roles=[["P"],["P"],["V"],["V"],["V"]],output_roles=[["V"]]} : ()->()
 "protocol.func"() ({ ^entry(%n:ui64,%T:!t,%U:!t,%claim:!f,%coins:!rng,%pk:!pk,%vk:!vk,%expectedT:!c,%expectedU:!c):
   %committedT:2 = "protocol.local_call"(%pk,%T) {callee=@commit,role="P",site="commit_T"} : (!pk,!t)->(!c,!o)
   %committedU:2 = "protocol.local_call"(%pk,%U) {callee=@commit,role="P",site="commit_U"} : (!pk,!t)->(!c,!o)
   %rootT = protocol.exchange %committedT#0 {sender="P",receiver="V",site="root_T"} : !c
   %rootU = protocol.exchange %committedU#0 {sender="P",receiver="V",site="root_U"} : !c
   %matchesT = "protocol.local_call"(%rootT,%expectedT) {callee=@same_root,role="V",site="expected_T"} : (!c,!c)->i1
   protocol.guard %matchesT {owner="V",site="root_T_check"}
   %matchesU = "protocol.local_call"(%rootU,%expectedU) {callee=@same_root,role="V",site="expected_U"} : (!c,!c)->i1
   protocol.guard %matchesU {owner="V",site="root_U_check"}
   %count = protocol.exchange %n {sender="P",receiver="V",site="arity"} : ui64
   %initial = "protocol.local_call"(%n,%T,%U) {callee=@init,role="P",site="initialize"} : (ui64,!t,!t)->!state
   %count_ok = "data.index_equal"(%count,%n) : (ui64,ui64)->i1
   protocol.guard %count_ok {owner="V",site="arity_check"}
   %empty = "protocol.local_call"() {callee=@empty_point,role="V",site="empty_point"} : ()->!p
   %done:3 = "protocol.repeat"(%count,%initial,%empty,%claim,%coins) ({
   ^body(%i:ui64,%state:!state,%point:!p,%current:!f,%random:!rng):
     %coeffs = "protocol.local_call"(%state) {callee=@round,role="P",site="round_coefficients"} : (!state)->!a
     %received = protocol.exchange %coeffs {sender="P",receiver="V",site="round_message"} : !a
     %q = "poly.from_coefficients"(%received) : (!a)->!q
     %zero = "algebra.constant"() {value=#algebra.literal<!f, 0 : ui255>} : ()->!f
     %one = "algebra.constant"() {value=#algebra.literal<!f, 1 : ui255>} : ()->!f
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
   %valueT = "protocol.apply"(%committedT#1,%finished#0,%done#1,%vk,%expectedT) {callee=@opening,roles=["P","V"],site="open_T"} : (!o,!p,!p,!vk,!c)->!f
   %valueU = "protocol.apply"(%committedU#1,%finished#0,%done#1,%vk,%expectedU) {callee=@opening,roles=["P","V"],site="open_U"} : (!o,!p,!p,!vk,!c)->!f
   %actual = algebra.field_multiply %valueT,%valueU : (!f,!f)->!f
   %accepted = algebra.field_equal %actual,%done#2 : (!f,!f)->i1
   "protocol.return"(%accepted,%finished#0,%finished#1) : (i1,!p,!f)->()
 }) {sym_name="main",function_type=(ui64,!t,!t,!f,!rng,!pk,!vk,!c,!c)->(i1,!p,!f),roles=["P","V"],input_roles=[["P","V"],["P"],["P"],["V"],["V"],["P"],["V"],["V"],["V"]],output_roles=[["V"],["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
