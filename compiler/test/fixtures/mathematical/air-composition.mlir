// A full-trace transition check, extension LDE, opening quotient, fold and Merkle opening.
// This demonstrates composition, not a complete succinct AIR/FRI proof system.
!b = !algebra.field<"koala-bear">
!bv = tensor<?x!b>
!e = !algebra.field<"koala-bear.ext8-binomial3">
!ev = tensor<?x!e>
!poly = !poly.univariate<"koala-bear.ext8-binomial3">
!root = !oracle.object<"rows.merkle-keccak256.koala-bear.ext8-binomial3/0","commitment">
!path = !oracle.object<"rows.merkle-keccak256.koala-bear.ext8-binomial3/0","proof">
!state = !oracle.object<"rows.merkle-keccak256.koala-bear.ext8-binomial3/0","opening_state">
!rng = !protocol.service_ref<"random.koala-bear.ext8-binomial3/0">
module { "protocol.module"() ({
"local.binding"() {sym_name="index_constant",contract="index.constant",arguments=[],implementation=""} : ()->()
"local.binding"() {sym_name="field_constant",contract="field.constant",arguments=["koala-bear.ext8-binomial3"],implementation=""} : ()->()
"local.binding"() {sym_name="base_vector_length",contract="vector.length",arguments=["koala-bear"],implementation=""} : ()->()
"local.binding"() {sym_name="index_equal",contract="index.equal",arguments=[],implementation=""} : ()->()
"local.binding"() {sym_name="vector_embed",contract="vector.embed",arguments=["koala-bear.ext8-binomial3"],implementation=""} : ()->()
"local.binding"() {sym_name="poly_coset_interpolate",contract="poly.coset_interpolate",arguments=["koala-bear.ext8-binomial3"],implementation=""} : ()->()
"local.binding"() {sym_name="index_mul",contract="index.mul",arguments=[],implementation=""} : ()->()
"local.binding"() {sym_name="poly_coset_evaluate",contract="poly.coset_evaluate",arguments=["koala-bear.ext8-binomial3"],implementation=""} : ()->()
"local.binding"() {sym_name="poly_univariate_evaluate",contract="poly.univariate_evaluate",arguments=["koala-bear.ext8-binomial3"],implementation=""} : ()->()
"local.binding"() {sym_name="poly_opening_quotient",contract="poly.opening_quotient",arguments=["koala-bear.ext8-binomial3"],implementation=""} : ()->()
"local.binding"() {sym_name="poly_even_odd_fold",contract="poly.even_odd_fold",arguments=["koala-bear.ext8-binomial3"],implementation=""} : ()->()
"local.binding"() {sym_name="index_sub",contract="index.sub",arguments=[],implementation=""} : ()->()
"local.binding"() {sym_name="base_vector_get",contract="vector.get",arguments=["koala-bear"],implementation=""} : ()->()
"local.binding"() {sym_name="base_field_equal",contract="field.equal",arguments=["koala-bear"],implementation=""} : ()->()
"local.binding"() {sym_name="base_vector_slice",contract="vector.slice",arguments=["koala-bear"],implementation=""} : ()->()
"local.binding"() {sym_name="base_vector_fill",contract="vector.fill",arguments=["koala-bear"],implementation=""} : ()->()
"local.binding"() {sym_name="base_vector_add",contract="vector.add",arguments=["koala-bear"],implementation=""} : ()->()
"local.binding"() {sym_name="base_vector_equal",contract="vector.equal",arguments=["koala-bear"],implementation=""} : ()->()
"local.binding"() {sym_name="bool_and",contract="bool.and",arguments=[],implementation=""} : ()->()
"local.binding"() {sym_name="oracle_commit",contract="oracle.commit",arguments=["rows.merkle-keccak256.koala-bear.ext8-binomial3/0"],implementation=""} : ()->()
"local.binding"() {sym_name="oracle_open",contract="oracle.open",arguments=["rows.merkle-keccak256.koala-bear.ext8-binomial3/0"],implementation=""} : ()->()
"local.binding"() {sym_name="vector_slice",contract="vector.slice",arguments=["koala-bear.ext8-binomial3"],implementation=""} : ()->()
"local.binding"() {sym_name="vector_equal",contract="vector.equal",arguments=["koala-bear.ext8-binomial3"],implementation=""} : ()->()
"local.binding"() {sym_name="oracle_check",contract="oracle.check",arguments=["rows.merkle-keccak256.koala-bear.ext8-binomial3/0"],implementation=""} : ()->()

local.func @fold(%trace:!bv,%shift:!e,%challenge:!e,%n:ui64)->(!ev) attributes {logical_origin=["fold",[]]} {
  %two = "algebra.exec.index_constant"() {binding=@index_constant,parameters=["2"],site="two"} : ()->(ui64)
  %one = "algebra.exec.field_constant"() {binding=@field_constant,parameters=["1"],site="one"} : ()->(!e)
  %zero = "algebra.exec.field_constant"() {binding=@field_constant,parameters=["0"],site="zero"} : ()->(!e)
  %size = "algebra.exec.vector_length"(%trace) {binding=@base_vector_length,parameters=[],site="size"} : (!bv)->(ui64)
  %shape = "algebra.exec.index_equal"(%size,%n) {binding=@index_equal,parameters=[],site="shape"} : (ui64,ui64)->(i1)
  "local.if"(%shape) ({ "local.yield"() : ()->() }, { "local.stop"() {site="trace_shape_reject",reason="reject"} : ()->() }) {site="trace_shape"} : (i1)->()
  %embedded = "algebra.exec.vector_embed"(%trace) {binding=@vector_embed,parameters=[],site="embedded"} : (!bv)->(!ev)
  %polynomial = "poly.exec.coset_interpolate"(%embedded,%one) {binding=@poly_coset_interpolate,parameters=[],site="polynomial"} : (!ev,!e)->(!poly)
  %lde_size = "algebra.exec.index_mul"(%n,%two) {binding=@index_mul,parameters=[],site="lde_size"} : (ui64,ui64)->(ui64)
  %lde = "poly.exec.coset_evaluate"(%polynomial,%shift,%lde_size) {binding=@poly_coset_evaluate,parameters=[],site="lde"} : (!poly,!e,ui64)->(!ev)
  %at_zero = "poly.exec.univariate_evaluate"(%polynomial,%zero) {binding=@poly_univariate_evaluate,parameters=[],site="at_zero"} : (!poly,!e)->(!e)
  %quotient = "poly.exec.opening_quotient"(%lde,%shift,%zero,%at_zero) {binding=@poly_opening_quotient,parameters=[],site="quotient"} : (!ev,!e,!e,!e)->(!ev)
  %folded = "poly.exec.even_odd_fold"(%quotient,%shift,%challenge) {binding=@poly_even_odd_fold,parameters=[],site="folded"} : (!ev,!e,!e)->(!ev)
  local.return %folded : !ev
}
local.func @transitions(%trace:!bv,%start:!b,%step:!b,%n:ui64)->(i1) attributes {logical_origin=["transitions",[]]} {
  %zero = "algebra.exec.index_constant"() {binding=@index_constant,parameters=["0"],site="zero"} : ()->(ui64)
  %one = "algebra.exec.index_constant"() {binding=@index_constant,parameters=["1"],site="one"} : ()->(ui64)
  %length = "algebra.exec.vector_length"(%trace) {binding=@base_vector_length,parameters=[],site="length"} : (!bv)->(ui64)
  %shape = "algebra.exec.index_equal"(%length,%n) {binding=@index_equal,parameters=[],site="shape"} : (ui64,ui64)->(i1)
  "local.if"(%shape) ({ "local.yield"() : ()->() }, { "local.stop"() {site="trace_shape_reject",reason="reject"} : ()->() }) {site="trace_shape"} : (i1)->()
  %count = "algebra.exec.index_sub"(%n,%one) {binding=@index_sub,parameters=[],site="count"} : (ui64,ui64)->(ui64)
  %first = "algebra.exec.vector_get"(%trace,%zero) {binding=@base_vector_get,parameters=[],site="first"} : (!bv,ui64)->(!b)
  %first_valid = "algebra.exec.field_equal"(%first,%start) {binding=@base_field_equal,parameters=[],site="first_valid"} : (!b,!b)->(i1)
  %left = "algebra.exec.vector_slice"(%trace,%zero,%count) {binding=@base_vector_slice,parameters=[],site="left"} : (!bv,ui64,ui64)->(!bv)
  %right = "algebra.exec.vector_slice"(%trace,%one,%count) {binding=@base_vector_slice,parameters=[],site="right"} : (!bv,ui64,ui64)->(!bv)
  %steps = "algebra.exec.vector_fill"(%step,%count) {binding=@base_vector_fill,parameters=[],site="steps"} : (!b,ui64)->(!bv)
  %expected = "algebra.exec.vector_add"(%left,%steps) {binding=@base_vector_add,parameters=[],site="expected"} : (!bv,!bv)->(!bv)
  %rows_valid = "algebra.exec.vector_equal"(%expected,%right) {binding=@base_vector_equal,parameters=[],site="rows_valid"} : (!bv,!bv)->(i1)
  %valid = "algebra.exec.bool_and"(%first_valid,%rows_valid) {binding=@bool_and,parameters=[],site="valid"} : (i1,i1)->(i1)
  local.return %valid : i1
}
local.func @open_fold(%values:!ev,%query:ui64)->(!root,!ev,!path) attributes {logical_origin=["open_fold",[]]} {
  %columns = "algebra.exec.index_constant"() {binding=@index_constant,parameters=["1"],site="columns"} : ()->(ui64)
  %tree:2 = "oracle.exec.commit"(%values,%columns) {binding=@oracle_commit,parameters=[],site="tree"} : (!ev,ui64)->(!root,!state)
  %opening:2 = "oracle.exec.open"(%tree#1,%query) {binding=@oracle_open,parameters=[],site="opening"} : (!state,ui64)->(!ev,!path)
  local.return %tree#0,%opening#0,%opening#1 : !root,!ev,!path
}
local.func @check_opening(%values:!ev,%root:!root,%row:!ev,%path:!path,%query:ui64,%n:ui64)->(i1) attributes {logical_origin=["check_opening",[]]} {
  %one = "algebra.exec.index_constant"() {binding=@index_constant,parameters=["1"],site="one"} : ()->(ui64)
  %expected = "algebra.exec.vector_slice"(%values,%query,%one) {binding=@vector_slice,parameters=[],site="expected"} : (!ev,ui64,ui64)->(!ev)
  %row_valid = "algebra.exec.vector_equal"(%expected,%row) {binding=@vector_equal,parameters=[],site="row_valid"} : (!ev,!ev)->(i1)
  %path_valid = "oracle.exec.check"(%root,%one,%n,%query,%row,%path) {binding=@oracle_check,parameters=[],site="path_valid"} : (!root,ui64,ui64,ui64,!ev,!path)->(i1)
  %valid = "algebra.exec.bool_and"(%row_valid,%path_valid) {binding=@bool_and,parameters=[],site="valid"} : (i1,i1)->(i1)
  local.return %valid : i1
}
"protocol.func"() ({ ^entry(%trace:!bv,%start:!b,%step:!b,%shift:!e,%n:ui64,%query:ui64,%random:!rng):
 %received = protocol.exchange %trace {sender="P",receiver="V",site="trace"} : !bv
 %q = "protocol.query"(%random) {owner="V",method="draw",site="draw"} : (!rng)->!e
 %challenge = protocol.exchange %q {sender="V",receiver="P",site="challenge"} : !e
 %echo = protocol.exchange %challenge {sender="P",receiver="V",site="challenge_echo"} : !e
 %folded = "protocol.local_call"(%trace,%shift,%challenge,%n) {callee=@fold,role="P",site="producer_fold"} : (!bv,!e,!e,ui64)->!ev
 %opened:3 = "protocol.local_call"(%folded,%query) {callee=@open_fold,role="P",site="open"} : (!ev,ui64)->(!root,!ev,!path)
 %root = protocol.exchange %opened#0 {sender="P",receiver="V",site="root"} : !root
 %row = protocol.exchange %opened#1 {sender="P",receiver="V",site="row"} : !ev
 %path = protocol.exchange %opened#2 {sender="P",receiver="V",site="path"} : !path
 %expected = "protocol.local_call"(%received,%shift,%q,%n) {callee=@fold,role="V",site="validator_fold"} : (!bv,!e,!e,ui64)->!ev
 %trace_ok = "protocol.local_call"(%received,%start,%step,%n) {callee=@transitions,role="V",site="transitions"} : (!bv,!b,!b,ui64)->i1
 %opening_ok = "protocol.local_call"(%expected,%root,%row,%path,%query,%n) {callee=@check_opening,role="V",site="opening"} : (!ev,!root,!ev,!path,ui64,ui64)->i1
 %echo_ok = algebra.field_equal %echo,%q : (!e,!e)->i1
 %checks = arith.andi %trace_ok,%opening_ok : i1
 %valid = arith.andi %checks,%echo_ok : i1
 "protocol.return"(%valid) : (i1)->()
}) {sym_name="main",function_type=(!bv,!b,!b,!e,ui64,ui64,!rng)->i1,roles=["P","V"],input_roles=[["P"],["V"],["V"],["P","V"],["P","V"],["P","V"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
