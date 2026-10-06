// Direct relation checking discloses the witness. This is a composition client.
!f = !algebra.field<"bn254.fr">
!v = tensor<?x!f>
!m = tensor<?x?x!f>
!ms = !data.sequence<!m>
!p = !poly.univariate<"bn254.fr">
!g = !algebra.group<"bn254.g1">
!gs = tensor<?x!g>
!g2 = !algebra.group<"bn254.g2">
!gt = !algebra.group<"bn254.gt">
module { "protocol.module"() ({
"local.binding"() {sym_name="index_constant",contract="index.constant",arguments=[],implementation=""} : ()->()
"local.binding"() {sym_name="field_constant",contract="field.constant",arguments=["bn254.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="sequence_length_2",contract="sequence.length",arguments=["matrix:bn254.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="index_equal",contract="index.equal",arguments=[],implementation=""} : ()->()
"local.binding"() {sym_name="index_add",contract="index.add",arguments=[],implementation=""} : ()->()
"local.binding"() {sym_name="vector_geometric",contract="vector.geometric",arguments=["bn254.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="vector_get",contract="vector.get",arguments=["bn254.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="field_equal",contract="field.equal",arguments=["bn254.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="bool_not",contract="bool.not",arguments=[],implementation=""} : ()->()
"local.binding"() {sym_name="sequence_at_9",contract="sequence.at",arguments=["matrix:bn254.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="matrix_mul_vector",contract="matrix.mul_vector",arguments=["bn254.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="vector_length",contract="vector.length",arguments=["bn254.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="poly_coset_interpolate",contract="poly.coset_interpolate",arguments=["bn254.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="poly_coset_evaluate",contract="poly.coset_evaluate",arguments=["bn254.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="vector_mul",contract="vector.mul",arguments=["bn254.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="vector_equal",contract="vector.equal",arguments=["bn254.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="vector_sub",contract="vector.sub",arguments=["bn254.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="curve_msm_17",contract="curve.msm",arguments=["bn254.g1"],implementation=""} : ()->()
"local.binding"() {sym_name="vector_slice",contract="vector.slice",arguments=["bn254.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="bool_and",contract="bool.and",arguments=[],implementation=""} : ()->()
relation.declare @relation {kind="external",key="example/qap-data",revision="1",signature=(!ms,!v,!v,!gs,!g2,!f,ui64)->i1,purposes=["parameter","statement","witness","parameter","parameter","parameter","parameter"]}
local.func @numerator(%matrices:!ms,%w:!v,%shift:!f,%n:ui64)->(!v,i1) attributes {logical_origin=["numerator",[]]} {
  %zero = "algebra.exec.index_constant"() {binding=@index_constant,parameters=["0"],site="zero"} : ()->(ui64)
  %one_index = "algebra.exec.index_constant"() {binding=@index_constant,parameters=["1"],site="one_index"} : ()->(ui64)
  %two = "algebra.exec.index_constant"() {binding=@index_constant,parameters=["2"],site="two"} : ()->(ui64)
  %three = "algebra.exec.index_constant"() {binding=@index_constant,parameters=["3"],site="three"} : ()->(ui64)
  %one = "algebra.exec.field_constant"() {binding=@field_constant,parameters=["1"],site="one"} : ()->(!f)
  %count = "data.exec.sequence_length"(%matrices) {binding=@sequence_length_2,parameters=[],site="count"} : (!ms)->(ui64)
  %arity = "algebra.exec.index_equal"(%count,%three) {binding=@index_equal,parameters=[],site="arity"} : (ui64,ui64)->(i1)
  "local.if"(%arity) ({ "local.yield"() : ()->() }, { "local.stop"() {site="matrix_arity_reject",reason="reject"} : ()->() }) {site="matrix_arity"} : (i1)->()
  %nplus = "algebra.exec.index_add"(%n,%one_index) {binding=@index_add,parameters=[],site="nplus"} : (ui64,ui64)->(ui64)
  %powers = "algebra.exec.vector_geometric"(%shift,%nplus) {binding=@vector_geometric,parameters=[],site="powers"} : (!f,ui64)->(!v)
  %shift_power = "algebra.exec.vector_get"(%powers,%n) {binding=@vector_get,parameters=[],site="shift_power"} : (!v,ui64)->(!f)
  %overlap = "algebra.exec.field_equal"(%shift_power,%one) {binding=@field_equal,parameters=[],site="overlap"} : (!f,!f)->(i1)
  %disjoint = "algebra.exec.bool_not"(%overlap) {binding=@bool_not,parameters=[],site="disjoint"} : (i1)->(i1)
  "local.if"(%disjoint) ({ "local.yield"() : ()->() }, { "local.stop"() {site="disjoint_coset_reject",reason="reject"} : ()->() }) {site="disjoint_coset"} : (i1)->()
  %a = "data.exec.sequence_at"(%matrices,%zero) {binding=@sequence_at_9,parameters=[],site="a"} : (!ms,ui64)->(!m)
  %az = "algebra.exec.matrix_mul_vector"(%a,%w) {binding=@matrix_mul_vector,parameters=[],site="az"} : (!m,!v)->(!v)
  %arows = "algebra.exec.vector_length"(%az) {binding=@vector_length,parameters=[],site="arows"} : (!v)->(ui64)
  %ashape = "algebra.exec.index_equal"(%arows,%n) {binding=@index_equal,parameters=[],site="ashape"} : (ui64,ui64)->(i1)
  "local.if"(%ashape) ({ "local.yield"() : ()->() }, { "local.stop"() {site="a_rows_reject",reason="reject"} : ()->() }) {site="a_rows"} : (i1)->()
  %apoly = "poly.exec.coset_interpolate"(%az,%one) {binding=@poly_coset_interpolate,parameters=[],site="apoly"} : (!v,!f)->(!p)
  %acoset = "poly.exec.coset_evaluate"(%apoly,%shift,%n) {binding=@poly_coset_evaluate,parameters=[],site="acoset"} : (!p,!f,ui64)->(!v)
  %b = "data.exec.sequence_at"(%matrices,%one_index) {binding=@sequence_at_9,parameters=[],site="b"} : (!ms,ui64)->(!m)
  %bz = "algebra.exec.matrix_mul_vector"(%b,%w) {binding=@matrix_mul_vector,parameters=[],site="bz"} : (!m,!v)->(!v)
  %brows = "algebra.exec.vector_length"(%bz) {binding=@vector_length,parameters=[],site="brows"} : (!v)->(ui64)
  %bshape = "algebra.exec.index_equal"(%brows,%n) {binding=@index_equal,parameters=[],site="bshape"} : (ui64,ui64)->(i1)
  "local.if"(%bshape) ({ "local.yield"() : ()->() }, { "local.stop"() {site="b_rows_reject",reason="reject"} : ()->() }) {site="b_rows"} : (i1)->()
  %bpoly = "poly.exec.coset_interpolate"(%bz,%one) {binding=@poly_coset_interpolate,parameters=[],site="bpoly"} : (!v,!f)->(!p)
  %bcoset = "poly.exec.coset_evaluate"(%bpoly,%shift,%n) {binding=@poly_coset_evaluate,parameters=[],site="bcoset"} : (!p,!f,ui64)->(!v)
  %c = "data.exec.sequence_at"(%matrices,%two) {binding=@sequence_at_9,parameters=[],site="c"} : (!ms,ui64)->(!m)
  %cz = "algebra.exec.matrix_mul_vector"(%c,%w) {binding=@matrix_mul_vector,parameters=[],site="cz"} : (!m,!v)->(!v)
  %crows = "algebra.exec.vector_length"(%cz) {binding=@vector_length,parameters=[],site="crows"} : (!v)->(ui64)
  %cshape = "algebra.exec.index_equal"(%crows,%n) {binding=@index_equal,parameters=[],site="cshape"} : (ui64,ui64)->(i1)
  "local.if"(%cshape) ({ "local.yield"() : ()->() }, { "local.stop"() {site="c_rows_reject",reason="reject"} : ()->() }) {site="c_rows"} : (i1)->()
  %cpoly = "poly.exec.coset_interpolate"(%cz,%one) {binding=@poly_coset_interpolate,parameters=[],site="cpoly"} : (!v,!f)->(!p)
  %ccoset = "poly.exec.coset_evaluate"(%cpoly,%shift,%n) {binding=@poly_coset_evaluate,parameters=[],site="ccoset"} : (!p,!f,ui64)->(!v)
  %products = "algebra.exec.vector_mul"(%az,%bz) {binding=@vector_mul,parameters=[],site="products"} : (!v,!v)->(!v)
  %valid = "algebra.exec.vector_equal"(%products,%cz) {binding=@vector_equal,parameters=[],site="valid"} : (!v,!v)->(i1)
  %coset_products = "algebra.exec.vector_mul"(%acoset,%bcoset) {binding=@vector_mul,parameters=[],site="coset_products"} : (!v,!v)->(!v)
  %out = "algebra.exec.vector_sub"(%coset_products,%ccoset) {binding=@vector_sub,parameters=[],site="out"} : (!v,!v)->(!v)
  local.return %out,%valid : !v,i1
}
local.func @contract(%values:!v,%query:!gs)->(!g) attributes {logical_origin=["contract",[]]} {
  %point = "algebra.exec.group_msm"(%values,%query) {binding=@curve_msm_17,parameters=[],site="point"} : (!v,!gs)->(!g)
  local.return %point : !g
}
local.func @public_prefix(%w:!v,%public:!v)->(i1) attributes {logical_origin=["public_prefix",[]]} {
  %zero = "algebra.exec.index_constant"() {binding=@index_constant,parameters=["0"],site="zero"} : ()->(ui64)
  %one_index = "algebra.exec.index_constant"() {binding=@index_constant,parameters=["1"],site="one_index"} : ()->(ui64)
  %one = "algebra.exec.field_constant"() {binding=@field_constant,parameters=["1"],site="one"} : ()->(!f)
  %first = "algebra.exec.vector_get"(%w,%zero) {binding=@vector_get,parameters=[],site="first"} : (!v,ui64)->(!f)
  %one_valid = "algebra.exec.field_equal"(%first,%one) {binding=@field_equal,parameters=[],site="one_valid"} : (!f,!f)->(i1)
  %count = "algebra.exec.vector_length"(%public) {binding=@vector_length,parameters=[],site="count"} : (!v)->(ui64)
  %prefix = "algebra.exec.vector_slice"(%w,%one_index,%count) {binding=@vector_slice,parameters=[],site="prefix"} : (!v,ui64,ui64)->(!v)
  %prefix_valid = "algebra.exec.vector_equal"(%prefix,%public) {binding=@vector_equal,parameters=[],site="prefix_valid"} : (!v,!v)->(i1)
  %valid = "algebra.exec.bool_and"(%prefix_valid,%one_valid) {binding=@bool_and,parameters=[],site="valid"} : (i1,i1)->(i1)
  local.return %valid : i1
}
"protocol.func"() ({ ^entry(%matrices:!ms,%public:!v,%w:!v,%query:!gs,%g2:!g2,%shift:!f,%n:ui64):
 protocol.statement @relation(%matrices,%public,%w,%query,%g2,%shift,%n) {selectors=["V","V","P","V","V","V","V"],acceptance=0:i64} : !ms,!v,!v,!gs,!g2,!f,ui64
 %computed:2 = "protocol.local_call"(%matrices,%w,%shift,%n) {callee=@numerator,role="P",site="producer_numerator"} : (!ms,!v,!f,ui64)->(!v,i1)
 %point = "protocol.local_call"(%computed#0,%query) {callee=@contract,role="P",site="producer_msm"} : (!v,!gs)->!g
 %target = algebra.pairing %point,%g2 : (!g,!g2)->!gt
 %received = protocol.exchange %w {sender="P",receiver="V",site="witness"} : !v
 %received_point = protocol.exchange %point {sender="P",receiver="V",site="point"} : !g
 %received_target = protocol.exchange %target {sender="P",receiver="V",site="target"} : !gt
 %checked:2 = "protocol.local_call"(%matrices,%received,%shift,%n) {callee=@numerator,role="V",site="validator_numerator"} : (!ms,!v,!f,ui64)->(!v,i1)
 %expected = "protocol.local_call"(%checked#0,%query) {callee=@contract,role="V",site="validator_msm"} : (!v,!gs)->!g
 %prefix = "protocol.local_call"(%received,%public) {callee=@public_prefix,role="V",site="public_prefix"} : (!v,!v)->i1
 %expected_target = algebra.pairing %expected,%g2 : (!g,!g2)->!gt
 %point_ok = algebra.group_equal %expected,%received_point : (!g,!g)->i1
 %target_ok = algebra.group_equal %expected_target,%received_target : (!gt,!gt)->i1
 %a = arith.andi %point_ok,%target_ok : i1
 %b = arith.andi %prefix,%checked#1 : i1
 %valid = arith.andi %a,%b : i1
 "protocol.return"(%valid) : (i1)->()
}) {sym_name="main",function_type=(!ms,!v,!v,!gs,!g2,!f,ui64)->i1,roles=["P","V"],input_roles=[["P","V"],["V"],["P"],["P","V"],["P","V"],["P","V"],["P","V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
