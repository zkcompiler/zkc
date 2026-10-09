// Direct constraint checking deliberately discloses the witness in the proof.
!f = !algebra.field<"bls12-381.fr">
!v = tensor<?x!f>
!trace = !data.sequence<!v>
!config = !local.variant<"variant:5b227a6b632e76617269616e742f31222c5b226578616d706c652f6169722d646174612f4c696e656172526563757272656e6365222c22636f656666696369656e7473222c226669656c643a626c7331322d3338312e6672222c5b2232222c2232225d2c5b2231222c2233225d2c5b2234225d2c5b2230222c2235225d5d5d">
module { "protocol.module"() ({
"local.binding"() {sym_name="index_constant",contract="index.constant",arguments=[],implementation=""} : ()->()
"local.binding"() {sym_name="sequence_length",contract="sequence.length",arguments=["vector:bls12-381.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="index_less",contract="index.less",arguments=[],implementation=""} : ()->()
"local.binding"() {sym_name="vector_length",contract="vector.length",arguments=["bls12-381.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="index_equal",contract="index.equal",arguments=[],implementation=""} : ()->()
"local.binding"() {sym_name="sequence_at",contract="sequence.at",arguments=["vector:bls12-381.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="vector_get",contract="vector.get",arguments=["bls12-381.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="field_equal",contract="field.equal",arguments=["bls12-381.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="bool_and",contract="bool.and",arguments=[],implementation=""} : ()->()
"local.binding"() {sym_name="field_mul",contract="field.mul",arguments=["bls12-381.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="field_add",contract="field.add",arguments=["bls12-381.fr"],implementation=""} : ()->()
relation.declare @relation {kind="external",key="example/air-data",revision="1",signature=(!config,!v,!trace)->i1,purposes=["parameter","statement","witness"]}
local.func @validate(%configuration:!config,%public:!v,%trace:!trace)->i1 attributes {logical_origin=["validate",[]]} {
%accepted = "local.match"(%configuration,%public,%trace) ({ ^parameters(%alpha:!f,%beta:!f,%inputs:!v,%rows:!trace):
%zero = "algebra.exec.index_constant"() {binding=@index_constant,parameters=["0"],site="zero"} : ()->ui64
%one = "algebra.exec.index_constant"() {binding=@index_constant,parameters=["1"],site="one"} : ()->ui64
%two = "algebra.exec.index_constant"() {binding=@index_constant,parameters=["2"],site="two"} : ()->ui64
%three = "algebra.exec.index_constant"() {binding=@index_constant,parameters=["3"],site="three"} : ()->ui64
%four = "algebra.exec.index_constant"() {binding=@index_constant,parameters=["4"],site="four"} : ()->ui64
%height = "data.exec.sequence_length"(%rows) {binding=@sequence_length,parameters=[],site="height"} : (!trace)->ui64
%nonempty = "algebra.exec.index_less"(%zero,%height) {binding=@index_less,parameters=[],site="nonempty"} : (ui64,ui64)->i1
"local.if"(%nonempty) ({ "local.yield"() : ()->() }, { "local.stop"() {site="trace_nonempty_reject",reason="reject"} : ()->() }) {site="trace_nonempty"} : (i1)->()
%input_count = "algebra.exec.vector_length"(%inputs) {binding=@vector_length,parameters=[],site="input_count"} : (!v)->ui64
%four_inputs = "algebra.exec.index_equal"(%input_count,%four) {binding=@index_equal,parameters=[],site="four_inputs"} : (ui64,ui64)->i1
"local.if"(%four_inputs) ({ "local.yield"() : ()->() }, { "local.stop"() {site="boundary_arity_reject",reason="reject"} : ()->() }) {site="boundary_arity"} : (i1)->()
%first = "data.exec.sequence_at"(%rows,%zero) {binding=@sequence_at,parameters=[],site="first"} : (!trace,ui64)->!v
%first_width = "algebra.exec.vector_length"(%first) {binding=@vector_length,parameters=[],site="first_width"} : (!v)->ui64
%first_shape = "algebra.exec.index_equal"(%first_width,%two) {binding=@index_equal,parameters=[],site="first_shape"} : (ui64,ui64)->i1
"local.if"(%first_shape) ({ "local.yield"() : ()->() }, { "local.stop"() {site="first_row_reject",reason="reject"} : ()->() }) {site="first_row"} : (i1)->()
%initial_x = "algebra.exec.vector_get"(%first,%zero) {binding=@vector_get,parameters=[],site="initial_x"} : (!v,ui64)->!f
%initial_y = "algebra.exec.vector_get"(%first,%one) {binding=@vector_get,parameters=[],site="initial_y"} : (!v,ui64)->!f
%expected_x = "algebra.exec.vector_get"(%inputs,%zero) {binding=@vector_get,parameters=[],site="expected_x"} : (!v,ui64)->!f
%expected_y = "algebra.exec.vector_get"(%inputs,%one) {binding=@vector_get,parameters=[],site="expected_y"} : (!v,ui64)->!f
%start_x = "algebra.exec.field_equal"(%initial_x,%expected_x) {binding=@field_equal,parameters=[],site="start_x"} : (!f,!f)->i1
%start_y = "algebra.exec.field_equal"(%initial_y,%expected_y) {binding=@field_equal,parameters=[],site="start_y"} : (!f,!f)->i1
%start = "algebra.exec.bool_and"(%start_x,%start_y) {binding=@bool_and,parameters=[],site="start"} : (i1,i1)->i1
%result:3 = "local.for"(%one,%height,%start,%initial_x,%initial_y,%rows,%alpha,%beta) ({ ^transition(%row:ui64,%ok:i1,%x:!f,%y:!f,%trace_rows:!trace,%a:!f,%b:!f):
%x_column = "algebra.exec.index_constant"() {binding=@index_constant,parameters=["0"],site="x_column"} : ()->ui64
%y_column = "algebra.exec.index_constant"() {binding=@index_constant,parameters=["1"],site="y_column"} : ()->ui64
%width = "algebra.exec.index_constant"() {binding=@index_constant,parameters=["2"],site="width"} : ()->ui64
%current = "data.exec.sequence_at"(%trace_rows,%row) {binding=@sequence_at,parameters=[],site="current"} : (!trace,ui64)->!v
%current_width = "algebra.exec.vector_length"(%current) {binding=@vector_length,parameters=[],site="current_width"} : (!v)->ui64
%row_shape = "algebra.exec.index_equal"(%current_width,%width) {binding=@index_equal,parameters=[],site="row_shape"} : (ui64,ui64)->i1
"local.if"(%row_shape) ({ "local.yield"() : ()->() }, { "local.stop"() {site="row_width_reject",reason="reject"} : ()->() }) {site="row_width"} : (i1)->()
%next_x = "algebra.exec.vector_get"(%current,%x_column) {binding=@vector_get,parameters=[],site="next_x"} : (!v,ui64)->!f
%next_y = "algebra.exec.vector_get"(%current,%y_column) {binding=@vector_get,parameters=[],site="next_y"} : (!v,ui64)->!f
%ax = "algebra.exec.field_multiply"(%a,%x) {binding=@field_mul,parameters=[],site="ax"} : (!f,!f)->!f
%by = "algebra.exec.field_multiply"(%b,%y) {binding=@field_mul,parameters=[],site="by"} : (!f,!f)->!f
%recurrence = "algebra.exec.field_add"(%ax,%by) {binding=@field_add,parameters=[],site="recurrence"} : (!f,!f)->!f
%x_ok = "algebra.exec.field_equal"(%next_x,%y) {binding=@field_equal,parameters=[],site="x_ok"} : (!f,!f)->i1
%y_ok = "algebra.exec.field_equal"(%next_y,%recurrence) {binding=@field_equal,parameters=[],site="y_ok"} : (!f,!f)->i1
%step_ok = "algebra.exec.bool_and"(%x_ok,%y_ok) {binding=@bool_and,parameters=[],site="step_ok"} : (i1,i1)->i1
%next_ok = "algebra.exec.bool_and"(%ok,%step_ok) {binding=@bool_and,parameters=[],site="next_ok"} : (i1,i1)->i1
"local.yield"(%next_ok,%next_x,%next_y,%trace_rows,%a,%b) : (i1,!f,!f,!trace,!f,!f)->()
}) {site="transitions"} : (ui64,ui64,i1,!f,!f,!trace,!f,!f)->(i1,!f,!f)
%final_x = "algebra.exec.vector_get"(%inputs,%two) {binding=@vector_get,parameters=[],site="final_x"} : (!v,ui64)->!f
%final_y = "algebra.exec.vector_get"(%inputs,%three) {binding=@vector_get,parameters=[],site="final_y"} : (!v,ui64)->!f
%end_x = "algebra.exec.field_equal"(%result#1,%final_x) {binding=@field_equal,parameters=[],site="end_x"} : (!f,!f)->i1
%end_y = "algebra.exec.field_equal"(%result#2,%final_y) {binding=@field_equal,parameters=[],site="end_y"} : (!f,!f)->i1
%end = "algebra.exec.bool_and"(%end_x,%end_y) {binding=@bool_and,parameters=[],site="end"} : (i1,i1)->i1
%valid = "algebra.exec.bool_and"(%result#0,%end) {binding=@bool_and,parameters=[],site="valid"} : (i1,i1)->i1
"local.yield"(%valid) : (i1)->()
}) {alternatives=["coefficients"],site="configuration"} : (!config,!v,!trace)->i1
local.return %accepted : i1
}
"protocol.func"() ({ ^entry(%configuration:!config,%public:!v,%witness:!trace):
 protocol.statement @relation(%configuration,%public,%witness) {selectors=["V","V","P"],acceptance=1 : i64} : !config,!v,!trace
 %received = protocol.exchange %witness {sender="P",receiver="V",site="witness"} : !trace
 %accepted = "protocol.local_call"(%configuration,%public,%received) {callee=@validate,role="V",site="validate"} : (!config,!v,!trace)->i1
 %unused = arith.constant false
 "protocol.return"(%unused,%accepted) : (i1,i1)->()
}) {sym_name="main",function_type=(!config,!v,!trace)->(i1,i1),roles=["P","V"],input_roles=[["V"],["V"],["P"]],output_roles=[["V"],["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
