// Direct constraint checking deliberately discloses the witness in the proof.
!f = !algebra.field<"bls12-381.fr">
!v = tensor<?x!f>
!m = tensor<?x?x!f>
!ms = !data.sequence<!m>
module { "protocol.module"() ({
"local.binding"() {sym_name="index_constant",contract="index.constant",arguments=[],implementation=""} : ()->()
"local.binding"() {sym_name="sequence_length",contract="sequence.length",arguments=["matrix:bls12-381.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="index_equal",contract="index.equal",arguments=[],implementation=""} : ()->()
"local.binding"() {sym_name="vector_length",contract="vector.length",arguments=["bls12-381.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="index_less",contract="index.less",arguments=[],implementation=""} : ()->()
"local.binding"() {sym_name="sequence_at",contract="sequence.at",arguments=["matrix:bls12-381.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="matrix_dimension",contract="matrix.dimension",arguments=["bls12-381.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="matrix_mul_vector",contract="matrix.mul_vector",arguments=["bls12-381.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="field_constant",contract="field.constant",arguments=["bls12-381.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="vector_get",contract="vector.get",arguments=["bls12-381.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="field_equal",contract="field.equal",arguments=["bls12-381.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="index_add",contract="index.add",arguments=[],implementation=""} : ()->()
"local.binding"() {sym_name="bool_and",contract="bool.and",arguments=[],implementation=""} : ()->()
"local.binding"() {sym_name="vector_mul",contract="vector.mul",arguments=["bls12-381.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="vector_equal",contract="vector.equal",arguments=["bls12-381.fr"],implementation=""} : ()->()
relation.declare @relation {kind="external",key="example/r1cs-data",revision="1",signature=(!ms,!v,!v)->i1,purposes=["parameter","statement","witness"]}
local.func @validate(%matrices:!ms,%public:!v,%assignment:!v)->i1 attributes {logical_origin=["validate",[]]} {
%zero = "algebra.exec.index_constant"() {binding=@index_constant,parameters=["0"],site="zero"} : ()->ui64
%one_index = "algebra.exec.index_constant"() {binding=@index_constant,parameters=["1"],site="one_index"} : ()->ui64
%two = "algebra.exec.index_constant"() {binding=@index_constant,parameters=["2"],site="two"} : ()->ui64
%three = "algebra.exec.index_constant"() {binding=@index_constant,parameters=["3"],site="three"} : ()->ui64
%matrix_count = "data.exec.sequence_length"(%matrices) {binding=@sequence_length,parameters=[],site="matrix_count"} : (!ms)->ui64
%three_matrices = "algebra.exec.index_equal"(%matrix_count,%three) {binding=@index_equal,parameters=[],site="three_matrices"} : (ui64,ui64)->i1
"local.if"(%three_matrices) ({ "local.yield"() : ()->() }, { "local.stop"() {site="matrix_arity_reject",reason="reject"} : ()->() }) {site="matrix_arity"} : (i1)->()
%assignment_count = "algebra.exec.vector_length"(%assignment) {binding=@vector_length,parameters=[],site="assignment_count"} : (!v)->ui64
%public_count = "algebra.exec.vector_length"(%public) {binding=@vector_length,parameters=[],site="public_count"} : (!v)->ui64
%prefix_fits = "algebra.exec.index_less"(%public_count,%assignment_count) {binding=@index_less,parameters=[],site="prefix_fits"} : (ui64,ui64)->i1
"local.if"(%prefix_fits) ({ "local.yield"() : ()->() }, { "local.stop"() {site="assignment_prefix_reject",reason="reject"} : ()->() }) {site="assignment_prefix"} : (i1)->()
%a = "data.exec.sequence_at"(%matrices,%zero) {binding=@sequence_at,parameters=[],site="a"} : (!ms,ui64)->!m
%acols = "algebra.exec.matrix_dimension"(%a) {binding=@matrix_dimension,parameters=["1"],site="acols"} : (!m)->ui64
%awidth = "algebra.exec.index_equal"(%acols,%assignment_count) {binding=@index_equal,parameters=[],site="awidth"} : (ui64,ui64)->i1
"local.if"(%awidth) ({ "local.yield"() : ()->() }, { "local.stop"() {site="acolumns_reject",reason="reject"} : ()->() }) {site="acolumns"} : (i1)->()
%az = "algebra.exec.matrix_mul_vector"(%a,%assignment) {binding=@matrix_mul_vector,parameters=[],site="az"} : (!m,!v)->!v
%arows = "algebra.exec.vector_length"(%az) {binding=@vector_length,parameters=[],site="arows"} : (!v)->ui64
%b = "data.exec.sequence_at"(%matrices,%one_index) {binding=@sequence_at,parameters=[],site="b"} : (!ms,ui64)->!m
%bcols = "algebra.exec.matrix_dimension"(%b) {binding=@matrix_dimension,parameters=["1"],site="bcols"} : (!m)->ui64
%bwidth = "algebra.exec.index_equal"(%bcols,%assignment_count) {binding=@index_equal,parameters=[],site="bwidth"} : (ui64,ui64)->i1
"local.if"(%bwidth) ({ "local.yield"() : ()->() }, { "local.stop"() {site="bcolumns_reject",reason="reject"} : ()->() }) {site="bcolumns"} : (i1)->()
%bz = "algebra.exec.matrix_mul_vector"(%b,%assignment) {binding=@matrix_mul_vector,parameters=[],site="bz"} : (!m,!v)->!v
%brows = "algebra.exec.vector_length"(%bz) {binding=@vector_length,parameters=[],site="brows"} : (!v)->ui64
%c = "data.exec.sequence_at"(%matrices,%two) {binding=@sequence_at,parameters=[],site="c"} : (!ms,ui64)->!m
%ccols = "algebra.exec.matrix_dimension"(%c) {binding=@matrix_dimension,parameters=["1"],site="ccols"} : (!m)->ui64
%cwidth = "algebra.exec.index_equal"(%ccols,%assignment_count) {binding=@index_equal,parameters=[],site="cwidth"} : (ui64,ui64)->i1
"local.if"(%cwidth) ({ "local.yield"() : ()->() }, { "local.stop"() {site="ccolumns_reject",reason="reject"} : ()->() }) {site="ccolumns"} : (i1)->()
%cz = "algebra.exec.matrix_mul_vector"(%c,%assignment) {binding=@matrix_mul_vector,parameters=[],site="cz"} : (!m,!v)->!v
%crows = "algebra.exec.vector_length"(%cz) {binding=@vector_length,parameters=[],site="crows"} : (!v)->ui64
%bsize = "algebra.exec.index_equal"(%arows,%brows) {binding=@index_equal,parameters=[],site="bsize"} : (ui64,ui64)->i1
"local.if"(%bsize) ({ "local.yield"() : ()->() }, { "local.stop"() {site="bshape_reject",reason="reject"} : ()->() }) {site="bshape"} : (i1)->()
%csize = "algebra.exec.index_equal"(%arows,%crows) {binding=@index_equal,parameters=[],site="csize"} : (ui64,ui64)->i1
"local.if"(%csize) ({ "local.yield"() : ()->() }, { "local.stop"() {site="cshape_reject",reason="reject"} : ()->() }) {site="cshape"} : (i1)->()
%one = "algebra.exec.field_constant"() {binding=@field_constant,parameters=["1"],site="one"} : ()->!f
%assignment_one = "algebra.exec.vector_get"(%assignment,%zero) {binding=@vector_get,parameters=[],site="assignment_one"} : (!v,ui64)->!f
%one_valid = "algebra.exec.field_equal"(%one,%assignment_one) {binding=@field_equal,parameters=[],site="one_valid"} : (!f,!f)->i1
%public_valid = "local.for"(%zero,%public_count,%one_valid,%public,%assignment) ({ ^prefix(%j:ui64,%ok:i1,%inputs:!v,%z:!v):
%offset = "algebra.exec.index_constant"() {binding=@index_constant,parameters=["1"],site="offset"} : ()->ui64
%column = "algebra.exec.index_add"(%j,%offset) {binding=@index_add,parameters=[],site="column"} : (ui64,ui64)->ui64
%expected = "algebra.exec.vector_get"(%inputs,%j) {binding=@vector_get,parameters=[],site="expected"} : (!v,ui64)->!f
%actual = "algebra.exec.vector_get"(%z,%column) {binding=@vector_get,parameters=[],site="actual"} : (!v,ui64)->!f
%equal = "algebra.exec.field_equal"(%expected,%actual) {binding=@field_equal,parameters=[],site="equal"} : (!f,!f)->i1
%prefix_ok = "algebra.exec.bool_and"(%ok,%equal) {binding=@bool_and,parameters=[],site="prefix_ok"} : (i1,i1)->i1
"local.yield"(%prefix_ok,%inputs,%z) : (i1,!v,!v)->()
}) {site="public_prefix"} : (ui64,ui64,i1,!v,!v)->i1
%products = "algebra.exec.vector_mul"(%az,%bz) {binding=@vector_mul,parameters=[],site="products"} : (!v,!v)->!v
%rows_valid = "algebra.exec.vector_equal"(%products,%cz) {binding=@vector_equal,parameters=[],site="rows_valid"} : (!v,!v)->i1
%accepted = "algebra.exec.bool_and"(%public_valid,%rows_valid) {binding=@bool_and,parameters=[],site="accepted"} : (i1,i1)->i1
local.return %accepted : i1
}
"protocol.func"() ({ ^entry(%configuration:!ms,%public:!v,%witness:!v):
 protocol.statement @relation(%configuration,%public,%witness) {selectors=["V","V","P"],acceptance=1 : i64} : !ms,!v,!v
 %received = protocol.exchange %witness {sender="P",receiver="V",site="witness"} : !v
 %accepted = "protocol.local_call"(%configuration,%public,%received) {callee=@validate,role="V",site="validate"} : (!ms,!v,!v)->i1
 %unused = arith.constant false
 "protocol.return"(%unused,%accepted) : (i1,i1)->()
}) {sym_name="main",function_type=(!ms,!v,!v)->(i1,i1),roles=["P","V"],input_roles=[["V"],["V"],["P"]],output_roles=[["V"],["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
