!f = !algebra.field<"bls12-381.fr">
!m = tensor<?x?x!f>
!v = tensor<?x!f>
!ms = !data.sequence<!m>
!vs = !data.sequence<!v>
module { "protocol.module"() ({
 "local.binding"() {sym_name="at",contract="sequence.at",arguments=["matrix:bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="vector",contract="sequence.at",arguments=["vector:bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="length",contract="sequence.length",arguments=["matrix:bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="vlength",contract="sequence.length",arguments=["vector:bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="constant",contract="index.constant",arguments=[],implementation=""} : ()->()
 "local.binding"() {sym_name="equal",contract="index.equal",arguments=[],implementation=""} : ()->()
 "local.binding"() {sym_name="and",contract="bool.and",arguments=[],implementation=""} : ()->()
 "local.binding"() {sym_name="zero",contract="field.constant",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="add",contract="field.add",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="bilinear",contract="matrix.bilinear",arguments=["bls12-381.fr"],implementation=""} : ()->()
 local.func @evaluate(%matrices:!ms,%rows:!vs,%columns:!vs)->(!f,i1) attributes {logical_origin=["evaluate",[]]} {
   %n = "data.exec.sequence_length"(%matrices) {binding=@length,parameters=[],site="count"} : (!ms)->ui64
   %nr = "data.exec.sequence_length"(%rows) {binding=@vlength,parameters=[],site="rows"} : (!vs)->ui64
   %nc = "data.exec.sequence_length"(%columns) {binding=@vlength,parameters=[],site="columns"} : (!vs)->ui64
   %r = "algebra.exec.index_equal"(%n,%nr) {binding=@equal,parameters=[],site="rows_match"} : (ui64,ui64)->i1
   %c = "algebra.exec.index_equal"(%n,%nc) {binding=@equal,parameters=[],site="columns_match"} : (ui64,ui64)->i1
   %ok = "algebra.exec.bool_and"(%r,%c) {binding=@and,parameters=[],site="counts"} : (i1,i1)->i1
   %sum = "local.if"(%ok,%n,%matrices,%rows,%columns) ({ ^matching(%count:ui64,%ms:!ms,%rs:!vs,%cs:!vs):
     %start = "algebra.exec.index_constant"() {binding=@constant,parameters=["0"],site="start"} : ()->ui64
     %zero = "algebra.exec.field_constant"() {binding=@zero,parameters=["0"],site="zero"} : ()->!f
     %result = "local.for"(%start,%count,%zero,%ms,%rs,%cs) ({ ^item(%i:ui64,%acc:!f,%loop_matrices:!ms,%loop_rows:!vs,%loop_columns:!vs):
       %loop_m = "data.exec.sequence_at"(%loop_matrices,%i) {binding=@at,parameters=[],site="matrix"} : (!ms,ui64)->!m
       %loop_r = "data.exec.sequence_at"(%loop_rows,%i) {binding=@vector,parameters=[],site="row"} : (!vs,ui64)->!v
       %loop_c = "data.exec.sequence_at"(%loop_columns,%i) {binding=@vector,parameters=[],site="column"} : (!vs,ui64)->!v
       %term = "algebra.exec.matrix_bilinear"(%loop_m,%loop_r,%loop_c) {binding=@bilinear,parameters=[],site="term"} : (!m,!v,!v)->!f
       %next = "algebra.exec.field_add"(%acc,%term) {binding=@add,parameters=[],site="sum"} : (!f,!f)->!f
       "local.yield"(%next,%loop_matrices,%loop_rows,%loop_columns) : (!f,!ms,!vs,!vs)->()
     }) {site="traces"} : (ui64,ui64,!f,!ms,!vs,!vs)->!f
     "local.yield"(%result) : (!f)->()
   }, { ^mismatch(%count:ui64,%ms:!ms,%rs:!vs,%cs:!vs):
     %zero = "algebra.exec.field_constant"() {binding=@zero,parameters=["0"],site="mismatch_zero"} : ()->!f
     "local.yield"(%zero) : (!f)->()
   }) {site="shape"} : (i1,ui64,!ms,!vs,!vs)->!f
   local.return %sum,%ok : !f,i1
 }
 "protocol.func"() ({ ^entry(%matrices:!ms,%rows:!vs,%columns:!vs,%claim:!f):
   %received = protocol.exchange %matrices {sender="P",receiver="V",site="traces"} : !ms
   %result:2 = "protocol.local_call"(%received,%rows,%columns) {callee=@evaluate,role="V",site="evaluate"} : (!ms,!vs,!vs)->(!f,i1)
   %same = algebra.field_equal %result#0,%claim : (!f,!f)->i1
   %accepted = arith.andi %same,%result#1 : i1
   "protocol.return"(%accepted) : (i1)->()
 }) {sym_name="main",function_type=(!ms,!vs,!vs,!f)->i1,roles=["P","V"],input_roles=[["P"],["V"],["V"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
