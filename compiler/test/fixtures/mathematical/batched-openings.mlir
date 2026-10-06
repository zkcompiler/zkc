!message = !local.variant<"variant:5b227a6b632e76617269616e742f31222c5b224f70656e696e67222c226e6f6e65222c5b5d2c5b2231222c2232225d2c22736f6d65222c226669656c643a626c7331322d3338312e6672222c2270726f6f663a6d756c74696c696e6561722e6b7a672e626c7331322d3338312f31222c5b2235222c2236225d2c5b2234222c2237225d2c5b2233222c2238225d2c5b2230222c2239225d5d5d">
!pk = !pcs.object<"multilinear.kzg.bls12-381/1", "prover_key">
!vk = !pcs.object<"multilinear.kzg.bls12-381/1", "verifier_key">
!c = !pcs.object<"multilinear.kzg.bls12-381/1", "commitment">
!o = !pcs.object<"multilinear.kzg.bls12-381/1", "opening_state">
!proof = !pcs.object<"multilinear.kzg.bls12-381/1", "proof">
!f = !algebra.field<"bls12-381.fr">
!t = !poly.multilinear<"bls12-381.fr">
!p = !poly.point<"bls12-381.fr">
!batch = !data.sequence<!message>
!fs = tensor<?x!f>
module { "protocol.module"() ({
 "local.binding"() {sym_name="empty",contract="sequence.empty",arguments=["variant:5b227a6b632e76617269616e742f31222c5b224f70656e696e67222c226e6f6e65222c5b5d2c5b2231222c2232225d2c22736f6d65222c226669656c643a626c7331322d3338312e6672222c2270726f6f663a6d756c74696c696e6561722e6b7a672e626c7331322d3338312f31222c5b2235222c2236225d2c5b2234222c2237225d2c5b2233222c2238225d2c5b2230222c2239225d5d5d"],implementation=""} : ()->()
 "local.binding"() {sym_name="append",contract="sequence.append",arguments=["variant:5b227a6b632e76617269616e742f31222c5b224f70656e696e67222c226e6f6e65222c5b5d2c5b2231222c2232225d2c22736f6d65222c226669656c643a626c7331322d3338312e6672222c2270726f6f663a6d756c74696c696e6561722e6b7a672e626c7331322d3338312f31222c5b2235222c2236225d2c5b2234222c2237225d2c5b2233222c2238225d2c5b2230222c2239225d5d5d"],implementation=""} : ()->()
 "local.binding"() {sym_name="length",contract="sequence.length",arguments=["variant:5b227a6b632e76617269616e742f31222c5b224f70656e696e67222c226e6f6e65222c5b5d2c5b2231222c2232225d2c22736f6d65222c226669656c643a626c7331322d3338312e6672222c2270726f6f663a6d756c74696c696e6561722e6b7a672e626c7331322d3338312f31222c5b2235222c2236225d2c5b2234222c2237225d2c5b2233222c2238225d2c5b2230222c2239225d5d5d"],implementation=""} : ()->()
 "local.binding"() {sym_name="at",contract="sequence.at",arguments=["variant:5b227a6b632e76617269616e742f31222c5b224f70656e696e67222c226e6f6e65222c5b5d2c5b2231222c2232225d2c22736f6d65222c226669656c643a626c7331322d3338312e6672222c2270726f6f663a6d756c74696c696e6561722e6b7a672e626c7331322d3338312f31222c5b2235222c2236225d2c5b2234222c2237225d2c5b2233222c2238225d2c5b2230222c2239225d5d5d"],implementation=""} : ()->()
 "local.binding"() {sym_name="constant",contract="index.constant",arguments=[],implementation=""} : ()->()
 "local.binding"() {sym_name="equal",contract="index.equal",arguments=[],implementation=""} : ()->()
 "local.binding"() {sym_name="and",contract="bool.and",arguments=[],implementation=""} : ()->()
 "local.binding"() {sym_name="vlength",contract="vector.length",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="get",contract="vector.get",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="point",contract="poly.empty_point",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="coordinate",contract="poly.append_point",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="commit",contract="pcs.commit",arguments=["multilinear.kzg.bls12-381/1"],implementation=""} : ()->()
 "local.binding"() {sym_name="open",contract="pcs.open",arguments=["multilinear.kzg.bls12-381/1"],implementation=""} : ()->()
 "local.binding"() {sym_name="check",contract="pcs.check",arguments=["multilinear.kzg.bls12-381/1"],implementation=""} : ()->()
 local.func @produce(%table:!t,%key:!pk,%points:!fs)->!batch attributes {logical_origin=["produce",[]]} {
   %state:2 = "pcs.exec.commit"(%key,%table) {binding=@commit,parameters=[],site="commit"} : (!pk,!t)->(!c,!o)
   %empty = "data.exec.sequence_empty"() {binding=@empty,parameters=[],site="empty"} : ()->!batch
   %count = "algebra.exec.vector_length"(%points) {binding=@vlength,parameters=[],site="count"} : (!fs)->ui64
   %zero = "algebra.exec.index_constant"() {binding=@constant,parameters=["0"],site="zero"} : ()->ui64
   %batch = "local.for"(%zero,%count,%empty,%state#1,%points) ({ ^element(%i:ui64,%acc:!batch,%s:!o,%xs:!fs):
     %x = "algebra.exec.vector_get"(%xs,%i) {binding=@get,parameters=[],site="coordinate"} : (!fs,ui64)->!f
     %p0 = "poly.exec.empty_point"() {binding=@point,parameters=[],site="point"} : ()->!p
     %p1 = "poly.exec.append_point"(%p0,%x) {binding=@coordinate,parameters=[],site="point1"} : (!p,!f)->!p
     %opening:2 = "pcs.exec.open"(%s,%p1) {binding=@open,parameters=[],site="opening"} : (!o,!p)->(!f,!proof)
     %record = "local.variant_inject"(%opening#0,%opening#1) {alternative="some",site="record"} : (!f,!proof)->!message
     %next = "data.exec.sequence_append"(%acc,%record) {binding=@append,parameters=[],site="append"} : (!batch,!message)->!batch
     "local.yield"(%next,%s,%xs) : (!batch,!o,!fs)->()
   }) {site="openings"} : (ui64,ui64,!batch,!o,!fs)->!batch
   local.return %batch : !batch
 }
 local.func @validate(%batch:!batch,%key:!vk,%root:!c,%points:!fs)->i1 attributes {logical_origin=["validate",[]]} {
   %count = "algebra.exec.vector_length"(%points) {binding=@vlength,parameters=[],site="expected_count"} : (!fs)->ui64
   %actual = "data.exec.sequence_length"(%batch) {binding=@length,parameters=[],site="actual_count"} : (!batch)->ui64
   %same = "algebra.exec.index_equal"(%count,%actual) {binding=@equal,parameters=[],site="count_matches"} : (ui64,ui64)->i1
   %result = "local.if"(%same,%batch,%key,%root,%points,%count) ({ ^matching(%bs:!batch,%k:!vk,%c:!c,%xs:!fs,%n:ui64):
     %yes = "local.bool_constant"() {value=true,site="yes"} : ()->i1
     %zero = "algebra.exec.index_constant"() {binding=@constant,parameters=["0"],site="zero"} : ()->ui64
     %checked = "local.for"(%zero,%n,%yes,%bs,%k,%c,%xs) ({ ^element(%i:ui64,%ok:i1,%items:!batch,%vk:!vk,%commitment:!c,%coordinates:!fs):
       %item = "data.exec.sequence_at"(%items,%i) {binding=@at,parameters=[],site="item"} : (!batch,ui64)->!message
       %x = "algebra.exec.vector_get"(%coordinates,%i) {binding=@get,parameters=[],site="coordinate"} : (!fs,ui64)->!f
       %p0 = "poly.exec.empty_point"() {binding=@point,parameters=[],site="point"} : ()->!p
       %p1 = "poly.exec.append_point"(%p0,%x) {binding=@coordinate,parameters=[],site="point1"} : (!p,!f)->!p
       %valid = "local.match"(%item,%vk,%commitment,%p1) ({ ^none(%match_key:!vk,%match_root:!c,%match_point:!p):
         %no = "local.bool_constant"() {value=false,site="absent"} : ()->i1
         "local.yield"(%no) : (i1)->()
       }, { ^some(%v:!f,%proof:!proof,%match_key:!vk,%match_root:!c,%match_point:!p):
         %valid = "pcs.exec.check"(%match_key,%match_root,%match_point,%v,%proof) {binding=@check,parameters=[],site="check"} : (!vk,!c,!p,!f,!proof)->i1
         "local.yield"(%valid) : (i1)->()
       }) {alternatives=["none","some"],site="present"} : (!message,!vk,!c,!p)->i1
       %next = "algebra.exec.bool_and"(%ok,%valid) {binding=@and,parameters=[],site="next"} : (i1,i1)->i1
       "local.yield"(%next,%items,%vk,%commitment,%coordinates) : (i1,!batch,!vk,!c,!fs)->()
     }) {site="check_openings"} : (ui64,ui64,i1,!batch,!vk,!c,!fs)->i1
     "local.yield"(%checked) : (i1)->()
   }, { ^mismatch(%bs:!batch,%k:!vk,%c:!c,%xs:!fs,%n:ui64):
     %no = "local.bool_constant"() {value=false,site="count_mismatch"} : ()->i1
     "local.yield"(%no) : (i1)->()
   }) {site="counts"} : (i1,!batch,!vk,!c,!fs,ui64)->i1
   local.return %result : i1
 }
 "protocol.func"() ({ ^entry(%table:!t,%pk:!pk,%vk:!vk,%root:!c,%points:!fs):
   %batch = "protocol.local_call"(%table,%pk,%points) {callee=@produce,role="P",site="produce"} : (!t,!pk,!fs)->!batch
   %received = protocol.exchange %batch {sender="P",receiver="V",site="batch"} : !batch
   %accepted = "protocol.local_call"(%received,%vk,%root,%points) {callee=@validate,role="V",site="validate"} : (!batch,!vk,!c,!fs)->i1
   "protocol.return"(%accepted) : (i1)->()
 }) {sym_name="main",function_type=(!t,!pk,!vk,!c,!fs)->i1,roles=["P","V"],input_roles=[["P"],["P"],["V"],["V"],["P","V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
