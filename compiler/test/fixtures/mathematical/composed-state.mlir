// Executable algebraic clients; see docs/compiler/mathematics.md.
!f = !algebra.field<"bls12-381.fr">
!g = !algebra.group<"bls12-381.g1">
!fs = tensor<?x!f>
!gs = tensor<?x!g>
!r = !local.capability<"rng:bls12-381.fr">
!s = !protocol.service_ref<"random.bls12-381.fr/0">
module { "protocol.module"() ({
  "local.binding"() {sym_name="random_draw",contract="random.draw",arguments=["bls12-381.fr"],implementation=""} : ()->()
  "local.binding"() {sym_name="field_constant",contract="field.constant",arguments=["bls12-381.fr"],implementation=""} : ()->()
  "local.binding"() {sym_name="field_equal",contract="field.equal",arguments=["bls12-381.fr"],implementation=""} : ()->()
  "local.binding"() {sym_name="field_inverse",contract="field.inverse",arguments=["bls12-381.fr"],implementation=""} : ()->()
  "local.binding"() {sym_name="bool_not",contract="bool.not",arguments=[],implementation=""} : ()->()
  "local.binding"() {sym_name="vector_scale",contract="vector.scale",arguments=["bls12-381.fr"],implementation=""} : ()->()
  "local.binding"() {sym_name="curve_msm",contract="curve.msm",arguments=["bls12-381.g1"],implementation=""} : ()->()
  "local.binding"() {sym_name="curve_append",contract="curve.append",arguments=["bls12-381.g1"],implementation=""} : ()->()
  "local.binding"() {sym_name="vector_append",contract="vector.append",arguments=["bls12-381.fr"],implementation=""} : ()->()
  "local.binding"() {sym_name="curve_get",contract="curve.get",arguments=["bls12-381.g1"],implementation=""} : ()->()
  "local.binding"() {sym_name="vector_get",contract="vector.get",arguments=["bls12-381.fr"],implementation=""} : ()->()
  "local.binding"() {sym_name="curve_empty",contract="curve.empty",arguments=["bls12-381.g1"],implementation=""} : ()->()
  "local.binding"() {sym_name="vector_empty",contract="vector.empty",arguments=["bls12-381.fr"],implementation=""} : ()->()
  "local.binding"() {sym_name="vector_split",contract="vector.split",arguments=["bls12-381.fr"],implementation=""} : ()->()
  "local.binding"() {sym_name="curve_split",contract="curve.split",arguments=["bls12-381.g1"],implementation=""} : ()->()
  "local.binding"() {sym_name="vector_add",contract="vector.add",arguments=["bls12-381.fr"],implementation=""} : ()->()
  "local.binding"() {sym_name="curve_vector_scale",contract="curve.vector_scale",arguments=["bls12-381.g1"],implementation=""} : ()->()
  "local.binding"() {sym_name="curve_vector_add",contract="curve.vector_add",arguments=["bls12-381.g1"],implementation=""} : ()->()
  "local.binding"() {sym_name="curve_length",contract="curve.length",arguments=["bls12-381.g1"],implementation=""} : ()->()
  "local.binding"() {sym_name="index_equal",contract="index.equal",arguments=[],implementation=""} : ()->()
  "local.binding"() {sym_name="index_constant",contract="index.constant",arguments=[],implementation=""} : ()->()
  "local.binding"() {sym_name="curve_equal",contract="curve.equal",arguments=["bls12-381.g1"],implementation=""} : ()->()
  "local.binding"() {sym_name="bool_and",contract="bool.and",arguments=[],implementation=""} : ()->()
  local.func @draw(%r:!r)->(!f,!r) attributes {logical_origin=["draw",[]]} {
    %s:2 = "crypto.exec.random_draw"(%r) {binding=@random_draw,parameters=[],site="s"} : (!r)->(!f,!r)
    local.return %s#0,%s#1 : !f,!r
  }
  local.func @inverse(%x:!f)->(!f,i1) attributes {logical_origin=["inverse",[]]} {
    %zero = "algebra.exec.field_constant"() {binding=@field_constant,parameters=["0"],site="zero"} : ()->(!f)
    %empty = "algebra.exec.field_equal"(%x,%zero) {binding=@field_equal,parameters=[],site="empty"} : (!f,!f)->(i1)

    %result = "local.if"(%empty,%x) ({ ^bad(%v:!f):
      "local.yield"(%v) : (!f)->()
    }, { ^good(%v:!f):
    %inv = "algebra.exec.field_inverse"(%v) {binding=@field_inverse,parameters=[],site="inv"} : (!f)->(!f)
      "local.yield"(%inv) : (!f)->()
    }) {site="partial_inverse"} : (i1,!f)->!f
    %ok = "algebra.exec.bool_not"(%empty) {binding=@bool_not,parameters=[],site="ok"} : (i1)->(i1)
    local.return %result,%ok : !f,i1
  }
  local.func @scale_vector(%a:!fs,%x:!f)->(!fs) attributes {logical_origin=["scale_vector",[]]} {
    %out = "algebra.exec.vector_scale"(%a,%x) {binding=@vector_scale,parameters=[],site="out"} : (!fs,!f)->(!fs)
    local.return %out : !fs
  }
  local.func @msm(%a:!fs,%g:!gs)->(!g) attributes {logical_origin=["msm",[]]} {
    %out = "algebra.exec.group_msm"(%a,%g) {binding=@curve_msm,parameters=[],site="out"} : (!fs,!gs)->(!g)
    local.return %out : !g
  }
  local.func @append_group(%g:!gs,%v:!g)->(!gs) attributes {logical_origin=["append_group",[]]} {
    %out = "algebra.exec.group_append"(%g,%v) {binding=@curve_append,parameters=[],site="out"} : (!gs,!g)->(!gs)
    local.return %out : !gs
  }
  local.func @append_field(%a:!fs,%v:!f)->(!fs) attributes {logical_origin=["append_field",[]]} {
    %out = "algebra.exec.vector_append"(%a,%v) {binding=@vector_append,parameters=[],site="out"} : (!fs,!f)->(!fs)
    local.return %out : !fs
  }
  local.func @get_group(%g:!gs,%i:ui64)->(!g) attributes {logical_origin=["get_group",[]]} {
    %out = "algebra.exec.group_get"(%g,%i) {binding=@curve_get,parameters=[],site="out"} : (!gs,ui64)->(!g)
    local.return %out : !g
  }
  local.func @get_field(%a:!fs,%i:ui64)->(!f) attributes {logical_origin=["get_field",[]]} {
    %out = "algebra.exec.vector_get"(%a,%i) {binding=@vector_get,parameters=[],site="out"} : (!fs,ui64)->(!f)
    local.return %out : !f
  }
  local.func @empty_group()->(!gs) attributes {logical_origin=["empty_group",[]]} {
    %out = "algebra.exec.group_empty"() {binding=@curve_empty,parameters=[],site="out"} : ()->(!gs)
    local.return %out : !gs
  }
  local.func @empty_field()->(!fs) attributes {logical_origin=["empty_field",[]]} {
    %out = "algebra.exec.vector_empty"() {binding=@vector_empty,parameters=[],site="out"} : ()->(!fs)
    local.return %out : !fs
  }
  local.func @cross(%a:!fs,%g:!gs)->(!g,!g) attributes {logical_origin=["cross",[]]} {
    %a2:2 = "algebra.exec.vector_split"(%a) {binding=@vector_split,parameters=[],site="a2"} : (!fs)->(!fs,!fs)
    %g2:2 = "algebra.exec.group_split"(%g) {binding=@curve_split,parameters=[],site="g2"} : (!gs)->(!gs,!gs)
    %l = "algebra.exec.group_msm"(%a2#0,%g2#1) {binding=@curve_msm,parameters=[],site="l"} : (!fs,!gs)->(!g)
    %r = "algebra.exec.group_msm"(%a2#1,%g2#0) {binding=@curve_msm,parameters=[],site="r"} : (!fs,!gs)->(!g)
    local.return %l,%r : !g,!g
  }
  local.func @fold_field(%a:!fs,%x:!f,%y:!f)->(!fs) attributes {logical_origin=["fold_field",[]]} {
    %s:2 = "algebra.exec.vector_split"(%a) {binding=@vector_split,parameters=[],site="s"} : (!fs)->(!fs,!fs)
    %l = "algebra.exec.vector_scale"(%s#0,%x) {binding=@vector_scale,parameters=[],site="l"} : (!fs,!f)->(!fs)
    %r = "algebra.exec.vector_scale"(%s#1,%y) {binding=@vector_scale,parameters=[],site="r"} : (!fs,!f)->(!fs)
    %v = "algebra.exec.vector_add"(%l,%r) {binding=@vector_add,parameters=[],site="v"} : (!fs,!fs)->(!fs)
    local.return %v : !fs
  }
  local.func @fold_group(%a:!gs,%x:!f,%y:!f)->(!gs) attributes {logical_origin=["fold_group",[]]} {
    %s:2 = "algebra.exec.group_split"(%a) {binding=@curve_split,parameters=[],site="s"} : (!gs)->(!gs,!gs)
    %l = "algebra.exec.group_vector_scale"(%s#0,%x) {binding=@curve_vector_scale,parameters=[],site="l"} : (!gs,!f)->(!gs)
    %r = "algebra.exec.group_vector_scale"(%s#1,%y) {binding=@curve_vector_scale,parameters=[],site="r"} : (!gs,!f)->(!gs)
    %v = "algebra.exec.group_vector_add"(%l,%r) {binding=@curve_vector_add,parameters=[],site="v"} : (!gs,!gs)->(!gs)
    local.return %v : !gs
  }
  local.func @same_groups(%a:!gs,%b:!gs)->(i1) attributes {logical_origin=["same_groups",[]]} {
    %n = "algebra.exec.group_length"(%a) {binding=@curve_length,parameters=[],site="n"} : (!gs)->(ui64)
    %m = "algebra.exec.group_length"(%b) {binding=@curve_length,parameters=[],site="m"} : (!gs)->(ui64)
    %same = "algebra.exec.index_equal"(%n,%m) {binding=@index_equal,parameters=[],site="same"} : (ui64,ui64)->(i1)

    %result = "local.if"(%same,%a,%b,%n) ({ ^equal_length(%a0:!gs,%b0:!gs,%count:ui64):
    %zero = "algebra.exec.index_constant"() {binding=@index_constant,parameters=["0"],site="zero"} : ()->(ui64)
    %yes = "local.bool_constant"() {value=true,site="yes"} : ()->i1
    %checked = "local.for"(%zero,%count,%yes,%a0,%b0) ({ ^element(%i:ui64,%ok:i1,%left:!gs,%right:!gs):
    %l = "algebra.exec.group_get"(%left,%i) {binding=@curve_get,parameters=[],site="l"} : (!gs,ui64)->(!g)
    %r = "algebra.exec.group_get"(%right,%i) {binding=@curve_get,parameters=[],site="r"} : (!gs,ui64)->(!g)
    %eq = "algebra.exec.group_equal"(%l,%r) {binding=@curve_equal,parameters=[],site="eq"} : (!g,!g)->(i1)
    %next = "algebra.exec.bool_and"(%ok,%eq) {binding=@bool_and,parameters=[],site="next"} : (i1,i1)->(i1)
      "local.yield"(%next,%left,%right) : (i1,!gs,!gs)->()
    }) {site="elements"} : (ui64,ui64,i1,!gs,!gs)->i1
    "local.yield"(%checked) : (i1)->()
    }, { ^different_length(%a0:!gs,%b0:!gs,%count:ui64):
      %no = "local.bool_constant"() {value=false,site="no"} : ()->i1
      "local.yield"(%no) : (i1)->()
    }) {site="lengths"} : (i1,!gs,!gs,ui64)->i1
    local.return %result : i1
  }
  "protocol.func"() ({ ^entry(%n:ui64,%g:!gs,%commitment:!g,%a:!fs,%rng:!r,%coins:!s):
    %sample:2 = "protocol.local_call"(%rng) {callee=@draw,role="P",site="sample"} : (!r)->(!f,!r)
    %prep:2 = "protocol.local_call"(%sample#0) {callee=@inverse,role="P",site="prep"} : (!f)->(!f,i1)
    %salt = protocol.exchange %sample#0 {sender="P",receiver="V",site="salt"} : !f
    %vprep:2 = "protocol.local_call"(%salt) {callee=@inverse,role="V",site="vprep"} : (!f)->(!f,i1)
    protocol.guard %vprep#1 {owner="V",site="nonzero_salt"}
    %scaled = "protocol.local_call"(%a,%prep#0) {callee=@scale_vector,role="P",site="scaled"} : (!fs,!f)->(!fs)
    %scaled_commitment = algebra.group_scale %commitment,%vprep#0 : (!g,!f)->!g
    %state:6 = "protocol.repeat"(%n,%scaled,%g,%g,%scaled_commitment,%prep#1,%sample#1,%coins) ({
    ^round(%i:ui64,%a0:!fs,%gp:!gs,%gv:!gs,%claim:!g,%complete:i1,%round_rng:!r,%random:!s):
    %cross:2 = "protocol.local_call"(%a0,%gp) {callee=@cross,role="P",site="cross"} : (!fs,!gs)->(!g,!g)
    %left = protocol.exchange %cross#0 {sender="P",receiver="V",site="left"} : !g
    %right = protocol.exchange %cross#1 {sender="P",receiver="V",site="right"} : !g
    %round_sample:2 = "protocol.local_call"(%round_rng) {callee=@draw,role="P",site="round_randomness"} : (!r)->(!f,!r)
    %round_salt = protocol.exchange %round_sample#0 {sender="P",receiver="V",site="round_salt"} : !f
    %c = "protocol.query"(%random) {method="draw",owner="V",site="draw"} : (!s)->!f
    %x = protocol.exchange %c {sender="V",receiver="P",site="challenge"} : !f
    %pi:2 = "protocol.local_call"(%x) {callee=@inverse,role="P",site="pi"} : (!f)->(!f,i1)
    %vi:2 = "protocol.local_call"(%c) {callee=@inverse,role="V",site="vi"} : (!f)->(!f,i1)
    protocol.guard %vi#1 {owner="V",site="nonzero_challenge"}
    %ready = arith.andi %complete,%pi#1 : i1
    %anext = "protocol.local_call"(%a0,%x,%pi#0) {callee=@fold_field,role="P",site="anext"} : (!fs,!f,!f)->(!fs)
    %gnext = "protocol.local_call"(%gp,%pi#0,%x) {callee=@fold_group,role="P",site="gnext"} : (!gs,!f,!f)->(!gs)
    %expected = "protocol.local_call"(%gv,%vi#0,%c) {callee=@fold_group,role="V",site="expected"} : (!gs,!f,!f)->(!gs)
    %received = protocol.exchange %gnext {sender="P",receiver="V",site="received"} : !gs
    %same = "protocol.local_call"(%received,%expected) {callee=@same_groups,role="V",site="same"} : (!gs,!gs)->(i1)
    protocol.guard %same {owner="V",site="received_groups"}
    %xx = algebra.field_multiply %c,%c : (!f,!f)->!f
    %yy = algebra.field_multiply %vi#0,%vi#0 : (!f,!f)->!f
    %lterm = algebra.group_scale %left,%xx : (!g,!f)->!g
    %rterm = algebra.group_scale %right,%yy : (!g,!f)->!g
    %middle = algebra.group_add %claim,%lterm : (!g,!g)->!g
    %next = algebra.group_add %middle,%rterm : (!g,!g)->!g
    "protocol.yield"(%anext,%gnext,%received,%next,%ready,%round_sample#1) : (!fs,!gs,!gs,!g,i1,!r)->()
    }) {site="rounds",carried=6:i64,maximum=8:i64,roles=["P","V"],carried_roles=[["P"],["P"],["V"],["V"],["P"],["P"]]} : (ui64,!fs,!gs,!gs,!g,i1,!r,!s)->(!fs,!gs,!gs,!g,i1,!r)
    %final = protocol.exchange %state#0 {sender="P",receiver="V",site="final"} : !fs
    %actual = "protocol.local_call"(%final,%state#2) {callee=@msm,role="V",site="actual"} : (!fs,!gs)->(!g)
    %accepted = algebra.group_equal %actual,%state#3 : (!g,!g)->i1
    "protocol.return"(%accepted,%state#4,%state#5) : (i1,i1,!r)->()
  }) {sym_name="fold",function_type=(ui64,!gs,!g,!fs,!r,!s)->(i1,i1,!r),roles=["P","V"],input_roles=[["P","V"],["P","V"],["V"],["P"],["P"],["V"]],output_roles=[["V"],["P"],["P"]]} : ()->()
  "protocol.func"() ({ ^entry(%n:ui64,%g:!gs,%commitment:!g,%a:!fs,%rng:!r,%coins:!s):
    %sample:2 = "protocol.local_call"(%rng) {callee=@draw,role="P",site="sample"} : (!r)->(!f,!r)
    %prep:2 = "protocol.local_call"(%sample#0) {callee=@inverse,role="P",site="prep"} : (!f)->(!f,i1)
    %salt = protocol.exchange %sample#0 {sender="P",receiver="V",site="salt"} : !f
    %vprep:2 = "protocol.local_call"(%salt) {callee=@inverse,role="V",site="vprep"} : (!f)->(!f,i1)
    protocol.guard %vprep#1 {owner="V",site="nonzero_salt"}
    %scaled = "protocol.local_call"(%a,%prep#0) {callee=@scale_vector,role="P",site="scaled"} : (!fs,!f)->(!fs)
    %scaled_commitment = algebra.group_scale %commitment,%vprep#0 : (!g,!f)->!g
    %empty_a = "protocol.local_call"() {callee=@empty_field,role="P",site="empty_a"} : ()->(!fs)
    %empty_p = "protocol.local_call"() {callee=@empty_group,role="P",site="empty_p"} : ()->(!gs)
    %empty_v = "protocol.local_call"() {callee=@empty_group,role="V",site="empty_v"} : ()->(!gs)
    %zero = algebra.field_subtract %salt,%salt : (!f,!f)->!f
    %identity = algebra.group_scale %commitment,%zero : (!g,!f)->!g
    %state:6 = "protocol.repeat"(%n,%empty_a,%empty_p,%empty_v,%identity,%identity,%sample#1,%scaled,%g,%coins) ({
    ^round(%i:ui64,%acc:!fs,%gp:!gs,%gv:!gs,%sum:!g,%weighted:!g,%round_rng:!r,%coefficients:!fs,%bases:!gs,%random:!s):
    %ai = "protocol.local_call"(%coefficients,%i) {callee=@get_field,role="P",site="ai"} : (!fs,ui64)->(!f)
    %gi = "protocol.local_call"(%bases,%i) {callee=@get_group,role="P",site="gi"} : (!gs,ui64)->(!g)
    %term = algebra.group_scale %gi,%ai : (!g,!f)->!g
    %contribution = protocol.exchange %term {sender="P",receiver="V",site="contribution"} : !g
    %round_sample:2 = "protocol.local_call"(%round_rng) {callee=@draw,role="P",site="round_randomness"} : (!r)->(!f,!r)
    %round_salt = protocol.exchange %round_sample#0 {sender="P",receiver="V",site="round_salt"} : !f
    %c = "protocol.query"(%random) {method="draw",owner="V",site="draw"} : (!s)->!f
    %x = protocol.exchange %c {sender="V",receiver="P",site="challenge"} : !f
    %weight = algebra.field_multiply %ai,%x : (!f,!f)->!f
    %anext = "protocol.local_call"(%acc,%weight) {callee=@append_field,role="P",site="anext"} : (!fs,!f)->(!fs)
    %gnext = "protocol.local_call"(%gp,%gi) {callee=@append_group,role="P",site="gnext"} : (!gs,!g)->(!gs)
    %base = "protocol.local_call"(%bases,%i) {callee=@get_group,role="V",site="base"} : (!gs,ui64)->(!g)
    %expected = "protocol.local_call"(%gv,%base) {callee=@append_group,role="V",site="expected"} : (!gs,!g)->(!gs)
    %received = protocol.exchange %gnext {sender="P",receiver="V",site="received"} : !gs
    %same = "protocol.local_call"(%received,%expected) {callee=@same_groups,role="V",site="same"} : (!gs,!gs)->(i1)
    protocol.guard %same {owner="V",site="received_groups"}
    %sum_next = algebra.group_add %sum,%contribution : (!g,!g)->!g
    %weighted_term = algebra.group_scale %contribution,%c : (!g,!f)->!g
    %weighted_next = algebra.group_add %weighted,%weighted_term : (!g,!g)->!g
    "protocol.yield"(%anext,%gnext,%received,%sum_next,%weighted_next,%round_sample#1) : (!fs,!gs,!gs,!g,!g,!r)->()
    }) {site="rounds",carried=6:i64,maximum=32:i64,roles=["P","V"],carried_roles=[["P"],["P"],["V"],["V"],["V"],["P"]]} : (ui64,!fs,!gs,!gs,!g,!g,!r,!fs,!gs,!s)->(!fs,!gs,!gs,!g,!g,!r)
    %final = protocol.exchange %state#0 {sender="P",receiver="V",site="final"} : !fs
    %actual = "protocol.local_call"(%final,%state#2) {callee=@msm,role="V",site="actual"} : (!fs,!gs)->(!g)
    %weighted_ok = algebra.group_equal %actual,%state#4 : (!g,!g)->i1
    %claim_ok = algebra.group_equal %state#3,%scaled_commitment : (!g,!g)->i1
    %accepted = arith.andi %weighted_ok,%claim_ok : i1
    "protocol.return"(%accepted,%prep#1,%state#5) : (i1,i1,!r)->()
  }) {sym_name="batch",function_type=(ui64,!gs,!g,!fs,!r,!s)->(i1,i1,!r),roles=["P","V"],input_roles=[["P","V"],["P","V"],["V"],["P"],["P"],["V"]],output_roles=[["V"],["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
