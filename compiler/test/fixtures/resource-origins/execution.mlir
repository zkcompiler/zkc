!r = !local.capability<"rng:bls12-381.fr">
!t = !local.capability<"transcript:merlin3.bls12-381.fr64be/0">
!f = !algebra.field<"bls12-381.fr">
!tag = !local.variant<"variant:5b227a6b632e76617269616e742f30222c5b2243686f696365222c226c656674222c5b5d2c5b2231222c2232225d2c227269676874222c5b2234222c2232225d2c5b2233222c2235225d2c5b2230222c2236225d5d5d">
module { "protocol.module"() ({
 "local.binding"() {sym_name="coordinates",contract="indices.empty",arguments=[],implementation=""} : ()->()
 "local.binding"() {sym_name="random",contract="random.draw",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="observe",contract="transcript.native.indexed.observe.data",arguments=["merlin3.bls12-381.fr64be/0","bool"],implementation=""} : ()->()
 "local.binding"() {sym_name="challenge",contract="transcript.native.indexed.challenge",arguments=["merlin3.bls12-381.fr64be/0"],implementation=""} : ()->()
 local.func @draw(%r:!r,%t:!t,%go:i1)->(!r,!t) attributes {logical_origin=["draw",[]]} {
  %sample:2 = "crypto.exec.random_draw"(%r) {binding=@random,parameters=[],site="random"} : (!r)->(!f,!r)
  %coordinates = "algebra.exec.indices_empty"() {binding=@coordinates,parameters=[],site="coordinates"} : ()->tensor<?xui64>
  %observed = "crypto.exec.indexed_transcript_observe_data"(%t,%go,%coordinates) {binding=@observe,parameters=["010500000000000000001c000000000000007a6b632e6e61746976652d6f726967696e2d74656d706c6174652f300004000000000000006d61696e0100000000000000000100000000000000000106000000000000000007000000000000006d6573736167650007000000000000004f726967696e730007000000000000006d6573736167650007000000000000006d6573736167650001000000000000005000010000000000000056"],site="observe"} : (!t,i1,tensor<?xui64>)->!t
  %challenge:2 = "crypto.exec.indexed_transcript_challenge"(%observed,%coordinates) {binding=@challenge,parameters=["010500000000000000001c000000000000007a6b632e6e61746976652d6f726967696e2d74656d706c6174652f300004000000000000006d61696e0100000000000000000100000000000000000107000000000000000005000000000000007175657279000500000000000000526f756e6400040000000000000064726177000700000000000000696e7075745f3000150000000000000072616e646f6d2e626c7331322d3338312e66722f300004000000000000006472617700010000000000000050"],site="challenge"} : (!t,tensor<?xui64>)->(!f,!t)
  local.return %sample#1,%challenge#1 : !r,!t
 }
 local.func @step(%r:!r,%t:!t,%go:i1,%lo:ui64,%hi:ui64)->(!r,!t) attributes {logical_origin=["step",[]]} {
  %tag = "local.if"(%go) ({
   %left = "local.variant_inject"() {alternative="left",site="left"} : ()->!tag
   "local.yield"(%left) : (!tag)->()
  }, {
   %right = "local.variant_inject"() {alternative="right",site="right"} : ()->!tag
   "local.yield"(%right) : (!tag)->()
  }) {site="tag"} : (i1)->!tag
  %same:2 = "local.match"(%tag,%r,%t) ({ ^left(%a:!r,%b:!t):
   "local.yield"(%a,%b) : (!r,!t)->()
  }, { ^right(%c:!r,%d:!t):
   "local.yield"(%c,%d) : (!r,!t)->()
  }) {alternatives=["left","right"],site="match"} : (!tag,!r,!t)->(!r,!t)
  %next:2 = "local.if"(%go,%same#0,%same#1,%go,%lo,%hi) ({ ^yes(%a:!r,%b:!t,%g:i1,%l:ui64,%h:ui64):
   %loop:2 = "local.for"(%l,%h,%a,%b,%g) ({ ^body(%i:ui64,%x:!r,%y:!t,%flag:i1):
    %out:2 = local.apply @draw(%x,%y,%flag) {site="draw"} : (!r,!t,i1)->(!r,!t)
    "local.yield"(%out#0,%out#1,%flag) : (!r,!t,i1)->()
   }) {site="loop"} : (ui64,ui64,!r,!t,i1)->(!r,!t)
   "local.yield"(%loop#0,%loop#1) : (!r,!t)->()
  }, { ^no(%a:!r,%b:!t,%g:i1,%l:ui64,%h:ui64):
   %once:2 = local.apply @draw(%a,%b,%g) {site="once"} : (!r,!t,i1)->(!r,!t)
   "local.yield"(%once#0,%once#1) : (!r,!t)->()
  }) {site="choice"} : (i1,!r,!t,i1,ui64,ui64)->(!r,!t)
  local.return %next#0,%next#1 : !r,!t
 }
 "protocol.func"() ({ ^child(%r:!r,%t:!t,%go:i1,%lo:ui64,%hi:ui64):
  %one = "data.index"() {value="1"} : ()->ui64
  %result:2 = "protocol.repeat"(%one,%r,%t,%go,%lo,%hi) ({ ^body(%i:ui64,%a:!r,%b:!t,%g:i1,%l:ui64,%h:ui64):
   %out:2 = "protocol.local_call"(%a,%b,%g,%l,%h) {callee=@step,role="P",site="step"} : (!r,!t,i1,ui64,ui64)->(!r,!t)
   "protocol.yield"(%out#0,%out#1) : (!r,!t)->()
  }) {site="inner",carried=2:i64,maximum=1:i64,roles=["P"],carried_roles=[["P"],["P"]]} : (ui64,!r,!t,i1,ui64,ui64)->(!r,!t)
  "protocol.return"(%result#0,%result#1) : (!r,!t)->()
 }) {sym_name="child",function_type=(!r,!t,i1,ui64,ui64)->(!r,!t),roles=["P"],input_roles=[["P"],["P"],["P"],["P"],["P"]],output_roles=[["P"],["P"]]} : ()->()
 "protocol.func"() ({ ^entry(%n:ui64,%r:!r,%t:!t,%go:i1,%lo:ui64,%hi:ui64):
  %result:2 = "protocol.repeat"(%n,%r,%t,%go,%lo,%hi) ({ ^body(%i:ui64,%a:!r,%b:!t,%g:i1,%l:ui64,%h:ui64):
   %out:2 = "protocol.apply"(%a,%b,%g,%l,%h) {callee=@child,roles=["P"],site="child"} : (!r,!t,i1,ui64,ui64)->(!r,!t)
   "protocol.yield"(%out#0,%out#1) : (!r,!t)->()
  }) {site="outer",carried=2:i64,maximum=8:i64,roles=["P"],carried_roles=[["P"],["P"]]} : (ui64,!r,!t,i1,ui64,ui64)->(!r,!t)
  "protocol.return"(%result#0,%result#1) : (!r,!t)->()
 }) {sym_name="main",function_type=(ui64,!r,!t,i1,ui64,ui64)->(!r,!t),roles=["P"],input_roles=[["P"],["P"],["P"],["P"],["P"],["P"]],output_roles=[["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
