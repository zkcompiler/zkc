!r = !local.capability<"rng:bls12-381.fr">
!t = !local.capability<"transcript:merlin3.bls12-381.fr64be/1">
!f = !algebra.field<"bls12-381.fr">
!tag = !local.variant<"variant:5b227a6b632e76617269616e742f31222c5b2243686f696365222c226c656674222c5b5d2c5b2231222c2232225d2c227269676874222c5b2234222c2232225d2c5b2233222c2235225d2c5b2230222c2236225d5d5d">
module { "protocol.module"() ({
 "local.binding"() {sym_name="random",contract="random.draw",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="observe",contract="transcript.observe.bool",arguments=["merlin3.bls12-381.fr64be/1","zkcv.bool/1"],implementation=""} : ()->()
 "local.binding"() {sym_name="challenge",contract="transcript.challenge",arguments=["merlin3.bls12-381.fr64be/1"],implementation=""} : ()->()
 local.func @draw(%r:!r,%t:!t,%go:i1)->(!r,!t) attributes {logical_origin=["draw",[]]} {
  %sample:2 = "crypto.exec.random_draw"(%r) {binding=@random,parameters=[],site="random"} : (!r)->(!f,!r)
  %observed = "crypto.exec.transcript_observe"(%t,%go) {binding=@observe,parameters=["Origins","message","bool","P","V"],site="observe"} : (!t,i1)->!t
  %challenge:2 = "crypto.exec.transcript_challenge"(%observed) {binding=@challenge,parameters=["Origins","challenge","Draw","value","P"],site="challenge"} : (!t)->(!f,!t)
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
