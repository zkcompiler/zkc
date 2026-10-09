!f = !algebra.field<"bls12-381.fr">
!m = tensor<?x?x!f>
!opt = !local.variant<"variant:5b227a6b632e76617269616e74222c5b224f7074696f6e616c5472616365222c226e6f6e65222c5b5d2c5b2231222c2232225d2c22736f6d65222c226d61747269783a626c7331322d3338312e6672222c5b2235225d2c5b2234222c2236225d2c5b2233222c2237225d2c5b2230222c2238225d5d5d">
!pair = !local.variant<"variant:5b227a6b632e76617269616e74222c5b22547261636550616972222c2270616972222c224f7074696f6e616c5472616365222c226e6f6e65222c5b5d2c5b2233222c2234225d2c22736f6d65222c226d61747269783a626c7331322d3338312e6672222c5b2237225d2c5b2236222c2238225d2c5b2235222c2239225d2c5b2232222c223130225d2c5b223131222c223131225d2c5b2231222c223132225d2c5b223133225d2c5b2230222c223134225d5d5d">
module { "protocol.module"() ({
 "local.binding"() {sym_name="dimension",contract="matrix.dimension",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="index",contract="index.constant",arguments=[],implementation=""} : ()->()
 local.func @dimensions(%input:!opt) -> (ui64,ui64) attributes {logical_origin=["dimensions",[]]} {
   %dims:2 = "local.match"(%input) ({
     %zero = "algebra.exec.index_constant"() {binding=@index,parameters=["0"],site="absent"} : ()->ui64
     "local.yield"(%zero,%zero) : (ui64,ui64)->()
   }, { ^some(%trace:!m):
     %h = "algebra.exec.matrix_dimension"(%trace) {binding=@dimension,parameters=["0"],site="height"} : (!m)->ui64
     %w = "algebra.exec.matrix_dimension"(%trace) {binding=@dimension,parameters=["1"],site="width"} : (!m)->ui64
     "local.yield"(%h,%w) : (ui64,ui64)->()
   }) {alternatives=["none","some"],site="presence"} : (!opt)->(ui64,ui64)
   local.return %dims#0,%dims#1 : ui64,ui64
 }
 "protocol.func"() ({ ^entry(%first:!opt,%second:!opt):
   %pair = "data.make"(%first,%second) {alternative="pair"} : (!opt,!opt)->!pair
   %a = "data.get"(%pair) {index=0:i64} : (!pair)->!opt
   %b = "data.get"(%pair) {index=1:i64} : (!pair)->!opt
   %presentA = "data.is"(%a) {alternative="some"} : (!opt)->i1
   %presentB = "data.is"(%b) {alternative="some"} : (!opt)->i1
   %shapeA:2 = "protocol.local_call"(%a) {callee=@dimensions,role="P",site="first"} : (!opt)->(ui64,ui64)
   %shapeB:2 = "protocol.local_call"(%b) {callee=@dimensions,role="P",site="second"} : (!opt)->(ui64,ui64)
   "protocol.return"(%presentA,%presentB,%shapeA#0,%shapeA#1,%shapeB#0,%shapeB#1) : (i1,i1,ui64,ui64,ui64,ui64)->()
 }) {sym_name="main",function_type=(!opt,!opt)->(i1,i1,ui64,ui64,ui64,ui64),roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"],["P"],["P"],["P"],["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
