!F = !algebra.field<"bls12-381.fr">
!Q = !local.variant<"variant:5b227a6b632e76617269616e742f30222c5b227175657279222c22626c7331322d3338312e6672222c5b2230222c2231225d2c2276616c7565222c22626f6f6c222c226669656c643a626c7331322d3338312e6672222c5b2234222c2235225d2c5b2233222c2236225d2c5b2237225d2c5b2232222c2238225d5d5d">
!S = !data.sequence<!Q>
module { "protocol.module"() ({
  "data.domain"() ({ ^entry(%queries:!S):
    %d = "data.domain_elements"(%queries) : (!S)->!data.domain<!Q>
    "data.domain_yield"(%d) : (!data.domain<!Q>)->()
  }) {sym_name="queries",sym_visibility="private",function_type=(!S)->!data.domain<!Q>} : ()->()
  func.func private @make(%active:i1,%value:!F)->!Q {
    %q = "data.make"(%active,%value) {alternative="value"} : (i1,!F)->!Q
    return %q : !Q
  }
  func.func private @step(%valid:i1,%query:!Q,%queries:!S)->i1 {
    %active = "data.get"(%query) {index=0:i64} : (!Q)->i1
    %value = "data.get"(%query) {index=1:i64} : (!Q)->!F
    %r = arith.andi %valid,%active : i1
    return %r : i1
  }
  "protocol.func"() ({ ^entry(%queries:!S):
    %yes = arith.constant true
    %r = "algebra.finite_fold"(%queries,%yes) {domain=@queries,step=@step} : (!S,i1)->i1
    "protocol.return"(%r) : (i1)->()
  }) {sym_name="main",origin=["main",[]],function_type=(!S)->i1,roles=["P"],input_roles=[["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
