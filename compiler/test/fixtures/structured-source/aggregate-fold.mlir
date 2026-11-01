!F = !algebra.field<"bls12-381.fr">
!Q = !data.variant<#data.identity<["tuple", [["atom", "query"], ["atom", "bls12-381.fr"]]]>, [#data.alternative<"value", [i1, !algebra.field<"bls12-381.fr">]>]>
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
    %r = "data.finite_fold"(%queries,%yes) {domain=@queries,step=@step} : (!S,i1)->i1
    "protocol.return"(%r) : (i1)->()
  }) {sym_name="main",origin=["main",[]],function_type=(!S)->i1,roles=["P"],input_roles=[["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
