!F = !algebra.field<"bls12-381.fr">
!G = !algebra.group<"bls12-381.g1">
module { "protocol.module"() ({
  func.func private @scale(%g:!G,%s:!F) -> (!G,i1) {
    %zero = "algebra.group_identity"() : ()->!G
    %scaled = algebra.group_scale %g,%s : (!G,!F)->!G
    %sum = algebra.group_add %zero,%scaled : (!G,!G)->!G
    %equal = algebra.group_equal %sum,%g : (!G,!G)->i1
    func.return %sum,%equal : !G,i1
  }
  "protocol.func"() ({
  ^entry(%g:!G,%s:!F):
    %r:2 = func.call @scale(%g,%s) : (!G,!F)->(!G,i1)
    "protocol.return"(%r#0,%r#1) : (!G,i1)->()
  }) {sym_name="main",function_type=(!G,!F)->(!G,i1),roles=["P","V"],input_roles=[["P","V"],["P","V"]],output_roles=[["P","V"],["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
