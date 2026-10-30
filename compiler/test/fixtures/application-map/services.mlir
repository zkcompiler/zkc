!F = !algebra.field<"bls12-381.fr">
!S = !protocol.service_ref<"random.bls12-381.fr/0">
module { "protocol.module"() ({
  "protocol.func"() ({ ^entry(%first:!S,%second:!S):
    %a = "protocol.query"(%first) {method="draw",owner="A",site="first"} : (!S)->!F
    %b = "protocol.query"(%second) {method="draw",owner="A",site="second"} : (!S)->!F
    "protocol.return"(%a,%b) : (!F,!F)->()
  }) {sym_name="draw_pair",origin=["draw_pair",[]],function_type=(!S,!S)->(!F,!F),roles=["A","B"],input_roles=[["A"],["A"]],output_roles=[["A"],["A"]]} : ()->()
  "protocol.func"() ({ ^entry(%first:!S,%second:!S):
    %r:2 = protocol.apply @draw_pair(%first,%second) {roles=["P","V"],site="pair"} : (!S,!S)->(!F,!F)
    "protocol.return"(%r#0,%r#1) : (!F,!F)->()
  }) {sym_name="main",origin=["main",[]],function_type=(!S,!S)->(!F,!F),roles=["P","V"],input_roles=[["P"],["P"]],output_roles=[["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
