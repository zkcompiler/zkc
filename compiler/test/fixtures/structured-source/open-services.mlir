!F = !algebra.field<"bls12-381.fr">
!S = !protocol.service_ref<"random.bls12-381.fr/0">
module { "protocol.module"() ({
  "protocol.func"() ({
  ^entry(%first:!S,%second:!S,%flag:i1):
    %a = "protocol.query"(%first) {method="draw",owner="P",site="first"} : (!S)->!F
    %b = "protocol.query"(%second) {method="draw",owner="P",site="second"} : (!S)->!F
    "protocol.guard"(%flag) {owner="P",site="check"} : (i1)->()
    "protocol.return"(%a,%b,%flag) : (!F,!F,i1)->()
  }) {sym_name="main",function_type=(!S,!S,i1)->(!F,!F,i1),roles=["P","V"],input_roles=[["P"],["P"],["P","V"]],output_roles=[["P"],["P"],["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
