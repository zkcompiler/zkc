// Shared repeated factors, nested prefix fixing, and two observations.
module { "protocol.module"() ({
"protocol.func"() ({
^entry(%T: tensor<8x!algebra.field<"bls12-381.fr">>, %U: tensor<8x!algebra.field<"bls12-381.fr">>, %r0: !algebra.field<"bls12-381.fr">, %r1: !algebra.field<"bls12-381.fr">, %y0: !algebra.field<"bls12-381.fr">, %y1: !algebra.field<"bls12-381.fr">):
 %smallT = "poly.fix_table"(%T, %r0, %r1) : (tensor<8x!algebra.field<"bls12-381.fr">>, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> tensor<2x!algebra.field<"bls12-381.fr">>
 %smallU = "poly.fix_table"(%U, %r0, %r1) : (tensor<8x!algebra.field<"bls12-381.fr">>, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> tensor<2x!algebra.field<"bls12-381.fr">>
 %t = "poly.mle"(%smallT) : (tensor<2x!algebra.field<"bls12-381.fr">>) -> !poly.polynomial<"bls12-381.fr", 1>
 %u = "poly.mle"(%smallU) : (tensor<2x!algebra.field<"bls12-381.fr">>) -> !poly.polynomial<"bls12-381.fr", 1>
 %square = "poly.multiply"(%t, %t) : (!poly.polynomial<"bls12-381.fr", 1>, !poly.polynomial<"bls12-381.fr", 1>) -> !poly.polynomial<"bls12-381.fr", 1>
 %cross = "poly.multiply"(%t, %u) : (!poly.polynomial<"bls12-381.fr", 1>, !poly.polynomial<"bls12-381.fr", 1>) -> !poly.polynomial<"bls12-381.fr", 1>
 %f = "poly.add"(%square, %cross) : (!poly.polynomial<"bls12-381.fr", 1>, !poly.polynomial<"bls12-381.fr", 1>) -> !poly.polynomial<"bls12-381.fr", 1>
 %a = "poly.evaluate"(%f, %y0) : (!poly.polynomial<"bls12-381.fr", 1>, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
 %b = "poly.evaluate"(%f, %y1) : (!poly.polynomial<"bls12-381.fr", 1>, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
 %c = "poly.coefficients"(%f) : (!poly.polynomial<"bls12-381.fr", 1>) -> tensor<3x!algebra.field<"bls12-381.fr">>
 "protocol.return"(%a, %b, %c) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, tensor<3x!algebra.field<"bls12-381.fr">>) -> ()
}) {sym_name="main", function_type=(tensor<8x!algebra.field<"bls12-381.fr">>, tensor<8x!algebra.field<"bls12-381.fr">>, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, tensor<3x!algebra.field<"bls12-381.fr">>), roles=["Solo"],
input_roles=[["Solo"],["Solo"],["Solo"],["Solo"],["Solo"],["Solo"]], output_roles=[["Solo"],["Solo"],["Solo"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () }
