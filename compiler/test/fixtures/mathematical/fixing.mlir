// Shared repeated factors, nested prefix fixing, and two observations.
module { "protocol.module"() ({
"protocol.func"() ({
^entry(%T: !data.field_array<"bls12-381.fr", 8>, %U: !data.field_array<"bls12-381.fr", 8>, %r0: !algebra.field<"bls12-381.fr">, %r1: !algebra.field<"bls12-381.fr">, %y0: !algebra.field<"bls12-381.fr">, %y1: !algebra.field<"bls12-381.fr">):
 %t = "poly.mle"(%T) : (!data.field_array<"bls12-381.fr", 8>) -> !poly.polynomial<"bls12-381.fr", 3>
 %u = "poly.mle"(%U) : (!data.field_array<"bls12-381.fr", 8>) -> !poly.polynomial<"bls12-381.fr", 3>
 %square = "poly.multiply"(%t, %t) : (!poly.polynomial<"bls12-381.fr", 3>, !poly.polynomial<"bls12-381.fr", 3>) -> !poly.polynomial<"bls12-381.fr", 3>
 %cross = "poly.multiply"(%t, %u) : (!poly.polynomial<"bls12-381.fr", 3>, !poly.polynomial<"bls12-381.fr", 3>) -> !poly.polynomial<"bls12-381.fr", 3>
 %f = "poly.add"(%square, %cross) : (!poly.polynomial<"bls12-381.fr", 3>, !poly.polynomial<"bls12-381.fr", 3>) -> !poly.polynomial<"bls12-381.fr", 3>
 %first = "poly.fix"(%f, %r0) : (!poly.polynomial<"bls12-381.fr", 3>, !algebra.field<"bls12-381.fr">) -> !poly.polynomial<"bls12-381.fr", 2>
 %fixed = "poly.fix"(%first, %r1) : (!poly.polynomial<"bls12-381.fr", 2>, !algebra.field<"bls12-381.fr">) -> !poly.polynomial<"bls12-381.fr", 1>
 %a = "poly.evaluate"(%fixed, %y0) : (!poly.polynomial<"bls12-381.fr", 1>, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
 %b = "poly.evaluate"(%fixed, %y1) : (!poly.polynomial<"bls12-381.fr", 1>, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
 %c = "poly.coefficients"(%fixed) : (!poly.polynomial<"bls12-381.fr", 1>) -> !data.field_array<"bls12-381.fr", 3>
 "protocol.return"(%a, %b, %c) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_array<"bls12-381.fr", 3>) -> ()
}) {sym_name="main", function_type=(!data.field_array<"bls12-381.fr", 8>, !data.field_array<"bls12-381.fr", 8>, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !data.field_array<"bls12-381.fr", 3>), roles=["Solo"],
input_roles=[["Solo"],["Solo"],["Solo"],["Solo"],["Solo"],["Solo"]], output_roles=[["Solo"],["Solo"],["Solo"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () }
