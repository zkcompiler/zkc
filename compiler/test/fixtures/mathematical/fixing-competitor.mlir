// Shared repeated factors, nested prefix fixing, and two observations.
module { "protocol.module"() ({
"protocol.func"() ({
^entry(%T: !algebra.field_array<"bls12-381.fr", 8>, %U: !algebra.field_array<"bls12-381.fr", 8>, %r0: !algebra.field<"bls12-381.fr">, %r1: !algebra.field<"bls12-381.fr">, %y0: !algebra.field<"bls12-381.fr">, %y1: !algebra.field<"bls12-381.fr">):
 %smallT = "poly.fix_table"(%T, %r0, %r1) : (!algebra.field_array<"bls12-381.fr", 8>, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_array<"bls12-381.fr", 2>
 %smallU = "poly.fix_table"(%U, %r0, %r1) : (!algebra.field_array<"bls12-381.fr", 8>, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_array<"bls12-381.fr", 2>
 %t = "poly.mle"(%smallT) : (!algebra.field_array<"bls12-381.fr", 2>) -> !poly.polynomial<"bls12-381.fr", 1>
 %u = "poly.mle"(%smallU) : (!algebra.field_array<"bls12-381.fr", 2>) -> !poly.polynomial<"bls12-381.fr", 1>
 %square = "poly.multiply"(%t, %t) : (!poly.polynomial<"bls12-381.fr", 1>, !poly.polynomial<"bls12-381.fr", 1>) -> !poly.polynomial<"bls12-381.fr", 1>
 %cross = "poly.multiply"(%t, %u) : (!poly.polynomial<"bls12-381.fr", 1>, !poly.polynomial<"bls12-381.fr", 1>) -> !poly.polynomial<"bls12-381.fr", 1>
 %f = "poly.add"(%square, %cross) : (!poly.polynomial<"bls12-381.fr", 1>, !poly.polynomial<"bls12-381.fr", 1>) -> !poly.polynomial<"bls12-381.fr", 1>
 %a = "poly.evaluate"(%f, %y0) : (!poly.polynomial<"bls12-381.fr", 1>, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
 %b = "poly.evaluate"(%f, %y1) : (!poly.polynomial<"bls12-381.fr", 1>, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
 %c = "poly.coefficients"(%f) : (!poly.polynomial<"bls12-381.fr", 1>) -> !algebra.field_array<"bls12-381.fr", 3>
 "protocol.return"(%a, %b, %c) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_array<"bls12-381.fr", 3>) -> ()
}) {sym_name="main", function_type=(!algebra.field_array<"bls12-381.fr", 8>, !algebra.field_array<"bls12-381.fr", 8>, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field_array<"bls12-381.fr", 3>), roles=["Solo"],
input_roles=[["Solo"],["Solo"],["Solo"],["Solo"],["Solo"],["Solo"]], output_roles=[["Solo"],["Solo"],["Solo"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () }
