module { "protocol.module"() ({
func.func private @recipe(%T: !algebra.field_array<"bls12-381.fr", 4>, %U: !algebra.field_array<"bls12-381.fr", 4>) -> !poly.polynomial<"bls12-381.fr", 2> {
 %t = "poly.mle"(%T) : (!algebra.field_array<"bls12-381.fr", 4>) -> !poly.polynomial<"bls12-381.fr", 2>
 %u = "poly.mle"(%U) : (!algebra.field_array<"bls12-381.fr", 4>) -> !poly.polynomial<"bls12-381.fr", 2>
 %square = "poly.multiply"(%t, %t) : (!poly.polynomial<"bls12-381.fr", 2>, !poly.polynomial<"bls12-381.fr", 2>) -> !poly.polynomial<"bls12-381.fr", 2>
 %cross = "poly.multiply"(%t, %u) : (!poly.polynomial<"bls12-381.fr", 2>, !poly.polynomial<"bls12-381.fr", 2>) -> !poly.polynomial<"bls12-381.fr", 2>
 %f = "poly.add"(%square, %cross) : (!poly.polynomial<"bls12-381.fr", 2>, !poly.polynomial<"bls12-381.fr", 2>) -> !poly.polynomial<"bls12-381.fr", 2>
 func.return %f : !poly.polynomial<"bls12-381.fr", 2>
}
"protocol.func"() ({
^entry(%T: !algebra.field_array<"bls12-381.fr", 4>, %U: !algebra.field_array<"bls12-381.fr", 4>, %claim: !algebra.field<"bls12-381.fr">, %random: !protocol.service_ref<"random.bls12-381.fr/0">):
 %f = func.call @recipe(%T, %U) : (!algebra.field_array<"bls12-381.fr", 4>, !algebra.field_array<"bls12-381.fr", 4>) -> !poly.polynomial<"bls12-381.fr", 2>
 %zero = "algebra.constant"() {value="0"} : () -> !algebra.field<"bls12-381.fr">
 %one = "algebra.constant"() {value="1"} : () -> !algebra.field<"bls12-381.fr">
 %round0 = "poly.sum_suffix"(%f) {count=1:i64} : (!poly.polynomial<"bls12-381.fr", 2>) -> !poly.polynomial<"bls12-381.fr", 1>
 %coefficients0 = "poly.coefficients"(%round0) : (!poly.polynomial<"bls12-381.fr", 1>) -> !algebra.field_array<"bls12-381.fr", 3>
 %received0 = protocol.exchange %coefficients0 {sender="P",receiver="V",site="round0"} : !algebra.field_array<"bls12-381.fr", 3>
 %q0 = "poly.from_coefficients"(%received0) : (!algebra.field_array<"bls12-381.fr", 3>) -> !poly.polynomial<"bls12-381.fr", 1>
 %at_zero0 = "poly.evaluate"(%q0, %zero) : (!poly.polynomial<"bls12-381.fr", 1>, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
 %at_one0 = "poly.evaluate"(%q0, %one) : (!poly.polynomial<"bls12-381.fr", 1>, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
 %sum0 = algebra.field_add %at_zero0, %at_one0 : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
 %ok0 = algebra.field_equal %sum0, %claim : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
 protocol.guard %ok0 {owner="V",site="guard0"}
 %r0 = "protocol.query"(%random) {method="draw",owner="V",site="query0"} : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
 %delivered0 = protocol.exchange %r0 {sender="V",receiver="P",site="challenge0"} : !algebra.field<"bls12-381.fr">
 %next0 = "poly.evaluate"(%q0, %r0) : (!poly.polynomial<"bls12-381.fr", 1>, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
 %fixed = "poly.fix"(%f, %delivered0) : (!poly.polynomial<"bls12-381.fr", 2>, !algebra.field<"bls12-381.fr">) -> !poly.polynomial<"bls12-381.fr", 1>
 %round1 = "poly.sum_suffix"(%fixed) {count=0:i64} : (!poly.polynomial<"bls12-381.fr", 1>) -> !poly.polynomial<"bls12-381.fr", 1>
 %coefficients1 = "poly.coefficients"(%round1) : (!poly.polynomial<"bls12-381.fr", 1>) -> !algebra.field_array<"bls12-381.fr", 3>
 %received1 = protocol.exchange %coefficients1 {sender="P",receiver="V",site="round1"} : !algebra.field_array<"bls12-381.fr", 3>
 %q1 = "poly.from_coefficients"(%received1) : (!algebra.field_array<"bls12-381.fr", 3>) -> !poly.polynomial<"bls12-381.fr", 1>
 %at_zero1 = "poly.evaluate"(%q1, %zero) : (!poly.polynomial<"bls12-381.fr", 1>, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
 %at_one1 = "poly.evaluate"(%q1, %one) : (!poly.polynomial<"bls12-381.fr", 1>, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
 %sum1 = algebra.field_add %at_zero1, %at_one1 : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
 %ok1 = algebra.field_equal %sum1, %next0 : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
 protocol.guard %ok1 {owner="V",site="guard1"}
 %r1 = "protocol.query"(%random) {method="draw",owner="V",site="query1"} : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
 %delivered1 = protocol.exchange %r1 {sender="V",receiver="P",site="challenge1"} : !algebra.field<"bls12-381.fr">
 %next1 = "poly.evaluate"(%q1, %r1) : (!poly.polynomial<"bls12-381.fr", 1>, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
 "protocol.return"(%T, %U, %r0, %r1, %next1, %delivered0, %delivered1) : (!algebra.field_array<"bls12-381.fr", 4>, !algebra.field_array<"bls12-381.fr", 4>, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
}) {sym_name="reduction", function_type=(!algebra.field_array<"bls12-381.fr", 4>, !algebra.field_array<"bls12-381.fr", 4>, !algebra.field<"bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field_array<"bls12-381.fr", 4>, !algebra.field_array<"bls12-381.fr", 4>, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">),
 roles=["P","V"],input_roles=[["P","V"],["P","V"],["P","V"],["V"]],output_roles=[["V"],["V"],["V"],["V"],["V"],["P"],["P"]]} : () -> ()
"protocol.func"() ({
^entry(%T: !algebra.field_array<"bls12-381.fr", 4>, %U: !algebra.field_array<"bls12-381.fr", 4>, %r0: !algebra.field<"bls12-381.fr">, %r1: !algebra.field<"bls12-381.fr">, %claim: !algebra.field<"bls12-381.fr">):
 %f = func.call @recipe(%T, %U) : (!algebra.field_array<"bls12-381.fr", 4>, !algebra.field_array<"bls12-381.fr", 4>) -> !poly.polynomial<"bls12-381.fr", 2>
 %actual = "poly.evaluate"(%f, %r0, %r1) : (!poly.polynomial<"bls12-381.fr", 2>, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
 %accept = algebra.field_equal %actual, %claim : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
 "protocol.return"(%accept) : (i1) -> ()
}) {sym_name="terminal", function_type=(!algebra.field_array<"bls12-381.fr", 4>, !algebra.field_array<"bls12-381.fr", 4>, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1,
 roles=["V"], input_roles=[["V"],["V"],["V"],["V"],["V"]], output_roles=[["V"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () }
