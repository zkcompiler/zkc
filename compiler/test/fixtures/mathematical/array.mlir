module { "protocol.module"() ({
"protocol.func"() ({
^entry(%x: !algebra.field<"bls12-381.fr">):
 %one = "algebra.constant"() {value="1"} : () -> !algebra.field<"bls12-381.fr">
 %a = "algebra.array_from_elements"(%x, %one) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_array<"bls12-381.fr", 2>
 %received = protocol.exchange %a {sender="P", receiver="V", site="array"} : !algebra.field_array<"bls12-381.fr", 2>
 %v = "algebra.array_at"(%received) {index=0:i64} : (!algebra.field_array<"bls12-381.fr", 2>) -> !algebra.field<"bls12-381.fr">
 "protocol.return"(%v) : (!algebra.field<"bls12-381.fr">) -> ()
}) {sym_name="main", function_type=(!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, roles=["P","V"], input_roles=[["P"]],output_roles=[["V"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () }
