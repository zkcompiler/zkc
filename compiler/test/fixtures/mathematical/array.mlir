module { "protocol.module"() ({
"protocol.func"() ({
^entry(%x: !algebra.field<"bls12-381.fr">):
 %one = "algebra.constant"() {value=#algebra.literal<!algebra.field<"bls12-381.fr">, 1 : ui255>} : () -> !algebra.field<"bls12-381.fr">
 %a = "data.array_from_elements"(%x, %one) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !data.field_array<"bls12-381.fr", 2>
 %received = protocol.exchange %a {sender="P", receiver="V", site="array"} : !data.field_array<"bls12-381.fr", 2>
 %v = "data.array_at"(%received) {index=0:i64} : (!data.field_array<"bls12-381.fr", 2>) -> !algebra.field<"bls12-381.fr">
 "protocol.return"(%v) : (!algebra.field<"bls12-381.fr">) -> ()
}) {sym_name="main", function_type=(!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, roles=["P","V"], input_roles=[["P"]],output_roles=[["V"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () }
