module { "protocol.module"() ({
"protocol.func"() ({
^entry(%x: !algebra.field<"bls12-381.fr">):
 %one = "algebra.constant"() {value="1"} : () -> !algebra.field<"bls12-381.fr">
 %a = tensor.from_elements %x, %one : tensor<2x!algebra.field<"bls12-381.fr">>
 %received = protocol.exchange %a {sender="P", receiver="V", site="array"} : tensor<2x!algebra.field<"bls12-381.fr">>
 %v = "algebra.array_at"(%received) {index=0:i64} : (tensor<2x!algebra.field<"bls12-381.fr">>) -> !algebra.field<"bls12-381.fr">
 "protocol.return"(%v) : (!algebra.field<"bls12-381.fr">) -> ()
}) {sym_name="main", function_type=(!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, roles=["P","V"], input_roles=[["P"]],output_roles=[["V"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () }
