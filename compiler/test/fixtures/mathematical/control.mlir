module {
"protocol.module"() ({

"protocol.func"() ({
^entry(%condition: i1, %a: !algebra.field<"bls12-381.fr">, %b: !algebra.field<"bls12-381.fr">):
%v = arith.select %condition, %a, %b : !algebra.field<"bls12-381.fr">
%sent = protocol.exchange %v {site="selected",sender="Bob",receiver="Alice"} : !algebra.field<"bls12-381.fr">
protocol.guard %condition {site="check",owner="Bob"}
%again = protocol.exchange %a {site="after_guard",sender="Bob",receiver="Alice"} : !algebra.field<"bls12-381.fr">
"protocol.return"(%condition, %sent, %again) : (i1, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
}) {sym_name="main", function_type=(i1, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (i1, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), roles=["Alice", "Bob"], input_roles=[["Bob"], ["Alice", "Bob"], ["Alice", "Bob"]], output_roles=[["Bob"], ["Alice", "Bob"], ["Alice", "Bob"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> ()
}
