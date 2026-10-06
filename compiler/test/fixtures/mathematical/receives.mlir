module {
"protocol.module"() ({

"protocol.func"() ({
^entry(%a: !algebra.field<"bls12-381.fr">):
%one = protocol.exchange %a {site="first",sender="Alice",receiver="Bob"} : !algebra.field<"bls12-381.fr">
%two = protocol.exchange %a {site="second",sender="Alice",receiver="Bob"} : !algebra.field<"bls12-381.fr">
%sum = algebra.field_add %one, %two : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
"protocol.return"(%sum) : (!algebra.field<"bls12-381.fr">) -> ()
}) {sym_name="main", function_type=(!algebra.field<"bls12-381.fr">) -> (!algebra.field<"bls12-381.fr">), roles=["Alice", "Bob"], input_roles=[["Alice"]], output_roles=[["Alice", "Bob"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> ()
}
