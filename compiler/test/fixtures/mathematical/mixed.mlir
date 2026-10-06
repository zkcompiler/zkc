module {
"protocol.module"() ({
  func.func private @helper(%a: !algebra.field<"bls12-381.fr">, %w: !algebra.field<"bls12-381.fr">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) {
    %s = algebra.field_add %a, %a : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
    %t = algebra.field_multiply %s, %w : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
    return %s, %t : !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">
  }
  "protocol.func"() ({
  ^entry(%a: !algebra.field<"bls12-381.fr">, %w: !algebra.field<"bls12-381.fr">, %unused: i1):
    %h:2 = func.call @helper(%a, %w) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
    "protocol.return"(%h#0, %h#1) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
  }) {sym_name="main", function_type=(!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, i1) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), roles=["Alice", "Bob", "Observer"], input_roles=[["Alice","Bob"],["Alice"],["Observer"]], output_roles=[["Alice","Bob"],["Alice"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> ()
}
