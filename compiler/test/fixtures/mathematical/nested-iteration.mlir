module {
"protocol.module"() ({
  "protocol.func"() ({
  ^entry(%n: ui64, %go: i1, %rng: !protocol.service_ref<"random.bls12-381.fr/0">, %x: !algebra.field<"bls12-381.fr">):
    %count = protocol.exchange %n {sender="P", receiver="V", site="count"} : ui64
    %out = "protocol.repeat"(%count, %x, %go, %rng) ({
    ^outer(%outer_i: ui64, %outer_state: !algebra.field<"bls12-381.fr">, %outer_go: i1, %outer_rng: !protocol.service_ref<"random.bls12-381.fr/0">):
    %next = "protocol.repeat"(%outer_i, %outer_state, %outer_go, %outer_rng) ({
    ^body(%i: ui64, %state: !algebra.field<"bls12-381.fr">, %condition: i1, %coins: !protocol.service_ref<"random.bls12-381.fr/0">):
      protocol.guard %condition {owner="V", site="check"}
      %r = "protocol.query"(%coins) {method="draw", owner="V", site="draw"} : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
      %sent = protocol.exchange %r {sender="V", receiver="P", site="challenge"} : !algebra.field<"bls12-381.fr">
      %sum = algebra.field_add %state, %sent : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "protocol.yield"(%sum) : (!algebra.field<"bls12-381.fr">) -> ()
    }) {site="inner", carried=1:i64, maximum=8:i64, roles=["P", "V"], carried_roles=[["P"]]} : (ui64, !algebra.field<"bls12-381.fr">, i1, !protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
      "protocol.yield"(%next) : (!algebra.field<"bls12-381.fr">) -> ()
    }) {site="outer", carried=1:i64, maximum=8:i64, roles=["P", "V"], carried_roles=[["P"]]} : (ui64, !algebra.field<"bls12-381.fr">, i1, !protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
    "protocol.return"(%out) : (!algebra.field<"bls12-381.fr">) -> ()
  }) {sym_name="main", function_type=(ui64, i1, !protocol.service_ref<"random.bls12-381.fr/0">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">, roles=["P", "V"], input_roles=[["P"], ["V"], ["V"], ["P"]], output_roles=[["P"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> ()
}
