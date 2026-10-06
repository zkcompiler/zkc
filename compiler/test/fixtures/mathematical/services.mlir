module {
"protocol.module"() ({
  relation.declare @relation {kind="external", key="example/service-output", revision="1", signature=(!algebra.field<"bls12-381.fr">, i1) -> i1, purposes=["statement", "statement"]}
  "protocol.func"() ({
  ^entry(%first: !protocol.service_ref<"random.bls12-381.fr/1">,
         %x: !algebra.field<"bls12-381.fr">, %go: i1,
         %second: !protocol.service_ref<"random.bls12-381.fr/1">,
         %accept: i1, %observer: i1):
    protocol.statement @relation(%x, %accept) {selectors=["Alice", "Bob"], acceptance=1 : i64} : !algebra.field<"bls12-381.fr">, i1
    %twice = algebra.field_add %x, %x : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
    protocol.guard %go {owner="Alice", site="before_query"}
    %a = "protocol.query"(%first) {method="draw", owner="Alice", site="first_draw"} : (!protocol.service_ref<"random.bls12-381.fr/1">) -> !algebra.field<"bls12-381.fr">
    %middle = algebra.field_add %twice, %a : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
    %b = "protocol.query"(%second) {method="draw", owner="Alice", site="second_draw"} : (!protocol.service_ref<"random.bls12-381.fr/1">) -> !algebra.field<"bls12-381.fr">
    %sum = algebra.field_add %middle, %b : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
    %unused = "protocol.query"(%first) {method="draw", owner="Alice", site="unused_draw"} : (!protocol.service_ref<"random.bls12-381.fr/1">) -> !algebra.field<"bls12-381.fr">
    %message = protocol.exchange %sum {sender="Alice", receiver="Bob", site="result"} : !algebra.field<"bls12-381.fr">
    "protocol.return"(%message, %accept) : (!algebra.field<"bls12-381.fr">, i1) -> ()
  }) {sym_name="main",
      function_type=(!protocol.service_ref<"random.bls12-381.fr/1">, !algebra.field<"bls12-381.fr">, i1, !protocol.service_ref<"random.bls12-381.fr/1">, i1, i1) -> (!algebra.field<"bls12-381.fr">, i1),
      roles=["Alice", "Bob", "Observer"], input_roles=[["Alice"], ["Alice"], ["Alice"], ["Alice"], ["Bob"], ["Observer"]], output_roles=[["Alice", "Bob"], ["Bob"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> ()
}
