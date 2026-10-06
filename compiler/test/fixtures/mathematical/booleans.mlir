module {
"protocol.module"() ({
  func.func private @invert(%a: i1) -> i1 {
    %true = arith.constant true
    %not = arith.xori %a, %true : i1
    return %not : i1
  }
  "protocol.func"() ({
  ^entry(%a: i1, %b: i1, %c: i1, %x: !algebra.field<"bls12-381.fr">, %y: !algebra.field<"bls12-381.fr">, %g: !algebra.group<"bls12-381.g1">, %h: !algebra.group<"bls12-381.g1">):
    %true = arith.constant true
    %false = arith.constant false
    %and = arith.andi %a, %b : i1
    %or = arith.ori %a, %b : i1
    %xor = arith.xori %a, %b : i1
    %eq = arith.cmpi eq, %a, %b : i1
    %ne = arith.cmpi ne, %a, %b : i1
    %not = func.call @invert(%a) : (i1) -> i1
    %bool = arith.select %c, %a, %b : i1
    %field = arith.select %c, %x, %y : !algebra.field<"bls12-381.fr">
    %group = arith.select %c, %g, %h : !algebra.group<"bls12-381.g1">
    "protocol.return"(%true, %false, %and, %or, %xor, %eq, %ne, %not, %bool, %field, %group) : (i1, i1, i1, i1, i1, i1, i1, i1, i1, !algebra.field<"bls12-381.fr">, !algebra.group<"bls12-381.g1">) -> ()
  }) {sym_name="main", function_type=(i1, i1, i1, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">) -> (i1, i1, i1, i1, i1, i1, i1, i1, i1, !algebra.field<"bls12-381.fr">, !algebra.group<"bls12-381.g1">), roles=["P"], input_roles=[["P"], ["P"], ["P"], ["P"], ["P"], ["P"], ["P"]], output_roles=[["P"], ["P"], ["P"], ["P"], ["P"], ["P"], ["P"], ["P"], ["P"], ["P"], ["P"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> ()
}
