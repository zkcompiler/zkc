import Tools.Interactive.ReferenceValue

/-! Typed local execution of authenticated row contracts. Ownership and transport
are handled by the surrounding protocol interpreter, not by the Merkle tree. -/
set_option autoImplicit false
namespace Tools.Interactive.Reference

private def index (value : Value) : Result Nat := do
  let .index n ← value.toArithmetic .bls | throw "oracle-operands"
  return n
private def indexValue (n : Nat) : Value := Value.fromArithmetic .bls (.index n)
private def rowValue (domain : OracleReference.Domain) (wire : ByteArray) : Result Value :=
  if domain == .base then Value.fromArithmetic .koalaBear <$> Tools.Artifact.decodeArithmeticWire .koalaBear "vector" wire
  else Value.fromExtension <$> Tools.Artifact.decodeExtensionWire "vector" wire

/-- Domain equality is checked at the typed request boundary; collection entries
are immutable and receive their domain only through commit/append or wire decode. -/
def oracleCompute (name scheme : String) (inputs : List Value) : Result (List Value) := do
  let domain ← OracleReference.Domain.parse scheme
  match name, inputs with
  | "oracle.commit", [vector, width] =>
      let state ← OracleReference.commit domain (← index width) (← vector.wire)
      return [.oracle (.root domain state.root), .oracle (.state state)]
  | "oracle.open", [.oracle (.state state), coordinate] =>
      let (wire, path) ← state.open (← index coordinate)
      return [← rowValue domain wire, .oracle (.path domain path)]
  | "oracle.check", [.oracle (.root _ root), width, height, coordinate, vector, .oracle (.path _ path)] =>
      return [.boolean (← OracleReference.verify domain root (← index width) (← index height)
        (← index coordinate) (← vector.wire) path)]
  | "commitments.empty", [] => return [.oracle (.roots domain [])]
  | "opening_states.empty", [] => return [.oracle (.states domain [])]
  | "commitments.append", [.oracle (.roots _ roots), .oracle (.root _ root)] =>
      ensure (roots.length < 2^20) "oracle-element-limit"
      return [.oracle (.roots domain (roots ++ [root]))]
  | "opening_states.append", [.oracle (.states _ states), .oracle (.state state)] =>
      ensure (states.length < 2^20) "oracle-element-limit"
      return [.oracle (.states domain (states ++ [state]))]
  | "commitments.at", [.oracle (.roots _ roots), coordinate] =>
      let some root := roots[← index coordinate]? | throw "oracle-coordinate"
      return [.oracle (.root domain root)]
  | "opening_states.at", [.oracle (.states _ states), coordinate] =>
      let some state := states[← index coordinate]? | throw "oracle-coordinate"
      return [.oracle (.state state)]
  | "commitments.length", [.oracle (.roots _ roots)] => return [indexValue roots.length]
  | "opening_states.length", [.oracle (.states _ states)] => return [indexValue states.length]
  | _, _ => throw "oracle-operands"
end Tools.Interactive.Reference
