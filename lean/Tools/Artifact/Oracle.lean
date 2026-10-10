import Tools.Artifact.Bindings
import Tools.Interactive.ReferenceOracle

/-! The artifact evaluator uses the same mathematical row contract as interactive
source execution. It does not call the native Merkle provider. -/
set_option autoImplicit false
namespace Tools.Artifact
open Tools.Interactive

private def input : Value → Result Reference.Value
  | .oracle value => .ok (.oracle value)
  | .extension value => .ok (Reference.Value.fromExtension value)
  | .arithmetic d value => .ok (Reference.Value.fromArithmetic d value)
  | .boolean value => .ok (.boolean value)
  | _ => .error "oracle-operands"
private def output : Reference.Value → Result Value
  | .oracle value => .ok (.oracle value)
  | .extension value => .ok (Value.fromExtension value)
  | .arithmetic d value => .ok (Value.fromArithmetic d value)
  | .boolean value => .ok (.boolean value)
  | _ => .error "oracle-results"

def oracleCompute (name scheme : String) (values : List Value) : Result (List Value) := do
  (← Reference.oracleCompute name scheme (← values.mapM input)).mapM output
end Tools.Artifact
