import Tools.Interactive.Bindings.Field
import Tools.Interactive.Bindings.Vector
import Tools.Interactive.Bindings.Matrix
import Tools.Interactive.Bindings.Polynomial
import Tools.Interactive.Bindings.Curve
import Tools.Interactive.Bindings.Pairing
import Tools.Interactive.Bindings.Commitment
import Tools.Interactive.Bindings.Oracle
import Tools.Interactive.Bindings.Random
import Tools.Interactive.Bindings.Transcript
import Tools.Interactive.Bindings.Native
import Tools.Interactive.Bindings.External
import Tools.Interactive.Bindings.FixedVector
import Tools.Interactive.Bindings.ResourceUnit
import Tools.Interactive.Bindings.Table

/-! The independently authored finite binding installation. Domain modules own
exact operation signatures and physical eligibility; this file selects them
explicitly. Admission is separate from reference execution and theorem support. -/

set_option autoImplicit false

namespace Tools.Interactive.Bindings

/-- Build-time selection of domain contributions; carrier data cannot extend it. -/
def contributions : List Contribution :=
  [Field.contribution, Vector.contribution, Matrix.contribution, Polynomial.contribution,
   Curve.contribution, Pairing.contribution, Commitment.contribution, Oracle.contribution,
   Random.contribution, Transcript.contribution, Native.contribution, External.contribution,
   FixedVector.contribution, ResourceUnit.contribution, Table.contribution]

/-- Assemble once and refuse duplicate ownership before resolving any contract. -/
def installation : Result Installation := assemble contributions

/-- The existing generic shape API, including its intentional omissions. -/
def shape (contract : String) : Result (List String × List String) := do
  (← installation).shape contract

/-- Resolve an explicit contract independently. Implementation eligibility is
checked even at logical stages, while their ports retain logical types. -/
def resolve (physical : Bool) (binding : Declaration) : Result Signature := do
  (← installation).resolve physical binding

/-- Positive classification of the installed mathematical subset. Signature
resolution and its nominal domain checks are still required. This flag is an
admission fact; operation interpretations supply the totality laws. -/
def totalContract (contract : String) : Bool :=
  ["field.add", "field.mul", "field.from_nonzero", "curve.generator",
   "curve.add", "curve.scale", "curve.equal"].contains contract

/-- Independently installed nullary entropy services. Ordinary operation
formation does not grant permission to use arbitrary kernels as root services. -/
def entropyService (binding : Declaration) : Result (ValueType × ValueType) := do
  ensure (binding.implementation.isEmpty &&
    ["random.draw", "random.draw_nonzero"].contains binding.contract) "entropy-service-contract"
  let signature ← resolve false binding
  let [state] := signature.inputs | throw "entropy-service-signature"
  let [reply, successor] := signature.outputs | throw "entropy-service-signature"
  ensure (state.kind == "rng" && state == successor) "entropy-service-signature"
  return (state, reply)

/-- Finite implementation names for a partially configured definition. Exact
nominal applicability is checked again by resolve at specialization. -/
def implementationName (contract implementation : String) : Bool :=
  match installation >>= (·.operation contract) with
  | .ok operation => operation.implementations.contains implementation
  | .error _ => false

end Tools.Interactive.Bindings
