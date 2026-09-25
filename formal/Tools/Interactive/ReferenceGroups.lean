import Tools.Interactive.ReferenceState

/-! Finite group-sequence structure is executed here; point decoding, subgroup
membership and group equations belong to exact typed primitive requests.
No byte predicate is promoted to a proof of a Ristretto point. -/

set_option autoImplicit false

namespace Tools.Interactive.Reference

private def groupWidth (identity : String) : Result Nat :=
  if identity == Bindings.g1 then .ok 48
  else if identity == Bindings.ristrettoGroup || identity == Bindings.bn254G1 then .ok 32
  else if identity == Bindings.bn254G2 then .ok 64
  else .error "group-domain"

def groupWire (value : Value) : Result ByteArray := do
  let bytes ← value.wire
  if value.ty.identity == Bindings.g1 then
    let _ ← Tools.Artifact.decodeWire value.ty.kind bytes
  else if value.ty.identity == Bindings.ristrettoGroup then
    Tools.Artifact.checkRistrettoWire value.ty.kind bytes
  else Tools.Artifact.checkBn254Wire value.ty.identity value.ty.kind bytes
  return bytes

def groupCount (value : Value) : Result Nat := do
  ensure (value.ty.kind == "groups") "group-kind"
  return Tools.Artifact.valueLE ((← groupWire value).extract 6 10)

private def groupValue (identity kind : String) (payload : ByteArray) : Result Value := do
  let _ ← groupWidth identity
  let tag : UInt8 ← if identity == Bindings.bn254G1 || identity == Bindings.bn254G2 then
      Tools.Artifact.bn254GroupTag identity kind
    else pure (if identity == Bindings.g1 then (if kind == "group" then 9 else 10)
    else (if kind == "group" then 16 else 17))
  let bytes := Tools.Artifact.magic.push tag ++ payload
  let value := if identity == Bindings.bn254G1 || identity == Bindings.bn254G2 then
      Value.bnGroup (identity == Bindings.bn254G2) (kind == "groups") bytes
    else if identity == Bindings.g1 then
      if kind == "group" then Value.group bytes else .groups bytes
    else if kind == "group" then .rgroup bytes else .rgroups bytes
  let _ ← groupWire value
  return value

/-- Pure sequence structure is bounded independently of the service. An MSM or
coordinatewise action never receives mismatched lengths. -/
def groupCompute (location : Location) (contract identity : String) (attrs : List String)
    (inputs : List Value) : RunM (List Value) := do
  let width ← checked location (groupWidth identity)
  let count := fun value => checked location (groupCount value)
  let bytes := fun value => checked location (groupWire value)
  let make := fun kind payload => checked location (groupValue identity kind payload)
  let sequence := fun n payload => make "groups" (Tools.Artifact.little 4 n ++ payload)
  let payload := fun value => do
    let wire ← bytes value
    pure (wire.extract (if value.ty.kind == "groups" then 10 else 6) wire.size)
  let mut expectedCount : Option Nat := none
  match contract, inputs with
  | "curve.empty", [] => return [← sequence 0 ByteArray.empty]
  | "curve.append", [xs, x] =>
      let n ← count xs
      require location (n < 4096) "group-limit"
      return [← sequence (n + 1) ((← payload xs) ++ (← payload x))]
  | "curve.at", [xs] =>
      let [index] := attrs | failAt location "refused" "kernel-attributes"
      let i ← checked location (Decode.natural (.str index))
      require location (i < (← count xs)) "group-index"
      return [← make "group" ((← payload xs).extract (i * width) ((i + 1) * width))]
  | "curve.get", [xs, index] =>
      let .index i ← checked location (index.toArithmetic .bls)
        | failAt location "refused" "runtime-kernel-types"
      require location (i < (← count xs)) "group-index"
      return [← make "group" ((← payload xs).extract (i * width) ((i + 1) * width))]
  | "curve.length", [xs] =>
      return [Value.fromArithmetic .bls (.index (← count xs))]
  | "curve.split", [xs] =>
      let n ← count xs
      require location (n > 0 && n % 2 == 0) "group-split-shape"
      let data ← payload xs
      return [← sequence (n / 2) (data.extract 0 (n / 2 * width)),
        ← sequence (n / 2) (data.extract (n / 2 * width) data.size)]
  | "curve.concat", [xs, ys] =>
      let n := (← count xs) + (← count ys)
      require location (n ≤ 4096) "group-limit"
      return [← sequence n ((← payload xs) ++ (← payload ys))]
  | "curve.msm", [scalars, bases] | "curve.scale_each", [scalars, bases] =>
      let d ← checked location (ScalarReference.Domain.parse (← checked location (Bindings.associatedIdentity identity "Scalar")))
      let .vector xs ← checked location (scalars.toArithmetic d)
        | failAt location "refused" "runtime-kernel-types"
      let n ← count bases
      require location (xs.length == n) "vector-shape"
      if contract == "curve.scale_each" then expectedCount := some n
  | "curve.vector_add", [xs, ys] =>
      let n ← count xs
      require location (n == (← count ys)) "vector-shape"
      expectedCount := some n
  | "curve.vector_scale", [xs, _] => expectedCount := some (← count xs)
  | "curve.generator", [] | "curve.add", [_, _] | "curve.scale", [_, _]
  | "curve.neg", [_] | "curve.nonidentity", [_] | "curve.equal", [_, _] => pure ()
  | _, _ => failAt location "refused" "reference-group-contract"
  for value in inputs do
    if value.ty.kind == "group" || value.ty.kind == "groups" then
      let _ ← bytes value
  let outputs ← external location contract [identity] attrs inputs
  let signature ← checked location (Bindings.resolve false ⟨"", contract, [identity], ""⟩)
  require location (outputs.map Value.ty == signature.outputs) "runtime-kernel-results"
  if let some n := expectedCount then
    let [result] := outputs | failAt location "refused" "runtime-kernel-results"
    require location ((← count result) == n) "group-count"
  return outputs

end Tools.Interactive.Reference
