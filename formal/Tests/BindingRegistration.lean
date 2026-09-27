import Tools.Interactive.Explicit
import Tests.Checks

/-! Finite controls for independently assembled binding interpretations. These
checks cover local registration and carrier admission, not cross-reader or
execution conformance. Run with `lake build Tests.BindingRegistration`. -/

set_option autoImplicit false

namespace Tests.BindingRegistration
open Tools.Interactive Tools.Interactive.Bindings
open Lean (Json)

private def get {α : Type} (result : Result α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def code {α : Type} : Result α → Option String
  | .ok _ => none
  | .error error => some error

private def agrees {α : Type} [BEq α] : Result α → Result α → Bool
  | .ok left, .ok right => left == right
  | .error left, .error right => left == right
  | _, _ => false

private def ports (result : Result Signature) : Result (List String × List String) := do
  let signature ← result
  return (signature.inputs.map (·.spelling), signature.outputs.map (·.spelling))

private def declarationJson (binding : Declaration) : Json :=
  .arr #[.str binding.name, .str binding.contract, Lean.toJson binding.arguments, .str binding.implementation]

private def common (bindings : List Declaration) : Result Explicit.Module :=
  Explicit.common (.arr #[.str "zkc.protocol/1", .arr (bindings.map declarationJson).toArray,
    .arr #[], .arr #[], .arr #[], .arr #[]])

private def candidate (bindings : List Declaration) : Result Explicit.CandidateLocals :=
  Explicit.candidateLocals (.arr #[.str "zkc.participants/1", .arr (bindings.map declarationJson).toArray,
    .str "physical", .arr #[], .arr #[], .arr #[]])

/-- Change only one full-type resolver. Its name and generic shape are unchanged,
so comparing inventories or generic shapes cannot detect this disagreement. -/
private def divergent (contribution : Contribution) : Contribution :=
  ⟨contribution.operations.map fun operation =>
    if operation.contract == "field.add" then
      { operation with resolve := fun physical binding => do
          let signature ← operation.resolve physical binding
          return { signature with outputs :=
            [ValueType.mk "bool" "" (if physical then "native.bool/1" else "")] } }
    else operation⟩

def run : IO Unit := do
  let checks ← Tests.Checks.start
  let installed ← get installation
  for kind in ["bool", "index", "indices"] do
    let contract := "transcript.observe." ++ kind
    for (transcript, provider) in [(transcriptIdentity, "arkworks"),
        (ristrettoTranscript, "dalek"), (spongefishTranscript, "spongefish"),
        (extensionTranscript, "plonky3")] do
      let name := provider ++ "/" ++ contract
      checks.holds (implementationName contract name &&
        (resolve false ⟨"observe", contract, [transcript, codec kind ""], name⟩).isOk)
        ("domain-independent observation partial selection: " ++ name)
  let field ← get (installed.operation "field.add")
  let unregistered ← get (assemble [⟨[{ field with implementations := [] }]⟩])
  checks.holds (code (unregistered.resolve true ⟨"add", "field.add", [fr],
      "arkworks/field.add"⟩) == some "binding-implementation")
    "a permissive resolver cannot bypass implementation registration"
  checks.holds (code (assemble [⟨[{ field with implementations := ["same", "same"] }]⟩]) ==
      some "binding-implementation-registration") "duplicate implementation names refuse"
  checks.holds (!implementationName "missing" "arkworks/missing" &&
    !implementationName "field.add" "uninstalled/add") "unknown partial selections refuse"
  let reversed ← get (assemble contributions.reverse)
  let empty ← get (assemble [])
  checks.holds (code (empty.resolve false ⟨"missing", "field.add", [fr], ""⟩) == some "binding-contract")
    "an omitted domain is not recovered by fallback dispatch"
  checks.holds (code (assemble [Field.contribution, Field.contribution]) == some "binding-duplicate-contract")
    "duplicate contract ownership refuses during assembly"
  checks.holds (code (assemble [Field.contribution, divergent Field.contribution]) == some "binding-duplicate-contract" &&
    code (assemble [divergent Field.contribution, Field.contribution]) == some "binding-duplicate-contract")
    "registration order cannot select a conflicting interpretation"
  for contract in ["field.unknown", "oracle.unknown", "fixed_vector.unknown", "resource_unit.unknown",
      "transcript.observe.fixed_vector", "external.openvm.unknown"] do
    checks.holds (code (resolve true ⟨"unknown", contract, [], "unknown"⟩) == some "binding-contract")
      ("exact installed membership: " ++ contract)
  for contract in ["table.relayout", "resource_unit.create", "resource_unit.pass", "resource_unit.consume"] do
    checks.holds (code (shape contract) == some "binding-contract")
      ("generic shape API retains its omission: " ++ contract)

  -- One independently expected complete signature for each contributed domain.
  let cases : List (Declaration × List String × List String) := [
    (⟨"field", "field.add", [fr], "arkworks/field.add"⟩,
      ["field:bls12-381.fr@arkworks.fr/1", "field:bls12-381.fr@arkworks.fr/1"], ["field:bls12-381.fr@arkworks.fr/1"]),
    (⟨"vector", "vector.dot", [fr], "arkworks-diagonal/vector.dot"⟩,
      ["vector:bls12-381.fr@arkworks.fr-vector/1", "vector:bls12-381.fr@arkworks.fr-diagonal/1"], ["field:bls12-381.fr@arkworks.fr/1"]),
    (⟨"matrix", "matrix.shape_check", [koalaBear], "plonky3/matrix.shape_check"⟩,
      ["matrix:koala-bear@plonky3.koala-bear-sparse-coo/1"], ["bool@native.bool/1"]),
    (⟨"poly", "poly.fold", [fr], "arkworks-msb/poly.fold"⟩,
      ["table:bls12-381.fr@arkworks.mle-msb/1", "field:bls12-381.fr@arkworks.fr/1"], ["table:bls12-381.fr@arkworks.mle-msb/1"]),
    (⟨"curve", "curve.scale_each", [ristrettoGroup], "dalek-diagonal/curve.scale_each"⟩,
      ["vector:ristretto255.scalar@dalek.scalar-vector/1", "groups:ristretto255.group@dalek.ristretto-vector/1"],
      ["groups:ristretto255.group@dalek.ristretto-diagonal/1"]),
    (⟨"pairing", "pairing.check", [bn254Fr], "arkworks/pairing.check"⟩,
      ["groups:bn254.g1@arkworks.bn254-g1-vector/1", "groups:bn254.g2@arkworks.bn254-g2-vector/1"], ["bool@native.bool/1"]),
    (⟨"pcs", "pcs.equal", [pcs], "arkworks/pcs.equal"⟩,
      ["commitment:multilinear.kzg.bls12-381/1@arkworks.multilinear-pcs/1",
       "commitment:multilinear.kzg.bls12-381/1@arkworks.multilinear-pcs/1"], ["bool@native.bool/1"]),
    (⟨"oracle", "commitments.length", [rowBase], "plonky3/commitments.length"⟩,
      ["commitments:rows.merkle-keccak256.koala-bear/1@plonky3.merkle-roots/1"], ["index@native.index/1"]),
    (⟨"random", "random.index", [koalaBearExt8], "plonky3/random.index"⟩,
      ["rng:koala-bear.ext8-binomial3@host.resource/1", "index@native.index/1"],
      ["index@native.index/1", "rng:koala-bear.ext8-binomial3@host.resource/1"]),
    (⟨"transcript", "transcript.challenge", [spongefishTranscript], "spongefish/transcript.challenge"⟩,
      ["transcript:spongefish0.7.4.keccak.bls12-381.fr64be/1@host.resource/1"],
      ["field:bls12-381.fr@arkworks.fr/1", "transcript:spongefish0.7.4.keccak.bls12-381.fr64be/1@host.resource/1"]),
    (⟨"native", "index.equal", [], "native/index.equal"⟩,
      ["index@native.index/1", "index@native.index/1"], ["bool@native.bool/1"]),
    (⟨"external", "external.openvm.sample", [], "native/external.openvm.sample"⟩,
      ["indices@native.indices/1"], ["indices@native.indices/1", "index@native.index/1"]),
    (⟨"fixed", "fixed_vector.from_vector", [koalaBear, "4"], "plonky3/fixed_vector.from_vector"⟩,
      ["vector:koala-bear@plonky3.koala-bear-vector/1"], ["fixed_vector<field:koala-bear,4>@plonky3.fixed-vector/1"]),
    (⟨"resource", "resource_unit.pass", ["Trace"], "logical/resource_unit.pass"⟩,
      ["resource_unit:Trace@logical.resource_unit/1"], ["resource_unit:Trace@logical.resource_unit/1"]),
    (⟨"table", "table.relayout", [fr, "arkworks.mle-lsb/1", "arkworks.mle-msb/1"], "arkworks/table.relayout"⟩,
      ["table:bls12-381.fr@arkworks.mle-lsb/1"], ["table:bls12-381.fr@arkworks.mle-msb/1"])]
  for (binding, inputs, outputs) in cases do
    checks.holds ((ports (resolve true binding)).toOption == some (inputs, outputs)) ("physical signature: " ++ binding.contract)
    checks.holds (agrees (installed.resolve true binding) (reversed.resolve true binding))
      ("order-independent resolution: " ++ binding.contract)
    if binding.contract != "table.relayout" then
      let logical := fun (port : String) => (port.splitOn "@").head!
      checks.holds ((ports (resolve false binding)).toOption == some (inputs.map logical, outputs.map logical))
        ("selected implementation retains logical ports: " ++ binding.contract)

  -- Multiple-invalid-input cases freeze the public refusal order.
  let refusals : List (Bool × Declaration × String) := [
    (false, ⟨"adapter", "table.relayout", [], "bad"⟩, "binding-adapter-at-logical-stage"),
    (true, ⟨"adapter", "table.relayout", [], "bad"⟩, "binding-implementation"),
    (true, ⟨"adapter", "table.relayout", [], "arkworks/table.relayout"⟩, "binding-static-arity"),
    (true, ⟨"field", "field.add", [], "bad"⟩, "binding-static-arity"),
    (true, ⟨"field", "field.add", ["unknown"], "bad"⟩, "binding-static-arguments"),
    (true, ⟨"fold", "poly.fold", [koalaBear], "bad"⟩, "binding-domain-not-supported"),
    (true, ⟨"coset", "poly.coset_evaluate", [fr], "bad"⟩, "binding-two-adic-field"),
    (true, ⟨"embed", "field.embed", [koalaBear], "bad"⟩, "binding-associated-identity"),
    (true, ⟨"oracle", "oracle.open", [rowBase], "bad"⟩, "binding-static-arguments"),
    (true, ⟨"fixed", "fixed_vector.dot", [koalaBear, "04"], "bad"⟩, "binding-type-natural"),
    (true, ⟨"fixed", "fixed_vector.dot", [fr, "4"], "plonky3/fixed_vector.dot"⟩, "binding-implementation"),
    (true, ⟨"resource", "resource_unit.pass", [""], "bad"⟩, "binding-resource-unit-domain"),
    (true, ⟨"random", "random.index", [fr], "bad"⟩, "binding-index-randomness"),
    (true, ⟨"transcript", "transcript.draw_index", [transcriptIdentity], "bad"⟩, "binding-index-transcript")]
  for (physical, binding, expected) in refusals do
    checks.holds (code (resolve physical binding) == some expected) ("refusal order: " ++ binding.contract ++ ": " ++ expected)

  let fixed : Declaration := ⟨"unused", "fixed_vector.dot", [fr, "4"], ""⟩
  checks.holds ((resolve false fixed).isOk && code (resolve true fixed) == some "binding-implementation")
    "logical admission does not supply physical support"
  let observation : Declaration := ⟨"unused", "transcript.observe.field",
    [extensionTranscript, bn254Fr, codec "field" bn254Fr], ""⟩
  checks.holds ((resolve false observation).isOk &&
    code (resolve false {observation with implementation := "plonky3/transcript.observe.field"}) == some "binding-static-arguments")
    "codec-valid logical observation does not imply provider support"
  checks.holds (implementationName "fixed_vector.dot" "plonky3/fixed_vector.dot" &&
    !implementationName "fixed_vector.unknown" "plonky3/fixed_vector.unknown")
    "partially configured implementation names remain exact"

  let retained ← get (common [fixed, {fixed with name := "also_unused"}])
  checks.holds (retained.source.environment == .explicit [fixed, {fixed with name := "also_unused"}])
    "unused logical declarations and declaration names are retained in order"
  checks.holds (code (common [fixed, ⟨"unknown", "field.unknown", [], ""⟩]) == some "binding-contract")
    "unused unknown source binding is still resolved"
  checks.holds (code (common [{fixed with implementation := "plonky3/fixed_vector.dot"}]) == some "binding-implementation")
    "unused logical declaration checks explicit implementation eligibility"
  let some (physical, _, _) := cases.head? | throw (IO.userError "missing physical test binding")
  let physicalRetained ← get (candidate [physical])
  checks.holds (physicalRetained.bindings == [physical]) "unused physical declaration is retained"
  checks.holds (code (candidate [physical, {fixed with implementation := "plonky3/fixed_vector.dot"}]) == some "binding-implementation")
    "unused unsupported physical binding is still refused"

  let changed ← get (assemble (contributions.map divergent))
  let binding : Declaration := ⟨"addition", "field.add", [fr], "arkworks/field.add"⟩
  checks.holds (changed.operations.size == installed.operations.size && agrees (changed.shape "field.add") (installed.shape "field.add"))
    "divergent resolver preserves inventory and generic shape"
  for physical in [false, true] do
    let expected ← get (installed.resolve physical binding)
    let actual ← get (changed.resolve physical binding)
    checks.holds (actual.inputs == expected.inputs && actual.outputs != expected.outputs &&
      (actual.inputs ++ actual.outputs).all (·.valid physical))
      "complete signature comparison detects a valid but divergent resolver output"
  checks.holds (agrees (changed.resolve true ⟨"multiply", "field.mul", [fr], "arkworks/field.mul"⟩)
    (installed.resolve true ⟨"multiply", "field.mul", [fr], "arkworks/field.mul"⟩))
    "divergence fixture changes exactly the selected resolver"
  checks.finish "Lean domain binding registration"

end Tests.BindingRegistration

#eval Tests.BindingRegistration.run
