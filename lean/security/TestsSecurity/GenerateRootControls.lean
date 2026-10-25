import ZkcSecurity.Generation.Roots.Catalogue
import ZkcSecurity.Generation.SigmaCompleteness
import ZkcSecurity.Generation.SubjectABI

/-! Controls for generation refusals; no root configuration is owned by tests. -/
namespace TestsSecurity.GenerateRootControls
open Zkc.Source.Structured ZkcSecurity.Generation.Roots
open ZkcTools.StructuredSource.Root

private meta def refuses {α : Type} (code : String) (result : Except String α) :
    Lean.Elab.Command.CommandElabM Unit :=
  match result with
  | .error actual => unless actual == code do Lean.throwError m!"expected {code}, got {actual}"
  | .ok _ => Lean.throwError m!"generation accepted invalid input: {code}"

run_cmd do
  for ty in [Ty.sequence .boolean, Ty.product "query" "Query" (.cons .boolean .nil)] do
    refuses "uniform-root-aggregate-type" (ZkcSecurity.Generation.UniformRoot.carrier ty)
    refuses "sigma-completeness-aggregate-type" (ZkcSecurity.Generation.SigmaCompleteness.zeroInput ty)
    refuses "subject-abi-aggregate-type" (ZkcSecurity.Generation.SubjectABI.encoded ty "value")
  let [first, _] ← evaluateSelections | Lean.throwError "expected two production roots"
  let some definition := first.snapshot.definitions.find? (fun
    | .function function => function.kind == .local
    | _ => false) | Lean.throwError "missing local helper control"
  let .function function := definition | Lean.throwError "not a helper"
  let replace := fun replacement => { first.snapshot with
    definitions := first.snapshot.definitions.map fun retained =>
      if retained.name == function.name then .function replacement else retained }
  refuses "root-missing-helper-origin" (sourceAliases (replace { function with origin := none }) first.helpers)
  refuses "root-malformed-helper-origin" (sourceAliases (replace { function with origin := some ("", []) }) first.helpers)
  refuses "root-malformed-helper-origin" (sourceAliases
    (replace { function with origin := some ("helper", [("n", "1"), ("n", "2")]) }) first.helpers)
  refuses "root-helper-origin-association" (sourceAliases first.snapshot [])
  refuses "root-ambiguous-helper-origin" (sourceAliases
    { first.snapshot with definitions := first.snapshot.definitions ++ [definition] } first.helpers)
  refuses "root-unlabelled-charge-site" (sourceLabel "s0")
  for malformed in ["label_0", "label_gg", "label_ff", "label_", "label_612e62"] do
    refuses "root-malformed-charge-label" (sourceLabel malformed)
  refuses "root-missing-charge-origin" (chargeLabels
    { first with artifacts.validator.instructions := [] })
  let [occurrence] := ZkcSecurity.Claims.Domain.challengeOccurrences first.artifacts.validator.instructions
    | Lean.throwError "expected one challenge control"
  refuses "root-charge-origin" (chargeLabels { first with artifacts.validator.instructions := [
    ⟨.challenge occurrence.suite occurrence.field { occurrence.template with event := [] }, [], [], []⟩] })
  refuses "root-missing-policy-table" (inputPolicy { first with honestInputs.width := 0 })
  refuses "root-ambiguous-policy-bound" (inputPolicy { first with
    artifacts.producer.instructions := [], artifacts.validator.instructions := [] })
  for root in ← evaluateSelections do
    let .ok aliases := sourceAliases root.snapshot root.helpers | Lean.throwError "valid aliases refused"
    let .ok permuted := sourceAliases root.snapshot root.helpers.reverse | Lean.throwError "permuted aliases refused"
    unless aliases.map sourceAliasName == permuted.map sourceAliasName do
      Lean.throwError "source alias names depend on helper positions"
    let .ok _ := chargeLabels root | Lean.throwError "valid charges refused"
    let .ok _ := inputPolicy root | Lean.throwError "valid policy refused"
  Lean.logInfo "PASS production generation origin, label, association and policy controls"

end TestsSecurity.GenerateRootControls
