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
    unless (ZkcSecurity.Generation.UniformRoot.carrier ty).contains
        (ZkcTools.StructuredSource.Constructed.literal ty) do
      Lean.throwError "uniform presentation erased the nominal aggregate type"
    refuses "sigma-completeness-aggregate-type" (ZkcSecurity.Generation.SigmaCompleteness.zeroInput ty)
    let .ok encoded := ZkcSecurity.Generation.SubjectABI.encoded ty "value"
      | Lean.throwError "subject ABI refused data aggregate"
    unless encoded.contains (ZkcTools.StructuredSource.Constructed.literal ty) do
      Lean.throwError "subject ABI erased nominal data type"
  for ty in [Ty.service "rng", Ty.sequence (.service "rng"),
      Ty.product "opaque" "Opaque" (.cons (.service "rng") .nil)] do
    refuses "subject-abi-service-projection" (ZkcSecurity.Generation.SubjectABI.encoded ty "value")
  let [first, _] ← evaluateSelections | Lean.throwError "expected two production roots"
  let some definition := first.snapshot.definitions.find? (fun
    | .function function => function.kind == .local
    | _ => false) | Lean.throwError "missing local helper control"
  let .function function := definition | Lean.throwError "not a helper"
  let replace := fun replacement => { first.snapshot with
    definitions := first.snapshot.definitions.map fun retained =>
      if retained.name == function.name then .function replacement else retained }
  refuses "root-missing-helper-origin" (sourceAliases (replace { function with origin := none }) first.helpers)
  refuses "root-malformed-helper-origin" (sourceAliases (replace { function with origin := some (.local "" []) }) first.helpers)
  refuses "root-malformed-helper-origin" (sourceAliases
    (replace { function with origin := some (.local "helper" [("n", "1"), ("n", "2")]) }) first.helpers)
  let some (.function protocol) := first.snapshot.definitions.find? (fun
    | .function retained => retained.kind == .protocol
    | _ => false) | Lean.throwError "missing protocol origin control"
  let some (.protocol origin) := protocol.origin | Lean.throwError "missing typed protocol origin"
  let replaceProtocol := fun replacement => { first.snapshot with
    definitions := first.snapshot.definitions.map fun retained =>
      if retained.name == protocol.name then .function replacement else retained }
  refuses "root-missing-helper-origin" (sourceAliases
    (replaceProtocol { protocol with origin := none }) first.helpers)
  refuses "root-malformed-helper-origin" (sourceAliases
    (replaceProtocol { protocol with origin := some (.protocol { origin with path := "" }) }) first.helpers)
  refuses "root-malformed-helper-origin" (sourceAliases
    (replaceProtocol { protocol with origin := some (.local origin.path []) }) first.helpers)
  refuses "root-malformed-helper-origin" (sourceAliases
    (replace { function with origin := some (.protocol origin) }) first.helpers)
  refuses "root-malformed-helper-origin" (sourceAliases
    (replaceProtocol { protocol with origin := some (.protocol
      { origin with arguments := [("n", .natural "1"), ("n", .natural "2")] }) }) first.helpers)
  refuses "root-ambiguous-helper-origin" (sourceAliases
    { first.snapshot with definitions := first.snapshot.definitions ++ [.function protocol] } first.helpers)
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
  for root in ← evaluateSelections do
    let .ok aliases := sourceAliases root.snapshot root.helpers | Lean.throwError "valid aliases refused"
    let .ok permuted := sourceAliases root.snapshot root.helpers.reverse | Lean.throwError "permuted aliases refused"
    unless aliases.map sourceAliasName == permuted.map sourceAliasName do
      Lean.throwError "source alias names depend on helper positions"
    let .ok program := check root.snapshot | Lean.throwError "valid protocol source refused"
    let protocols := aliases.filter fun candidate => match candidate.origin with
      | .protocol _ => true
      | .local .. => false
    unless protocols.length == program.payload.protocols.length do
      Lean.throwError "missing typed protocol origin candidate"
    for candidate in protocols do
      unless (program.payload.protocols[candidate.index]?).map (·.name) == some candidate.symbol do
        Lean.throwError "protocol origin candidate selects the wrong checked protocol"
    let .ok _ := chargeLabels root | Lean.throwError "valid charges refused"
  Lean.logInfo "PASS production generation origin, label, association controls"

end TestsSecurity.GenerateRootControls
