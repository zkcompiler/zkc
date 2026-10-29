module

public import Zkc.Construction.Compiled
public import Zkc.Construction.Uniform.DomainHandler
public import Zkc.Source.Structured.CommonAdapter
public import ZkcExamples.Structured.SumcheckSourceData
public import ZkcExamples.Construction.SumcheckProofParticipant
public import ZkcExamples.Structured.SumcheckSourceViews

@[expose] public section

/-! Generated artifact admission and source metadata for `example::Proof` of `sumcheck`.
Regenerate with `lean/bridges/subject.py --write`.

The structural checks do not establish source correspondence. The maintained
endpoint imports this metadata and a separate checked Domain connection. -/

namespace ZkcExamples.Construction.SumcheckProof
open Zkc.Source Zkc.Source.Structured Zkc.Construction

set_option smartUnfolding false

/-! ## The original Proof Entry -/

abbrev program := ZkcExamples.Structured.SumcheckSourceViews.program
/-- The admitted original. -/
abbrev imported : Structured.Imported ZkcExamples.Structured.SumcheckSourceData.snapshot :=
  ZkcExamples.Structured.SumcheckSourceViews.imported

abbrev snapshot := ZkcExamples.Structured.SumcheckSourceData.snapshot
abbrev participant := ZkcExamples.Construction.SumcheckProofParticipant.participant

/-! ## The constructed validator and its checked selection -/

set_option smartUnfolding true in
/-- The composed per-compile check accepts the actual export against the
admitted original. -/
theorem compiled : checkCompiled imported participant = .ok () := by decide +kernel

set_option smartUnfolding true in
/-- The selection of the export's inputs and acceptance output, constructed from
the admitted original and the export's policy. -/
def selection : Selection imported.program.payload.entry.outputs :=
  (select imported participant).get (by decide +kernel)

theorem selected : select imported participant = some selection := (Option.some_get _).symm

set_option smartUnfolding true in
/-- The selection check accepts the export. -/
theorem selection_checked : selection.check imported participant = true := by decide +kernel

/-- The occurrence context the check derives from the original roster and the
exported policy. -/
def context : Context := selection.context

theorem context_admitted : exportContext ZkcExamples.Structured.SumcheckSourceData.snapshot participant = some context :=
  (select_sound imported participant selected).1

set_option smartUnfolding true in
/-- The derived context: entry, roster, producer and validator positions, the
replaced service input, its contract and the draw request its challenges
carry, the suite and the selected query/delivery sites. -/
theorem context_eq : context =
    Context.fiatShamir ZkcExamples.Structured.SumcheckSourceData.snapshot.entry ["role00000000", "role00000001"] 0 1 3 "random.bls12-381.fr/0" (some (.draw "bls12-381.fr")) participant.policy.suite [("apply_18_label_726564756365_label_6368616c6c656e6765", "apply_18_label_726564756365_label_64656c6976657279_0")] := by
  decide +kernel

/-- The structural check and exact occurrence provenance on the actual export. -/
theorem compiled_rules : checkExport ZkcExamples.Structured.SumcheckSourceData.snapshot participant = .ok () ∧ check context participant = .ok () ∧
    SourceOccurrences.check ZkcExamples.Structured.SumcheckSourceData.snapshot context participant = .ok () := by
  obtain ⟨exported, construction, occurrences⟩ :=
    checkCompiled_components context_admitted compiled
  exact ⟨exported, construction, occurrences⟩

/-- The per-compile construction check accepts the actual export. -/
theorem accepted : checkExport ZkcExamples.Structured.SumcheckSourceData.snapshot participant = .ok () := compiled_rules.1

/-- The transcript-construction rule accepts the actual export. -/
theorem checked : check context participant = .ok () := compiled_rules.2.1

/-- Exact source occurrences are retained by the actual export. -/
theorem source_occurrences : SourceOccurrences.check ZkcExamples.Structured.SumcheckSourceData.snapshot context participant = .ok () := compiled_rules.2.2

set_option smartUnfolding true in
theorem validator_eq : context.validator = 1 := by decide +kernel

set_option smartUnfolding true in
theorem producer_eq : context.producer = 0 := by decide +kernel

/-- Where the export returns the selected acceptance output. -/
def acceptancePosition : Nat := selection.position

theorem acceptance_admitted : exportAcceptance ZkcExamples.Structured.SumcheckSourceData.snapshot participant = some acceptancePosition :=
  (select_sound imported participant selected).2.1

set_option smartUnfolding true in
theorem acceptancePosition_eq : acceptancePosition = 0 := by decide +kernel

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The acceptance output selected by the policy, read from returned values. -/
def acceptance (values : List (Value F G)) : Option Bool :=
  match values[acceptancePosition]? with
  | some (.data (.boolean decision)) => some decision
  | _ => none

/-- The acceptance decision among the validator's outputs. -/
def decision (options : List (Option (Value F G))) : Option Bool :=
  match options[acceptancePosition]? with
  | some (some (.data (.boolean value))) => some value
  | _ => none

/-- Data inputs of the constructed validator: the policy's public inputs, in
policy order. -/
def inputs (valuesValue : List F) (claim : F) (rounds : Nat) : List (Value F G) :=
  [.vector "bls12-381.fr" valuesValue, .data (.field "bls12-381.fr" claim), .index rounds]

/-- The validator's original inputs: the published values at their positions,
absent inputs of other roles, and the challenge service handle. -/
def verifierInputs (valuesValue : List F) (claim : F) (rounds : Nat) (handle : Nat) :
    Values (Component (assignment F G)) program.payload.entry.inputs :=
  .cons (some valuesValue) (.cons (some claim) (.cons (some rounds) (.cons (some handle) (.nil))))

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The constructed program's data inputs are the published inputs and the
initial transcript. -/
theorem inputs_arity (valuesValue : List F) (claim : F) (rounds : Nat) :
    (inputs (F := F) (G := G) valuesValue claim rounds).length + 1 = participant.inputs.length :=
  rfl

/-- Helper calls of the constructed program denote the original's checked
helpers. -/
abbrev table : Structured.Meanings F G := helperTable program F G

/-- The admitted root's validator process, read through its acceptance output. -/
def process (valuesValue : List F) (claim : F) (rounds : Nat) (handle : Nat) : PIR.Process (participantInterface F G) (Option Bool) :=
  (program.participant F G 1 (verifierInputs valuesValue claim rounds handle)).bind fun outputs =>
    .done (outputs.get .here)

/-- The original validator, read through its acceptance output. -/
def verifier (valuesValue : List F) (claim : F) (rounds : Nat) (handle : Nat) : PIR.Process (Actions F G) (Option Bool) :=
  (process valuesValue claim rounds handle).interpret CommonAdapter.project


end ZkcExamples.Construction.SumcheckProof
