module

public import Zkc.Source.Structured.UnitViews
public import Zkc.Construction.Compiled
public import Zkc.Construction.Uniform.DomainHandler
public import Zkc.Source.Structured.CommonAdapter
public import ZkcExamples.Construction.ComposedSumcheckProofData
public import ZkcExamples.Construction.ComposedSumcheckProofParticipant
public import ZkcExamples.Construction.ComposedSumcheckProofBodies

@[expose] public section

/-! Admission metadata for the retained composed Sumcheck export. The finite
checks fix source/artifact identity and selection. Execution correspondence is
provided by the generated checked root and ComposedSumcheckScalarConnection. -/

namespace ZkcExamples.Construction.ComposedSumcheckProof
open Zkc.Source Zkc.Source.Structured Zkc.Construction

set_option smartUnfolding false

/-! ## The original Proof Entry -/

open ZkcExamples.Construction.ComposedSumcheckProofBodies in
structured_views ZkcExamples.Construction.ComposedSumcheckProofData.snapshot
  helpers [helper0, helper1, helper2, helper3, helper4, helper5, helper6, helper7, helper8, pending, helper15, helper9, helper16, tableShapeFormula, helper11, helper12, helper13, pendingFormula, helper17, openClaim, helper18, helper19, helper20, helper23, atPrefix, helper31, scopedHelper22, scopedHelper23, scopedHelper24, helper22, helper24, helper25, scopedHelper28, scopedHelper29, helper27, helper28, check, helper30]
  protocols [protocol0, proof]

theorem admitted : Structured.check ZkcExamples.Construction.ComposedSumcheckProofData.snapshot = .ok program := kernel_admission

abbrev snapshot := ZkcExamples.Construction.ComposedSumcheckProofData.snapshot
abbrev participant := ZkcExamples.Construction.ComposedSumcheckProofParticipant.participant

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

theorem context_admitted : exportContext ZkcExamples.Construction.ComposedSumcheckProofData.snapshot participant = some context :=
  (select_sound imported participant selected).1

set_option smartUnfolding true in
/-- The derived context: entry, roster, producer and validator positions, the
replaced service input, its contract and the draw request its challenges
carry, the suite and the selected query/delivery sites. -/
theorem context_eq : context =
    Context.fiatShamir ZkcExamples.Construction.ComposedSumcheckProofData.snapshot.entry ["role00000000", "role00000001"] 0 1 5 "random.bls12-381.fr/0" (some (.draw "bls12-381.fr")) participant.policy.suite [("apply_14_label_6c656674_label_6368616c6c656e6765", "apply_14_label_6c656674_label_64656c6976657279_0"), ("apply_16_label_7269676874_label_6368616c6c656e6765", "apply_16_label_7269676874_label_64656c6976657279_0")] := by
  decide +kernel

/-- The structural check and exact occurrence provenance on the actual export. -/
theorem compiled_rules : checkExport ZkcExamples.Construction.ComposedSumcheckProofData.snapshot participant = .ok () ∧ check context participant = .ok () ∧
    SourceOccurrences.check ZkcExamples.Construction.ComposedSumcheckProofData.snapshot context participant = .ok () := by
  obtain ⟨exported, construction, occurrences⟩ :=
    checkCompiled_components context_admitted compiled
  exact ⟨exported, construction, occurrences⟩

/-- The per-compile construction check accepts the actual export. -/
theorem accepted : checkExport ZkcExamples.Construction.ComposedSumcheckProofData.snapshot participant = .ok () := compiled_rules.1

/-- The transcript-construction rule accepts the actual export. -/
theorem checked : check context participant = .ok () := compiled_rules.2.1

/-- Exact source occurrences are retained by the actual export. -/
theorem source_occurrences : SourceOccurrences.check ZkcExamples.Construction.ComposedSumcheckProofData.snapshot context participant = .ok () := compiled_rules.2.2

set_option smartUnfolding true in
theorem validator_eq : context.validator = 1 := by decide +kernel

set_option smartUnfolding true in
theorem producer_eq : context.producer = 0 := by decide +kernel

/-- Where the export returns the selected acceptance output. -/
def acceptancePosition : Nat := selection.position

theorem acceptance_admitted : exportAcceptance ZkcExamples.Construction.ComposedSumcheckProofData.snapshot participant = some acceptancePosition :=
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
def inputs (left right : List F) (leftSum rightSum : F) (rounds : Nat) : List (Value F G) :=
  [.vector "bls12-381.fr" left, .vector "bls12-381.fr" right, .data (.field "bls12-381.fr" leftSum), .data (.field "bls12-381.fr" rightSum), .index rounds]

/-- The validator's original inputs: the published values at their positions,
absent inputs of other roles, and the challenge service handle. -/
def verifierInputs (left right : List F) (leftSum rightSum : F) (rounds : Nat) (handle : Nat) :
    Values (Component (assignment F G)) program.payload.entry.inputs :=
  .cons (some left) (.cons (some right) (.cons (some leftSum) (.cons (some rightSum) (.cons (some rounds) (.cons (some handle) (.nil))))))

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The constructed program's data inputs are the published inputs and the
initial transcript. -/
theorem inputs_arity (left right : List F) (leftSum rightSum : F) (rounds : Nat) :
    (inputs (F := F) (G := G) left right leftSum rightSum rounds).length + 1 = participant.inputs.length :=
  rfl

/-- Helper calls of the constructed program denote the original's checked
helpers. -/
abbrev table : Structured.Meanings F G := helperTable program F G

/-- The admitted root's validator process, read through its acceptance output. -/
def process (left right : List F) (leftSum rightSum : F) (rounds : Nat) (handle : Nat) : PIR.Process (participantInterface F G) (Option Bool) :=
  (program.participant F G 1 (verifierInputs left right leftSum rightSum rounds handle)).bind fun outputs =>
    .done (outputs.get .here)

/-- The original validator, read through its acceptance output. -/
def verifier (left right : List F) (leftSum rightSum : F) (rounds : Nat) (handle : Nat) : PIR.Process (Actions F G) (Option Bool) :=
  (process left right leftSum rightSum rounds handle).interpret CommonAdapter.project


end ZkcExamples.Construction.ComposedSumcheckProof
