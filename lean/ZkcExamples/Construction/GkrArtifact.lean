module

public import Zkc.Construction.Compiled
public import Zkc.Construction.Uniform.DomainHandler
public import Zkc.Source.Structured.CommonAdapter
public import ZkcExamples.Structured.GkrSourceData
public import ZkcExamples.Construction.GkrProofParticipant
public import ZkcExamples.Structured.GkrSourceViews

@[expose] public section

/-! Generated artifact admission and source metadata for `example::Proof` of `gkr`.
Regenerate with `lean/bridges/subject.py --write`.

The structural checks do not establish source correspondence. The maintained
endpoint imports this metadata and a separate checked Domain connection. -/

namespace ZkcExamples.Construction.GkrProof
open Zkc.Source Zkc.Source.Structured Zkc.Construction

set_option smartUnfolding false

/-! ## The original Proof Entry -/

abbrev program := ZkcExamples.Structured.GkrSourceViews.program
/-- The admitted original. -/
abbrev imported : Structured.Imported ZkcExamples.Structured.GkrSourceData.snapshot :=
  ZkcExamples.Structured.GkrSourceViews.imported

abbrev snapshot := ZkcExamples.Structured.GkrSourceData.snapshot
abbrev participant := ZkcExamples.Construction.GkrProofParticipant.participant

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

theorem context_admitted : exportContext ZkcExamples.Structured.GkrSourceData.snapshot participant = some context :=
  (select_sound imported participant selected).1

set_option smartUnfolding true in
/-- The derived context: entry, roster, producer and validator positions, the
replaced service input, its contract and the draw request its challenges
carry, the suite and the selected query/delivery sites. -/
theorem context_eq : context =
    Context.fiatShamir ZkcExamples.Structured.GkrSourceData.snapshot.entry ["role00000000", "role00000001"] 0 1 7 "random.bls12-381.fr/0" (some (.draw "bls12-381.fr")) participant.policy.suite [("label_6f7574707574", "label_6f75747075745f64656c6976657279_0"), ("apply_14_label_6c656674_label_6368616c6c656e6765", "apply_14_label_6c656674_label_64656c6976657279_0"), ("apply_16_label_7269676874_label_6368616c6c656e6765", "apply_16_label_7269676874_label_64656c6976657279_0"), ("label_6c696e655f6368616c6c656e6765", "label_6c696e655f64656c6976657279_0")] := by
  decide +kernel

/-- The composed check's two rules, each on the actual export. -/
theorem compiled_rules : checkExport ZkcExamples.Structured.GkrSourceData.snapshot participant = .ok () ∧ check context participant = .ok () ∧
    project program context participant = .ok () := by
  obtain ⟨exported, construction, _, projection⟩ :=
    checkCompiled_components context_admitted compiled
  exact ⟨exported, construction, projection⟩

/-- The per-compile construction check accepts the actual export. -/
theorem accepted : checkExport ZkcExamples.Structured.GkrSourceData.snapshot participant = .ok () := compiled_rules.1

/-- The transcript-construction rule accepts the actual export. -/
theorem checked : check context participant = .ok () := compiled_rules.2.1

/-- The participant projection rule accepts the actual export. -/
theorem projected : project program context participant = .ok () := compiled_rules.2.2

set_option smartUnfolding true in
theorem validator_eq : context.validator = 1 := by decide +kernel

set_option smartUnfolding true in
theorem producer_eq : context.producer = 0 := by decide +kernel

/-- Where the export returns the selected acceptance output. -/
def acceptancePosition : Nat := selection.position

theorem acceptance_admitted : exportAcceptance ZkcExamples.Structured.GkrSourceData.snapshot participant = some acceptancePosition :=
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
def inputs (inputsValue outputsValue add mul : List F) (layers selector width : Nat) : List (Value F G) :=
  [.vector "bls12-381.fr" inputsValue, .vector "bls12-381.fr" outputsValue, .vector "bls12-381.fr" add, .vector "bls12-381.fr" mul, .index layers, .index selector, .index width]

/-- The validator's original inputs: the published values at their positions,
absent inputs of other roles, and the challenge service handle. -/
def verifierInputs (inputsValue outputsValue add mul : List F) (layers selector width : Nat) (handle : Nat) :
    Values (Component (assignment F G)) program.payload.entry.inputs :=
  .cons (some inputsValue) (.cons (some outputsValue) (.cons (some add) (.cons (some mul) (.cons (some layers) (.cons (some selector) (.cons (some width) (.cons (some handle) (.nil))))))))

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The constructed program's data inputs are the published inputs and the
initial transcript. -/
theorem inputs_arity (inputsValue outputsValue add mul : List F) (layers selector width : Nat) :
    (inputs (F := F) (G := G) inputsValue outputsValue add mul layers selector width).length + 1 = participant.inputs.length :=
  rfl

/-- Helper calls of the constructed program denote the original's checked
helpers. -/
abbrev table : Structured.Meanings F G := helperTable program F G

/-- The admitted root's validator process, read through its acceptance output. -/
def process (inputsValue outputsValue add mul : List F) (layers selector width : Nat) (handle : Nat) : PIR.Process (participantInterface F G) (Option Bool) :=
  (program.participant F G 1 (verifierInputs inputsValue outputsValue add mul layers selector width handle)).bind fun outputs =>
    .done (outputs.get .here)

/-- The original validator, read through its acceptance output. -/
def verifier (inputsValue outputsValue add mul : List F) (layers selector width : Nat) (handle : Nat) : PIR.Process (Actions F G) (Option Bool) :=
  (process inputsValue outputsValue add mul layers selector width handle).interpret CommonAdapter.project


end ZkcExamples.Construction.GkrProof
