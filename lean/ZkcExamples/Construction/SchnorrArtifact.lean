module

public import Zkc.Source.Structured.UnitViews
public import Zkc.Construction.Compiled
public import Zkc.Construction.Uniform.DomainHandler
public import Zkc.Source.Structured.CommonAdapter
public import ZkcExamples.Construction.SchnorrProofData
public import ZkcExamples.Construction.SchnorrProofParticipant
public import ZkcExamples.Construction.SchnorrProofBodies
public import ZkcExamples.Construction.SchnorrProofModel

@[expose] public section

/-! Generated artifact admission and source metadata for `example::Proof` of `schnorr`.
Regenerate with `lean/bridges/subject.py --write`.

The structural checks do not establish source correspondence. The maintained
endpoint imports this metadata and a separate checked Domain connection. -/

namespace ZkcExamples.Construction.SchnorrProof
open Zkc.Source Zkc.Source.Structured Zkc.Construction

set_option smartUnfolding false

/-! ## The original Proof Entry -/

open ZkcExamples.Construction.SchnorrProofBodies in
structured_views ZkcExamples.Construction.SchnorrProofData.snapshot
  helpers [formula]
  protocols [proof]

theorem admitted : Structured.check ZkcExamples.Construction.SchnorrProofData.snapshot = .ok program := kernel_admission

abbrev snapshot := ZkcExamples.Construction.SchnorrProofData.snapshot
abbrev participant := ZkcExamples.Construction.SchnorrProofParticipant.participant

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

theorem context_admitted : exportContext ZkcExamples.Construction.SchnorrProofData.snapshot participant = some context :=
  (select_sound imported participant selected).1

set_option smartUnfolding true in
/-- The derived context: entry, roster, producer and validator positions, the
replaced service input, its contract and the draw request its challenges
carry, the suite and the selected query/delivery sites. -/
theorem context_eq : context =
    Context.fiatShamir ZkcExamples.Construction.SchnorrProofData.snapshot.entry ["role00000000", "role00000001"] 0 1 4 "random.bls12-381.fr/0" (some (.draw "bls12-381.fr")) participant.policy.suite [("label_6368616c6c656e6765", "label_64656c6976657279_0")] := by
  decide +kernel

/-- The composed check's two rules, each on the actual export. -/
theorem compiled_rules : checkExport ZkcExamples.Construction.SchnorrProofData.snapshot participant = .ok () ∧ check context participant = .ok () ∧
    project program context participant = .ok () := by
  obtain ⟨exported, construction, _, projection⟩ :=
    checkCompiled_components context_admitted compiled
  exact ⟨exported, construction, projection⟩

/-- The per-compile construction check accepts the actual export. -/
theorem accepted : checkExport ZkcExamples.Construction.SchnorrProofData.snapshot participant = .ok () := compiled_rules.1

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

theorem acceptance_admitted : exportAcceptance ZkcExamples.Construction.SchnorrProofData.snapshot participant = some acceptancePosition :=
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
def inputs (base point : G) : List (Payload F G) :=
  [.group "bls12-381.g1" base, .group "bls12-381.g1" point]

/-- The validator's original inputs: the published values at their positions,
absent inputs of other roles, and the challenge service handle. -/
def verifierInputs (base point : G) (handle : Nat) :
    Values (Component (assignment F G)) program.payload.entry.inputs :=
  .cons (some base) (.cons (some point) (.cons (none) (.cons (none) (.cons (some handle) (.nil)))))

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The constructed program's data inputs are the published inputs and the
initial transcript. -/
theorem inputs_arity (base point : G) :
    (inputs (F := F) (G := G) base point).length + 1 = participant.inputs.length :=
  rfl

/-- The validator's original inputs, by original position. -/
def originalValue (base point : G) (handle : Nat) (index : Nat) : Option (Payload F G) :=
  ((inputPayloads (verifierInputs (F := F) (G := G) base point handle))[index]?).join

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The host binds exactly `inputs`: the validator's original inputs at the
checked policy's public positions, in order. -/
theorem public_values (base point : G) (handle : Nat) :
    publicValues participant.policy (originalValue (F := F) (G := G) base point handle) =
      some (inputs base point) := by
  rfl

/-- Helper calls of the constructed program denote the original's checked
helpers. -/
abbrev table : Structured.Meanings F G := helperTable program F G

/-- The admitted root's validator process, read through its acceptance output. -/
def process (base point : G) (handle : Nat) : PIR.Process (participantInterface F G) (Option Bool) :=
  (program.participant F G 1 (verifierInputs base point handle)).bind fun outputs =>
    .done (outputs.get .here)

/-- The original validator, read through its acceptance output. -/
def verifier (base point : G) (handle : Nat) : PIR.Process (Actions F G) (Option Bool) :=
  (process base point handle).interpret CommonAdapter.project


/-! ## The model the original validator is, by computation -/

/-- The admitted root's validator process is the model, by computation. -/
theorem process_equation (base point : G) (handle : Nat) :
    process (F := F) (G := G) base point handle = (Zkc.Protocols.Schnorr.Common.experiment wiring base point handle).interpret CommonAdapter.embed := by
  rfl

theorem verifier_correspondence (base point : G) (handle : Nat) :
    verifier (F := F) (G := G) base point handle = Zkc.Protocols.Schnorr.Common.experiment wiring base point handle := by
  rw [verifier, process_equation, CommonAdapter.project_embed]


end ZkcExamples.Construction.SchnorrProof
