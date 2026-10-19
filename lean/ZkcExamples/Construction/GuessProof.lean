module

public import Zkc.Source.Structured.UnitViews
public import Zkc.Construction.Compiled
public import Zkc.Source.Structured.CommonAdapter
public import ZkcExamples.Construction.GuessProofData
public import ZkcExamples.Construction.GuessProofParticipant
public import ZkcExamples.Construction.GuessProofBodies
public import ZkcExamples.Construction.GuessProofModel

@[expose] public section

/-! Generated construction facts of the compiled `example::Proof` Entry of the subject
`guess`. Regenerate with `lean/bridges/subject.py --write`.

`GuessProofData` is the Entry's original export and
`GuessProofParticipant` its constructed validator. The composed
transcript-construction and participant projection check accepts the pair
(`compiled`), and the selection check (`selection_checked`) discharges the
positional premises of the composed rules from data the kernel reads, so
`compiled_transform` holds with no proof specific to this Entry: for every
challenge function, the compiled verifier's ideal meaning is the Fiat–Shamir
transform of the original validator. -/

namespace ZkcExamples.Construction.GuessProof
open Zkc.Source Zkc.Source.Structured Zkc.Construction

set_option smartUnfolding false

/-! ## The original Proof Entry -/

structured_views ZkcExamples.Construction.GuessProofData.snapshot
  helpers []
  protocols [proof := ZkcExamples.Construction.GuessProofBodies.proof]

theorem admitted : Structured.check ZkcExamples.Construction.GuessProofData.snapshot = .ok program := kernel_admission

abbrev snapshot := ZkcExamples.Construction.GuessProofData.snapshot
abbrev participant := ZkcExamples.Construction.GuessProofParticipant.participant

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

theorem context_admitted : exportContext ZkcExamples.Construction.GuessProofData.snapshot participant = some context :=
  (select_sound imported participant selected).1

set_option smartUnfolding true in
/-- The derived context: entry, roster, producer and validator positions, the
replaced service input, its contract and the draw request its challenges
carry, the suite and the selected query/delivery sites. -/
theorem context_eq : context =
    ⟨ZkcExamples.Construction.GuessProofData.snapshot.entry, ["role00000000", "role00000001"], 0, 1, 2, "random.bls12-381.fr/0", some (.draw "bls12-381.fr"), participant.policy.suite, [("label_6368616c6c656e6765", "label_64656c6976657279_0")]⟩ := by
  decide +kernel

/-- The composed check's two rules, each on the actual export. -/
theorem compiled_rules : checkExport ZkcExamples.Construction.GuessProofData.snapshot participant = .ok () ∧ check context participant = .ok () ∧
    project program context participant = .ok () := by
  have accepted := compiled
  unfold checkCompiled at accepted
  split at accepted
  · rename_i context' exported found
    rw [context_admitted] at found
    cases found
    obtain ⟨context'', found', checked⟩ := checkExport_sound exported
    rw [context_admitted] at found'
    cases found'
    exact ⟨exported, checked, accepted⟩
  · cases accepted
  · cases accepted

/-- The per-compile construction check accepts the actual export. -/
theorem accepted : checkExport ZkcExamples.Construction.GuessProofData.snapshot participant = .ok () := compiled_rules.1

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

theorem acceptance_admitted : exportAcceptance ZkcExamples.Construction.GuessProofData.snapshot participant = some acceptancePosition :=
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

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- On every list of the returned length, the acceptance output is the decision
among the validator's outputs. -/
theorem acceptance_decision (values : List (Value F G))
    (length : values.length = participant.returned.length) :
    acceptance values = decision (values.dropLast.map some) :=
  (selection_sound (F := F) (G := G) imported participant selected selection_checked).1 values length

/-- Data inputs of the constructed validator: the policy's public inputs, in
policy order. -/
def inputs (offset : F) : List (Payload F G) :=
  [.field "bls12-381.fr" offset]

/-- The validator's original inputs: the published values at their positions,
absent inputs of other roles, and the challenge service handle. -/
def verifierInputs (offset : F) (handle : Nat) :
    Values (Component (assignment F G)) program.payload.entry.inputs :=
  .cons (some offset) (.cons (none) (.cons (some handle) (.nil)))

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The constructed program's data inputs hold the validator's original inputs:
the published values at their exported positions and the handle as the replaced
service. -/
theorem inputs_related (offset : F) (handle : Nat) (initial : History F G) :
    HoldsValues handle ((inputs offset).map .data ++ [.transcript initial])
      (inputSlots context participant.policy program.payload.entry.inputs)
      (verifierInputs (F := F) (G := G) offset handle) :=
  (selection_sound (F := F) (G := G) imported participant selected selection_checked).2.1 handle
    (.cons offset (.nil)) [.transcript initial]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The constructed program's data inputs are the published inputs and the
initial transcript. -/
theorem inputs_arity (offset : F) :
    (inputs (F := F) (G := G) offset).length + 1 = participant.inputs.length :=
  rfl

/-- The validator's original inputs, by original position. -/
def originalValue (offset : F) (handle : Nat) (index : Nat) : Option (Payload F G) :=
  ((inputPayloads (verifierInputs (F := F) (G := G) offset handle))[index]?).join

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The host binds exactly `inputs`: the validator's original inputs at the
checked policy's public positions, in order. -/
theorem public_values (offset : F) (handle : Nat) :
    publicValues participant.policy (originalValue (F := F) (G := G) offset handle) =
      some (inputs offset) := by
  rfl

/-- Helper calls of the constructed program denote the original's checked
helpers. -/
abbrev table : Structured.Meanings F G := helperTable program F G

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The decision among the validator's outputs is its acceptance output. -/
theorem decision_outputs (outputs : Values (Component (assignment F G)) program.payload.entry.outputs) :
    decision (validatorOutputs 1 program.payload.entry.outputScopes outputs) = outputs.get .here :=
  (selection_sound (F := F) (G := G) imported participant selected selection_checked).2.2.2 outputs

/-- The admitted root's validator process, read through its acceptance output. -/
def process (offset : F) (handle : Nat) : PIR.Proc (participantInterface F G) (Option Bool) :=
  (program.participant F G 1 (verifierInputs offset handle)).bind fun outputs =>
    .done (outputs.get .here)

/-- The original validator, read through its acceptance output. -/
def verifier (offset : F) (handle : Nat) : PIR.Proc (Actions F G) (Option Bool) :=
  (process offset handle).interpret CommonAdapter.project

/-- The original validator, read through its outputs, is the verifier. -/
theorem original_verifier (offset : F) (handle : Nat) :
    ((program.participant F G context.validator (verifierInputs offset handle)).bind fun outputs =>
      .done (decision (validatorOutputs context.validator program.payload.entry.outputScopes
        outputs))).interpret CommonAdapter.project = verifier offset handle := by
  unfold verifier process
  rw [validator_eq]
  simp only [decision_outputs]

/-- The compiled verifier, under the ideal transcript model with any challenge
function in any lawful monad, is the Fiat–Shamir transform of the original
Proof Entry's validator: equal acceptance outcomes, stops and unread proof
suffixes, for every published input, initial transcript, proof and service
handle. An instance of `Zkc.Construction.compiled_selected`, whose positional
premises the checked selection discharges. -/
theorem compiled_transform {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (offset : F) (handle : Nat) (initial : History F G)
    (proof : Proof F G) :
    (fun result => (mapOutcome acceptance result.1, result.2)) <$>
        ideal context challenge table participant.returned participant.instructions
          ((inputs offset).map .data ++ [.transcript initial]) proof =
      transform context challenge (verifier offset handle) initial proof :=
  (compiled_selected imported participant compiled selected selection_checked).2 challenge handle
    (.cons offset (.nil)) initial proof

/-- By the construction rule alone, the compiled verifier is the Fiat–Shamir
transform of the interactive reading of its exported instructions, read through
the acceptance output, for every service handle. -/
theorem spec_transform {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (handle : Nat) (data : List (Value F G))
    (arity : data.length = 1) (initial : History F G) (proof : Proof F G) :
    (fun result => (mapOutcome acceptance result.1, result.2)) <$>
        ideal context challenge table participant.returned participant.instructions
          (data ++ [.transcript initial]) proof =
      transform context challenge
        ((spec context handle table participant.returned participant.instructions
          (data ++ [.transcript initial])).bind fun values => .done (acceptance values))
        initial proof := by
  rw [check_sound context challenge handle table participant checked data initial proof
    (by rw [arity]; rfl), transform_bind_done]

/-! ## The model the original validator is, by computation -/

/-- The admitted root's validator process is the model, by computation. -/
theorem process_equation (offset : F) (handle : Nat) :
    process (F := F) (G := G) offset handle = (experiment offset handle).interpret CommonAdapter.embed := by
  rfl

theorem verifier_correspondence (offset : F) (handle : Nat) :
    verifier (F := F) (G := G) offset handle = experiment offset handle := by
  rw [verifier, process_equation, CommonAdapter.project_embed]

/-- The constructed program's interactive reading is the model, with every
reply, stop and acceptance decision. Derived from the projection rule; no
computation specific to this Entry is involved. -/
theorem spec_equation (offset : F) (handle : Nat) (initial : History F G) :
    (spec context handle table participant.returned participant.instructions
        ((inputs offset).map .data ++ [.transcript initial])).bind
      (fun values => .done (acceptance values)) =
      experiment offset handle := by
  rw [spec_bind_congr context handle table participant.returned participant.instructions _ acceptance
    (fun values => decision (values.dropLast.map some)) acceptance_decision]
  have projected' := project_sound program context participant projected handle
    ((inputs offset).map .data) initial (verifierInputs offset handle)
    (inputs_related offset handle initial) rfl
  calc (spec context handle table participant.returned participant.instructions
          ((inputs offset).map .data ++ [.transcript initial])).bind
          (fun values => .done (decision (values.dropLast.map some)))
      = ((spec context handle table participant.returned participant.instructions
          ((inputs offset).map .data ++ [.transcript initial])).bind
          (fun values => .done (values.dropLast.map some))).bind
          (fun options => .done (decision options)) := by
        rw [PIR.Proc.bind_assoc]
        rfl
    _ = (((program.participant F G context.validator (verifierInputs offset handle)).bind
          fun outputs => .done (validatorOutputs context.validator program.payload.entry.outputScopes
            outputs)).interpret CommonAdapter.project).bind
          (fun options => .done (decision options)) := by
        rw [projected']
    _ = ((program.participant F G context.validator (verifierInputs offset handle)).bind
          fun outputs => .done (decision (validatorOutputs context.validator
            program.payload.entry.outputScopes outputs))).interpret CommonAdapter.project := by
        rw [PIR.Proc.interpret_bind, PIR.Proc.interpret_bind, PIR.Proc.bind_assoc]
        rfl
    _ = experiment offset handle := by
        rw [original_verifier, verifier_correspondence]

end ZkcExamples.Construction.GuessProof
