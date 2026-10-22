module

public import Zkc.Source.Structured.UnitViews
public import Zkc.Construction.Compiled
public import Zkc.Source.Structured.CommonAdapter
public import ZkcExamples.Construction.SchnorrAndProofData
public import ZkcExamples.Construction.SchnorrAndProofParticipant
public import ZkcExamples.Construction.SchnorrAndProofBodies
public import ZkcExamples.Construction.SchnorrAndProofModel

@[expose] public section

/-! Generated construction facts of the compiled `example::AndProof` Entry of the subject
`schnorr-and`. Regenerate with `lean/bridges/subject.py --write`.

`SchnorrAndProofData` is the Entry's original export and
`SchnorrAndProofParticipant` its constructed validator. The composed
transcript-construction and participant projection check accepts the pair
(`compiled`), and the selection check (`selection_checked`) discharges the
positional premises of the composed rules from data the kernel reads, so
`compiled_transform` holds with no proof specific to this Entry: for every
challenge function, the compiled verifier's ideal meaning is the Fiat–Shamir
transform of the original validator. -/

namespace ZkcExamples.Construction.SchnorrAndProof
open Zkc.Source Zkc.Source.Structured Zkc.Construction

set_option smartUnfolding false

/-! ## The original Proof Entry -/

structured_views ZkcExamples.Construction.SchnorrAndProofData.snapshot
  helpers [formula := ZkcExamples.Construction.SchnorrAndProofBodies.formula]
  protocols [proof := ZkcExamples.Construction.SchnorrAndProofBodies.proof]

theorem admitted : Structured.check ZkcExamples.Construction.SchnorrAndProofData.snapshot = .ok program := kernel_admission

abbrev snapshot := ZkcExamples.Construction.SchnorrAndProofData.snapshot
abbrev participant := ZkcExamples.Construction.SchnorrAndProofParticipant.participant

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

theorem context_admitted : exportContext ZkcExamples.Construction.SchnorrAndProofData.snapshot participant = some context :=
  (select_sound imported participant selected).1

set_option smartUnfolding true in
/-- The derived context: entry, roster, producer and validator positions, the
replaced service input, its contract and the draw request its challenges
carry, the suite and the selected query/delivery sites. -/
theorem context_eq : context =
    ⟨ZkcExamples.Construction.SchnorrAndProofData.snapshot.entry, ["role00000000", "role00000001"], 0, 1, 7, "random.bls12-381.fr/0", some (.draw "bls12-381.fr"), participant.policy.suite, [("label_6368616c6c656e6765", "label_64656c6976657279_0")]⟩ := by
  decide +kernel

/-- The composed check's two rules, each on the actual export. -/
theorem compiled_rules : checkExport ZkcExamples.Construction.SchnorrAndProofData.snapshot participant = .ok () ∧ check context participant = .ok () ∧
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
theorem accepted : checkExport ZkcExamples.Construction.SchnorrAndProofData.snapshot participant = .ok () := compiled_rules.1

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

theorem acceptance_admitted : exportAcceptance ZkcExamples.Construction.SchnorrAndProofData.snapshot participant = some acceptancePosition :=
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
def inputs (firstBase firstPoint secondBase secondPoint : G) : List (Value F G) :=
  [.data (.group "bls12-381.g1" firstBase), .data (.group "bls12-381.g1" firstPoint), .data (.group "bls12-381.g1" secondBase), .data (.group "bls12-381.g1" secondPoint)]

/-- The validator's original inputs: the published values at their positions,
absent inputs of other roles, and the challenge service handle. -/
def verifierInputs (firstBase firstPoint secondBase secondPoint : G) (handle : Nat) :
    Values (Component (assignment F G)) program.payload.entry.inputs :=
  .cons (some firstBase) (.cons (some firstPoint) (.cons (some secondBase) (.cons (some secondPoint) (.cons (none) (.cons (none) (.cons (none) (.cons (some handle) (.nil))))))))

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The constructed program's data inputs hold the validator's original inputs:
the published values at their exported positions and the handle as the replaced
service. -/
theorem inputs_related (firstBase firstPoint secondBase secondPoint : G) (handle : Nat) (initial : History F G) :
    HoldsValues handle (inputs firstBase firstPoint secondBase secondPoint ++ [.transcript initial])
      (inputSlots context participant.policy program.payload.entry.inputs)
      (verifierInputs (F := F) (G := G) firstBase firstPoint secondBase secondPoint handle) :=
  (selection_sound (F := F) (G := G) imported participant selected selection_checked).2.1 handle
    (.cons firstBase (.cons firstPoint (.cons secondBase (.cons secondPoint (.nil))))) [.transcript initial]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The constructed program's data inputs are the published inputs and the
initial transcript. -/
theorem inputs_arity (firstBase firstPoint secondBase secondPoint : G) :
    (inputs (F := F) (G := G) firstBase firstPoint secondBase secondPoint).length + 1 = participant.inputs.length :=
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
def process (firstBase firstPoint secondBase secondPoint : G) (handle : Nat) : PIR.Process (participantInterface F G) (Option Bool) :=
  (program.participant F G 1 (verifierInputs firstBase firstPoint secondBase secondPoint handle)).bind fun outputs =>
    .done (outputs.get .here)

/-- The original validator, read through its acceptance output. -/
def verifier (firstBase firstPoint secondBase secondPoint : G) (handle : Nat) : PIR.Process (Actions F G) (Option Bool) :=
  (process firstBase firstPoint secondBase secondPoint handle).interpret CommonAdapter.project

/-- The original validator, read through its outputs, is the verifier. -/
theorem original_verifier (firstBase firstPoint secondBase secondPoint : G) (handle : Nat) :
    ((program.participant F G context.validator (verifierInputs firstBase firstPoint secondBase secondPoint handle)).bind fun outputs =>
      .done (decision (validatorOutputs context.validator program.payload.entry.outputScopes
        outputs))).interpret CommonAdapter.project = verifier firstBase firstPoint secondBase secondPoint handle := by
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
    (challenge : History F G → m F) (firstBase firstPoint secondBase secondPoint : G) (handle : Nat) (initial : History F G)
    (proof : Proof F G) :
    (fun result => (mapOutcome acceptance result.1, result.2)) <$>
        ideal context challenge table participant.returned participant.instructions
          (inputs firstBase firstPoint secondBase secondPoint ++ [.transcript initial]) proof =
      transform context challenge (verifier firstBase firstPoint secondBase secondPoint handle) initial proof :=
  (compiled_selected imported participant compiled selected selection_checked).2 challenge handle
    (.cons firstBase (.cons firstPoint (.cons secondBase (.cons secondPoint (.nil))))) initial proof

/-- By the construction rule alone, the compiled verifier is the Fiat–Shamir
transform of the interactive reading of its exported instructions, read through
the acceptance output, for every service handle. -/
theorem spec_transform {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (handle : Nat) (data : List (Value F G))
    (arity : data.length = 4) (initial : History F G) (proof : Proof F G) :
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
theorem process_equation (firstBase firstPoint secondBase secondPoint : G) (handle : Nat) :
    process (F := F) (G := G) firstBase firstPoint secondBase secondPoint handle = (Zkc.Protocols.Schnorr.Variants.conjunction wiring firstBase firstPoint secondBase secondPoint handle).interpret CommonAdapter.embed := by
  rfl

theorem verifier_correspondence (firstBase firstPoint secondBase secondPoint : G) (handle : Nat) :
    verifier (F := F) (G := G) firstBase firstPoint secondBase secondPoint handle = Zkc.Protocols.Schnorr.Variants.conjunction wiring firstBase firstPoint secondBase secondPoint handle := by
  rw [verifier, process_equation, CommonAdapter.project_embed]

/-- The constructed program's interactive reading is the model, with every
reply, stop and acceptance decision. Derived from the projection rule; no
computation specific to this Entry is involved. -/
theorem spec_equation (firstBase firstPoint secondBase secondPoint : G) (handle : Nat) (initial : History F G) :
    (spec context handle table participant.returned participant.instructions
        (inputs firstBase firstPoint secondBase secondPoint ++ [.transcript initial])).bind
      (fun values => .done (acceptance values)) =
      Zkc.Protocols.Schnorr.Variants.conjunction wiring firstBase firstPoint secondBase secondPoint handle := by
  rw [spec_bind_congr context handle table participant.returned participant.instructions _ acceptance
    (fun values => decision (values.dropLast.map some)) acceptance_decision]
  have projected' := project_sound program context participant projected handle
    (inputs firstBase firstPoint secondBase secondPoint) initial (verifierInputs firstBase firstPoint secondBase secondPoint handle)
    (inputs_related firstBase firstPoint secondBase secondPoint handle initial) rfl
  calc (spec context handle table participant.returned participant.instructions
          (inputs firstBase firstPoint secondBase secondPoint ++ [.transcript initial])).bind
          (fun values => .done (decision (values.dropLast.map some)))
      = ((spec context handle table participant.returned participant.instructions
          (inputs firstBase firstPoint secondBase secondPoint ++ [.transcript initial])).bind
          (fun values => .done (values.dropLast.map some))).bind
          (fun options => .done (decision options)) := by
        rw [PIR.Process.bind_assoc]
        rfl
    _ = (((program.participant F G context.validator (verifierInputs firstBase firstPoint secondBase secondPoint handle)).bind
          fun outputs => .done (validatorOutputs context.validator program.payload.entry.outputScopes
            outputs)).interpret CommonAdapter.project).bind
          (fun options => .done (decision options)) := by
        rw [projected']
    _ = ((program.participant F G context.validator (verifierInputs firstBase firstPoint secondBase secondPoint handle)).bind
          fun outputs => .done (decision (validatorOutputs context.validator
            program.payload.entry.outputScopes outputs))).interpret CommonAdapter.project := by
        rw [PIR.Process.interpret_bind, PIR.Process.interpret_bind, PIR.Process.bind_assoc]
        rfl
    _ = Zkc.Protocols.Schnorr.Variants.conjunction wiring firstBase firstPoint secondBase secondPoint handle := by
        rw [original_verifier, verifier_correspondence]

end ZkcExamples.Construction.SchnorrAndProof
