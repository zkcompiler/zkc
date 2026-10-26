module

public import Zkc.Source.Structured.UnitViews
public import Zkc.Construction.Compiled
public import Zkc.Source.Structured.CommonAdapter
public import ZkcExamples.Construction.ComposedSumcheckProofData
public import ZkcExamples.Construction.ComposedSumcheckProofParticipant
public import ZkcExamples.Construction.ComposedSumcheckProofBodies

@[expose] public section

/-! Generated construction facts of the compiled `example::Proof` Entry of the subject
`composed-sumcheck`. Regenerate with `lean/bridges/subject.py --write`.

`ComposedSumcheckProofData` is the Entry's original export and
`ComposedSumcheckProofParticipant` its constructed validator. The composed
transcript-construction and participant projection Uniform.check accepts the pair
(`compiled`), and the selection Uniform.check (`selection_checked`) discharges the
positional premises of the composed rules from data the kernel reads, so
`compiled_transform` holds with no proof specific to this Entry: for every
challenge function, the compiled verifier's ideal meaning is the Fiat–Shamir
transform of the original validator. -/

namespace ZkcExamples.Construction.ComposedSumcheckProof
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.Uniform

set_option smartUnfolding false

/-! ## The original Proof Entry -/

structured_views ZkcExamples.Construction.ComposedSumcheckProofData.snapshot
  helpers [helper0 := ZkcExamples.Construction.ComposedSumcheckProofBodies.helper0, helper1 := ZkcExamples.Construction.ComposedSumcheckProofBodies.helper1, helper2 := ZkcExamples.Construction.ComposedSumcheckProofBodies.helper2, helper3 := ZkcExamples.Construction.ComposedSumcheckProofBodies.helper3, helper4 := ZkcExamples.Construction.ComposedSumcheckProofBodies.helper4, helper5 := ZkcExamples.Construction.ComposedSumcheckProofBodies.helper5, helper6 := ZkcExamples.Construction.ComposedSumcheckProofBodies.helper6, helper7 := ZkcExamples.Construction.ComposedSumcheckProofBodies.helper7, helper8 := ZkcExamples.Construction.ComposedSumcheckProofBodies.helper8, helper9 := ZkcExamples.Construction.ComposedSumcheckProofBodies.helper9, helper10 := ZkcExamples.Construction.ComposedSumcheckProofBodies.helper10, helper11 := ZkcExamples.Construction.ComposedSumcheckProofBodies.helper11, helper12 := ZkcExamples.Construction.ComposedSumcheckProofBodies.helper12, helper13 := ZkcExamples.Construction.ComposedSumcheckProofBodies.helper13, helper14 := ZkcExamples.Construction.ComposedSumcheckProofBodies.helper14, helper15 := ZkcExamples.Construction.ComposedSumcheckProofBodies.helper15, helper16 := ZkcExamples.Construction.ComposedSumcheckProofBodies.helper16, helper17 := ZkcExamples.Construction.ComposedSumcheckProofBodies.helper17, helper18 := ZkcExamples.Construction.ComposedSumcheckProofBodies.helper18, helper19 := ZkcExamples.Construction.ComposedSumcheckProofBodies.helper19, helper20 := ZkcExamples.Construction.ComposedSumcheckProofBodies.helper20, helper21 := ZkcExamples.Construction.ComposedSumcheckProofBodies.helper21, helper22 := ZkcExamples.Construction.ComposedSumcheckProofBodies.helper22, helper23 := ZkcExamples.Construction.ComposedSumcheckProofBodies.helper23, helper24 := ZkcExamples.Construction.ComposedSumcheckProofBodies.helper24, helper25 := ZkcExamples.Construction.ComposedSumcheckProofBodies.helper25, helper26 := ZkcExamples.Construction.ComposedSumcheckProofBodies.helper26, helper27 := ZkcExamples.Construction.ComposedSumcheckProofBodies.helper27, helper28 := ZkcExamples.Construction.ComposedSumcheckProofBodies.helper28, helper29 := ZkcExamples.Construction.ComposedSumcheckProofBodies.helper29, helper30 := ZkcExamples.Construction.ComposedSumcheckProofBodies.helper30, helper31 := ZkcExamples.Construction.ComposedSumcheckProofBodies.helper31]
  protocols [protocol0 := ZkcExamples.Construction.ComposedSumcheckProofBodies.protocol0, proof := ZkcExamples.Construction.ComposedSumcheckProofBodies.proof]

theorem admitted : Structured.check ZkcExamples.Construction.ComposedSumcheckProofData.snapshot = .ok program := kernel_admission

abbrev snapshot := ZkcExamples.Construction.ComposedSumcheckProofData.snapshot
abbrev participant := ZkcExamples.Construction.ComposedSumcheckProofParticipant.participant

/-! ## The constructed validator and its checked selection -/

set_option smartUnfolding true in
/-- The composed per-compile Uniform.check accepts the actual export against the
admitted original. -/
theorem compiled : Uniform.checkCompiled imported participant = .ok () := by decide +kernel

set_option smartUnfolding true in
/-- The selection of the export's inputs and acceptance output, constructed from
the admitted original and the export's policy. -/
def selection : Uniform.Selection imported.program.payload.entry.outputs :=
  (Uniform.select imported participant).get (by decide +kernel)

theorem selected : Uniform.select imported participant = some selection := (Option.some_get _).symm

set_option smartUnfolding true in
/-- The selection Uniform.check accepts the export. -/
theorem selection_checked : selection.check imported participant = true := by decide +kernel

/-- The occurrence context the Uniform.check derives from the original roster and the
exported policy. -/
def context : Context := selection.context

theorem context_admitted : Uniform.exportContext ZkcExamples.Construction.ComposedSumcheckProofData.snapshot participant = some context :=
  (select_sound imported participant selected).1

set_option smartUnfolding true in
/-- The derived context: entry, roster, producer and validator positions, the
replaced service input, its contract and the draw request its challenges
carry, the suite and the selected query/delivery sites. -/
theorem context_eq : context =
    Context.fiatShamir ZkcExamples.Construction.ComposedSumcheckProofData.snapshot.entry ["role00000000", "role00000001"] 0 1 5 "random.bls12-381.fr/0" (some (.draw "bls12-381.fr")) participant.policy.suite [("apply_14_label_6c656674_label_6368616c6c656e6765", "apply_14_label_6c656674_label_64656c6976657279_0"), ("apply_16_label_7269676874_label_6368616c6c656e6765", "apply_16_label_7269676874_label_64656c6976657279_0")] := by
  decide +kernel

/-- The composed Uniform.check's two rules, each on the actual export. -/
theorem compiled_rules : Uniform.checkExport ZkcExamples.Construction.ComposedSumcheckProofData.snapshot participant = .ok () ∧ Uniform.check context participant = .ok () ∧
    Uniform.project program context participant = .ok () := by
  have accepted := compiled
  unfold Uniform.checkCompiled at accepted
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

/-- The per-compile construction Uniform.check accepts the actual export. -/
theorem accepted : Uniform.checkExport ZkcExamples.Construction.ComposedSumcheckProofData.snapshot participant = .ok () := compiled_rules.1

/-- The transcript-construction rule accepts the actual export. -/
theorem checked : Uniform.check context participant = .ok () := compiled_rules.2.1

/-- The participant projection rule accepts the actual export. -/
theorem projected : Uniform.project program context participant = .ok () := compiled_rules.2.2

set_option smartUnfolding true in
theorem validator_eq : context.validator = 1 := by decide +kernel

set_option smartUnfolding true in
theorem producer_eq : context.producer = 0 := by decide +kernel

/-- Where the export returns the selected acceptance output. -/
def acceptancePosition : Nat := selection.position

theorem acceptance_admitted : Uniform.exportAcceptance ZkcExamples.Construction.ComposedSumcheckProofData.snapshot participant = some acceptancePosition :=
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
def inputs (left right : List F) (leftSum rightSum : F) (rounds : Nat) : List (Value F G) :=
  [.vector "bls12-381.fr" left, .vector "bls12-381.fr" right, .data (.field "bls12-381.fr" leftSum), .data (.field "bls12-381.fr" rightSum), .index rounds]

/-- The validator's original inputs: the published values at their positions,
absent inputs of other roles, and the challenge service handle. -/
def verifierInputs (left right : List F) (leftSum rightSum : F) (rounds : Nat) (handle : Nat) :
    Values (Component (assignment F G)) program.payload.entry.inputs :=
  .cons (some left) (.cons (some right) (.cons (some leftSum) (.cons (some rightSum) (.cons (some rounds) (.cons (some handle) (.nil))))))

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The constructed program's data inputs hold the validator's original inputs:
the published values at their exported positions and the handle as the replaced
service. -/
theorem inputs_related (left right : List F) (leftSum rightSum : F) (rounds : Nat) (handle : Nat) (initial : History F G) :
    HoldsValues handle (inputs left right leftSum rightSum rounds ++ [.transcript initial])
      (Uniform.inputSlots context participant.policy program.payload.entry.inputs)
      (verifierInputs (F := F) (G := G) left right leftSum rightSum rounds handle) :=
  (selection_sound (F := F) (G := G) imported participant selected selection_checked).2.1 handle
    (.cons left (.cons right (.cons leftSum (.cons rightSum (.cons rounds (.nil)))))) [.transcript initial]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The constructed program's data inputs are the published inputs and the
initial transcript. -/
theorem inputs_arity (left right : List F) (leftSum rightSum : F) (rounds : Nat) :
    (inputs (F := F) (G := G) left right leftSum rightSum rounds).length + 1 = participant.inputs.length :=
  rfl

/-- Helper calls of the constructed program denote the original's checked
helpers. -/
abbrev table : Structured.Meanings F G := Uniform.helperTable program F G

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The decision among the validator's outputs is its acceptance output. -/
theorem decision_outputs (outputs : Values (Component (assignment F G)) program.payload.entry.outputs) :
    decision (validatorOutputs 1 program.payload.entry.outputScopes outputs) = outputs.get .here :=
  (selection_sound (F := F) (G := G) imported participant selected selection_checked).2.2.2 outputs

/-- The admitted root's validator process, read through its acceptance output. -/
def process (left right : List F) (leftSum rightSum : F) (rounds : Nat) (handle : Nat) : PIR.Process (participantInterface F G) (Option Bool) :=
  (program.participant F G 1 (verifierInputs left right leftSum rightSum rounds handle)).bind fun outputs =>
    .done (outputs.get .here)

/-- The original validator, read through its acceptance output. -/
def verifier (left right : List F) (leftSum rightSum : F) (rounds : Nat) (handle : Nat) : PIR.Process (Actions F G) (Option Bool) :=
  (process left right leftSum rightSum rounds handle).interpret CommonAdapter.project

/-- The original validator, read through its outputs, is the verifier. -/
theorem original_verifier (left right : List F) (leftSum rightSum : F) (rounds : Nat) (handle : Nat) :
    ((program.participant F G context.validator (verifierInputs left right leftSum rightSum rounds handle)).bind fun outputs =>
      .done (decision (validatorOutputs context.validator program.payload.entry.outputScopes
        outputs))).interpret CommonAdapter.project = verifier left right leftSum rightSum rounds handle := by
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
    (challenge : History F G → m F) (left right : List F) (leftSum rightSum : F) (rounds : Nat) (handle : Nat) (initial : History F G)
    (proof : Proof F G) :
    (fun result => (mapOutcome acceptance result.1, result.2)) <$>
        ideal context challenge table participant.returned participant.instructions
          (inputs left right leftSum rightSum rounds ++ [.transcript initial]) proof =
      transform context challenge (verifier left right leftSum rightSum rounds handle) initial proof :=
  (compiled_selected imported participant compiled selected selection_checked).2 challenge handle
    (.cons left (.cons right (.cons leftSum (.cons rightSum (.cons rounds (.nil)))))) initial proof

/-- By the construction rule alone, the compiled verifier is the Fiat–Shamir
transform of the interactive reading of its exported instructions, read through
the acceptance output, for every service handle. -/
theorem spec_transform {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (handle : Nat) (data : List (Value F G))
    (arity : data.length = 5) (initial : History F G) (proof : Proof F G) :
    (fun result => (mapOutcome acceptance result.1, result.2)) <$>
        ideal context challenge table participant.returned participant.instructions
          (data ++ [.transcript initial]) proof =
      transform context challenge
        ((spec context handle table participant.returned participant.instructions
          (data ++ [.transcript initial])).bind fun values => .done (acceptance values))
        initial proof := by
  rw [check_sound context challenge handle table participant checked data initial proof
    (by rw [arity]; rfl), transform_bind_done]

end ZkcExamples.Construction.ComposedSumcheckProof
