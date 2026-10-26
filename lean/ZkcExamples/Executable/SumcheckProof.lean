module

public import ZkcExamples.Executable.SumcheckProofFacts
public import ZkcExamples.Executable.SumcheckHelpers
public import ZkcExamples.Executable.SumcheckFamily
public import Zkc.Executable.NormalizationSoundness

@[expose] public section

/-! The executable Sumcheck proof verifier.

`SumcheckProofProgramData` is the validator participant of the `zkc.program/0`
candidate that the native deployment of the Sumcheck example's `example::Proof`
carries and the runtime admits. The lowering rule accepts it against the
constructed validator that the composed transcript-construction and
participant projection check accepted (`accepted`): it reads back as exactly
those instructions, with the round loop bounded by the Entry's static maximum
(`maximum`) and the three helper calls, and its local functions of the called
helpers implement the source's checked helpers (`SumcheckHelpers.prepared`).
The lowering facts are generated (`SumcheckProofFacts`, in this namespace).

The kernel recognizes the pair as an artifact of the Sumcheck family
(`artifact`, `ZkcExamples.Executable.SumcheckFamily.Artifact`): the family's
shape with this Entry's names and maximum, the reading's code and receive
plan, the occurrence templates the context names, and the helper meanings of
the admitted original. The family's theorems for every round count up to the
maximum then apply to it (`SumcheckCharges`, `SumcheckCompleteness`).

For every challenge function in every lawful monad, decoder, budget, data
input, initial transcript and proof byte string, the executable's observation
is the metered meaning of the reading on the proof its message bytes decode to,
at the receive types of the round count (`executable_metered`). Host
validation prunes the ideal acceptance of the decoded proof by rejections, at
every budget and with every framing header (`executable_prunes`); with the
composed rules' theorem for this Entry
(`ZkcExamples.Construction.SumcheckProof.compiled_transform`) that ideal
acceptance is the acceptance of the Fiat–Shamir transform of the original
Sumcheck validator (`executable_transform_prunes`).
-/

set_option autoImplicit false

namespace ZkcExamples.Executable.SumcheckProof
open Zkc.Construction Zkc.Executable
open ZkcExamples.Construction

/-- The constructed validator calls the empty point, the point extension and
the terminal check by name. -/
theorem helpers_named : Instruction.helpers SumcheckProof.participant.instructions =
    [ZkcExamples.Structured.SumcheckHelperBodies.emptyHelper.name,
      ZkcExamples.Structured.SumcheckHelperBodies.appendHelper.name,
      ZkcExamples.Structured.SumcheckHelperBodies.checkHelper.name] :=
  helpers

/-- The helper calls of the constructed validator, at the result sorts of the
called helpers. -/
theorem calls : Instruction.callList SumcheckProof.participant.instructions =
    [ZkcExamples.Structured.SumcheckHelperBodies.emptyHelper,
      ZkcExamples.Structured.SumcheckHelperBodies.appendHelper,
      ZkcExamples.Structured.SumcheckHelperBodies.checkHelper].map
      fun helper => (helper.name, helper.outputs.map .data) := by
  decide +kernel

/-- A round message coordinate: a scalar field element. -/
abbrev coordinate : PhysicalType := ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩

/-- The receive types of one round: its two message coordinates. -/
abbrev round : List PhysicalType := [coordinate, coordinate]

/-- The Entry's static maximum: the round loop's bound. -/
def maximum : Nat := SumcheckShape.maximumOf SumcheckProof.participant.instructions

/-- This Entry admits at most two rounds. -/
theorem maximum_eq : maximum = 2 := by decide +kernel

/-- The names of this Entry's sites, templates and helpers. -/
def names : SumcheckShape.Names := SumcheckShape.Names.of SumcheckProof.participant.instructions

set_option maxRecDepth 20000 in
/-- The receive plan: a loop over the round count, at most `maximum` rounds,
each receiving two coordinates. -/
theorem plan_eq : lowered.plan = [.loop 2 maximum [.receive coordinate, .receive coordinate]] := by
  decide +kernel

/-- The receive types of a run: two field messages per admitted round. -/
def receives (rounds : Nat) : List PhysicalType :=
  if rounds ≤ maximum then (List.replicate rounds round).flatten else []

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem plan_types (values : List F) (claim : F) (rounds : Nat) :
    Plan.types (SumcheckProof.inputs (G := G) values claim rounds) lowered.plan = receives rounds := by
  rw [plan_eq]
  by_cases admitted : rounds ≤ maximum <;>
    simp [Plan.types, SumcheckProof.inputs, receives, admitted, round]

/-- Every helper the reading calls is prepared. -/
theorem prepared : ∀ name ∈ Instruction.helpers SumcheckProof.participant.instructions,
    Prepared installed validator (helperTable SumcheckProof.program F G) name := by
  rw [helpers_named]
  exact SumcheckHelpers.prepared

/-- Every helper the reading calls returns values of its declared result sorts. -/
theorem helpersSorted : ∀ call ∈ Instruction.callList SumcheckProof.participant.instructions,
    HelperSorted (helperTable SumcheckProof.program F G) call.1 call.2 := by
  have sorted : ∀ (helper : Zkc.Source.Structured.Helper) {body},
      Zkc.Source.Structured.BodyIn ZkcExamples.Structured.SumcheckSourceViews.unit.definitions helper body →
      HelperSorted (helperTable SumcheckProof.program F G) helper.name (helper.outputs.map .data) := by
    intro helper body association
    apply helperSorted_of_outputs
    intro entry found
    obtain ⟨entry', found', same⟩ :=
      Uniform.helperTable_lookup (F := F) (G := G) SumcheckProof.program helper (SumcheckHelpers.present association)
    rw [found] at found'
    cases found'
    rw [same]
  rw [calls]
  intro call member
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact sorted _ ZkcExamples.Structured.SumcheckSourceContracts.bodies.empty
  · exact sorted _ ZkcExamples.Structured.SumcheckSourceContracts.bodies.append
  · exact sorted _ ZkcExamples.Structured.SumcheckSourceAssociations.check_association

/-- For every challenge function in every lawful monad, decoder and budget, the
executable's observation is the metered meaning of the reading on the proof its
message bytes decode to. -/
theorem executable_metered {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (decode : PhysicalType → List UInt8 → Option (Payload F G))
    (budget : Nat) (values : List F) (claim : F) (rounds : Nat) (initial : History F G)
    (bytes : List UInt8) :
    Run.observe <$> execute installed validator SumcheckProof.context challenge decode budget
        (SumcheckProof.inputs values claim rounds) initial bytes =
      idealObservation <$> metered SumcheckProof.context challenge (helperTable SumcheckProof.program F G)
        (helperCost installed validator) budget lowered
        (SumcheckProof.inputs values claim rounds ++ [.transcript initial])
        (decodeProof decode (receives rounds) bytes) := by
  rw [← plan_types (G := G) values claim rounds]
  exact execute_metered installed validator SumcheckProof.context challenge _ decode budget _ prepared
    (checkLowering_spec accepted).1 _ initial bytes (admitted values claim rounds)

/-- Host validation of proof bytes prunes the ideal acceptance of the decoded
proof by rejections, at every budget and with every framing header. -/
theorem executable_prunes {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (decode : PhysicalType → List UInt8 → Option (Payload F G))
    (budget : Nat) (binding : List UInt8) (values : List F) (claim : F) (rounds : Nat)
    (initial : History F G) (bytes : List UInt8) :
    Prunes (fun accepted => accepted = false)
      (validate installed validator SumcheckProof.context challenge decode budget binding
        SumcheckProof.acceptancePosition (SumcheckProof.inputs values claim rounds) initial bytes)
      ((fun result => Accepts SumcheckProof.acceptancePosition (idealObservation result)) <$>
        ideal SumcheckProof.context challenge (helperTable SumcheckProof.program F G)
          SumcheckProof.participant.returned SumcheckProof.participant.instructions
          (SumcheckProof.inputs values claim rounds ++ [.transcript initial])
          (decodeProof decode (receives rounds) (bytes.drop 40))) := by
  rw [← plan_types (G := G) values claim rounds]
  exact validate_prunes_export installed validator SumcheckProof.context challenge _ decode budget accepted
    prepared helpersSorted binding SumcheckProof.acceptancePosition _ initial bytes (admitted values claim rounds)

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Acceptance of a verifier's result: it returned the decision true and read
the whole proof. -/
def accepting (result : PIR.Outcome (Option Bool) × Proof F G) : Bool :=
  match result.1, result.2 with
  | .returned (some decision), [] => decision
  | _, _ => false

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Host acceptance of an ideal result is the acceptance of its decision. -/
theorem accepts_eq (result : PIR.Outcome (List (Value F G)) × Proof F G) :
    Accepts SumcheckProof.acceptancePosition (idealObservation result) =
      accepting (mapOutcome SumcheckProof.acceptance result.1, result.2) := by
  rcases result with ⟨outcome, unread⟩
  cases outcome with
  | stopped stop => simp [Accepts, idealObservation, observation, Decision, accepting, mapOutcome]
  | returned values =>
      simp only [Accepts, idealObservation, observation, Decision, selectedTrue, mapOutcome,
        SumcheckProof.acceptance]
      cases values[SumcheckProof.acceptancePosition]? with
      | none => cases unread <;> simp [accepting]
      | some value =>
          rcases value with ⟨(_ | _) | _ | _⟩ | _ | _ | _ | _ <;> cases unread <;> simp [accepting]

/-- Host validation of proof bytes prunes, by rejections, the acceptance of the
Fiat–Shamir transform of the original Sumcheck validator on the decoded proof,
at every budget and with every framing header. -/
theorem executable_transform_prunes {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (decode : PhysicalType → List UInt8 → Option (Payload F G))
    (budget : Nat) (binding : List UInt8) (values : List F) (claim : F) (rounds handle : Nat)
    (initial : History F G) (bytes : List UInt8) :
    Prunes (fun accepted => accepted = false)
      (validate installed validator SumcheckProof.context challenge decode budget binding
        SumcheckProof.acceptancePosition (SumcheckProof.inputs values claim rounds) initial bytes)
      (accepting <$> transform SumcheckProof.context challenge
        (SumcheckProof.verifier values claim rounds handle) initial
        (decodeProof decode (receives rounds) (bytes.drop 40))) := by
  rw [← SumcheckProof.compiled_transform challenge values claim rounds handle initial, Functor.map_map]
  simp only [← accepts_eq]
  exact executable_prunes challenge decode budget binding values claim rounds initial bytes

/-! ## The artifact -/

theorem names_scalar : names.scalar = "bls12-381.fr" := by decide +kernel
theorem names_empty : names.emptyHelper = ZkcExamples.Structured.SumcheckHelperBodies.emptyHelper.name := by
  decide +kernel
theorem names_append : names.appendHelper = ZkcExamples.Structured.SumcheckHelperBodies.appendHelper.name := by
  decide +kernel
theorem names_check : names.checkHelper = ZkcExamples.Structured.SumcheckHelperBodies.checkHelper.name := by
  decide +kernel

set_option maxRecDepth 20000 in
/-- The compiled Sumcheck validator of this Entry as an artifact of the family. -/
def artifact : SumcheckFamily.Artifact where
  validator := validator
  participant := SumcheckProof.participant
  context := SumcheckProof.context
  program := SumcheckProof.program
  lowered := lowered
  accepted := accepted
  names := names
  maximum := maximum
  small := by decide +kernel
  shape := by decide +kernel
  code := by decide +kernel
  returned := rfl
  sorts := by decide +kernel
  coordinate := coordinate
  plan := plan_eq
  admitted := fun values claim rounds => by rw [names_scalar]; rfl
  templates := by decide +kernel
  emptyBound := by decide +kernel
  roundCharges := by decide +kernel
  empty_call := by rw [names_empty, names_scalar]; exact SumcheckHelpers.empty_call
  append_call := fun point answer => by rw [names_append, names_scalar]; exact SumcheckHelpers.append_call point answer
  check_call := fun xs point claim vectorBound pointBound => by
    rw [names_check, names_scalar]; exact SumcheckHelpers.check_call vectorBound pointBound
  check_cost := fun xs point claim small shaped => by
    rw [names_check, names_scalar]; exact SumcheckHelpers.check_cost small shaped
  prepared := prepared
  helpersSorted := helpersSorted

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem artifact_inputs (values : List F) (claim : F) (rounds : Nat) :
    artifact.inputs (G := G) values claim rounds = SumcheckProof.inputs values claim rounds := by
  simp only [SumcheckFamily.Artifact.inputs, artifact, names_scalar]
  rfl

theorem artifact_receives (rounds : Nat) : artifact.receives rounds = receives rounds := rfl

theorem artifact_validator : artifact.validator = validator := by unfold artifact; rfl
theorem artifact_participant : artifact.participant = SumcheckProof.participant := by unfold artifact; rfl
theorem artifact_context : artifact.context = SumcheckProof.context := by unfold artifact; rfl
theorem artifact_program : artifact.program = SumcheckProof.program := by unfold artifact; rfl
theorem artifact_lowered : artifact.lowered = lowered := by dsimp only [artifact]
theorem artifact_maximum : artifact.maximum = maximum := by unfold artifact; rfl
theorem artifact_coordinate : artifact.coordinate = coordinate := by unfold artifact; rfl

end ZkcExamples.Executable.SumcheckProof
