module

public import ZkcExamples.Executable.SumcheckHelpers
public import Zkc.Executable.Pruning

@[expose] public section

/-! The executable Sumcheck proof verifier.

`SumcheckProofProgramData` is the validator participant of the `zkc.program/0`
candidate that the native deployment of the Sumcheck example's `example::Proof`
carries and the runtime admits. The lowering rule accepts it against the
constructed validator that the composed transcript-construction and
participant projection check accepted (`accepted`): it reads back as exactly
those instructions, with the round loop of at most two iterations and the three
helper calls, and its local functions of the called helpers implement the
source's checked helpers (`SumcheckHelpers.prepared`).

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

abbrev validator : Validator := SumcheckProofProgramData.validator

set_option maxRecDepth 20000 in
/-- The reading of the executable validator. -/
def lowered : Lowered :=
  (checkLowering installed SumcheckProof.participant validator).toOption.get (by decide +kernel)

/-- The per-compile lowering rule accepts the actual executable validator. -/
theorem accepted : checkLowering installed SumcheckProof.participant validator = .ok lowered :=
  ok_of_isSome _ _

/-- The constructed validator calls the empty point, the point extension and
the terminal check by name. -/
theorem helpers : Instruction.helpers SumcheckProof.participant.instructions =
    [ZkcExamples.Structured.SumcheckHelperBodies.emptyHelper.name,
      ZkcExamples.Structured.SumcheckHelperBodies.appendHelper.name,
      ZkcExamples.Structured.SumcheckHelperBodies.checkHelper.name] := by
  rw [← Instruction.helperList_eq]
  decide +kernel

/-- A round message coordinate: a scalar field element. -/
abbrev coordinate : PhysicalType := ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩

/-- The receive types of one round: its two message coordinates. -/
abbrev round : List PhysicalType := [coordinate, coordinate]

set_option maxRecDepth 20000 in
/-- The receive plan: a loop over the round count, at most two rounds, each
receiving two coordinates. -/
theorem plan_eq : lowered.plan = [.loop 2 2 [.receive coordinate, .receive coordinate]] := by
  decide +kernel

/-- The receive types of a run: two field messages per admitted round. -/
def receives (rounds : Nat) : List PhysicalType :=
  if rounds ≤ 2 then (List.replicate rounds round).flatten else []

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem plan_types (values : List F) (claim : F) (rounds : Nat) :
    Plan.types (SumcheckProof.inputs (G := G) values claim rounds) lowered.plan = receives rounds := by
  rw [plan_eq]
  by_cases admitted : rounds ≤ 2 <;>
    simp [Plan.types, SumcheckProof.inputs, receives, admitted, round]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The executable admits the validator's data inputs: table values, claim and
round count. -/
theorem admitted (values : List F) (claim : F) (rounds : Nat) :
    validator.admits (SumcheckProof.inputs (G := G) values claim rounds) = true := by
  rfl

/-- Every helper the reading calls is prepared. -/
theorem prepared : ∀ name ∈ Instruction.helpers SumcheckProof.participant.instructions,
    Prepared installed validator (helperTable SumcheckProof.program F G) name := by
  rw [helpers]
  exact SumcheckHelpers.prepared

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
    (checkLowering_sound accepted).1 _ initial bytes (admitted values claim rounds)

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
  obtain ⟨reading, code, returned, -⟩ := checkLowering_sound accepted
  rw [← code, ← returned, ← plan_types (G := G) values claim rounds]
  exact validate_prunes installed validator SumcheckProof.context challenge _ decode budget _ prepared reading
    binding SumcheckProof.acceptancePosition _ initial bytes (admitted values claim rounds)

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

end ZkcExamples.Executable.SumcheckProof
