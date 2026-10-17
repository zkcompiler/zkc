module

public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.Construction.SchnorrAndProofData
public import ZkcExamples.Construction.SchnorrAndProofBodies
public import ZkcExamples.Construction.SchnorrAndProofParticipant
public import Zkc.Construction.Compiled
public import Zkc.Source.Structured.CommonAdapter

@[expose] public section

/-! The compiled non-interactive Schnorr AND verifier of the Sigma example.

`examples/projects/sigma` declares `example::AndProof` over the `SchnorrAnd`
protocol of `libraries/sigma`: two Schnorr statements with independent witnesses and one shared challenge, whose verifier checks both equations. `SchnorrAndProofData` is the Entry's
original export, whose protocol additionally retains its proof statement, and
`SchnorrAndProofParticipant` its constructed validator, in which the final
conjunction of the two checked equations is a Boolean conjunction.
`SchnorrAndProofBodies` holds the typed bodies printed from the admitted original
by `bridges/structured/bodies.py`; `structured_views` admits the original from
them in the kernel, so a printing error is refused, and gives the literal
checked program `program`.

The composed transcript-construction and participant projection check accepts
the export (`compiled`), so the generic composition theorem applies with no
equation specific to this Entry. `compiled_transform` instantiates it at the
Entry's public inputs (`inputs_related`) and acceptance output
(`acceptance_decision`): for every challenge function, the compiled verifier's
ideal meaning is the Fiat–Shamir transform of the original validator. No
security theorem about the compiled verifier is stated here; the Fiat–Shamir
theorems of the Sigma compositions are about the transforms of the imported
interactive verifiers.
-/

namespace ZkcExamples.Construction.SchnorrAndProof
open Zkc.Source Zkc.Source.Structured Zkc.Construction

set_option smartUnfolding false

/-! ## The original Proof Entry -/

structured_views SchnorrAndProofData.snapshot
  helpers [formula := SchnorrAndProofBodies.formula]
  protocols [proof := SchnorrAndProofBodies.proof]

theorem admitted : Structured.check SchnorrAndProofData.snapshot = .ok program := kernel_admission

/-! ## The constructed validator -/

abbrev snapshot := SchnorrAndProofData.snapshot
abbrev participant := SchnorrAndProofParticipant.participant

/-- The occurrence context the check derives from the original roster and the
exported policy. -/
def context : Context := (exportContext snapshot participant).get (by decide +kernel)

theorem context_admitted : exportContext snapshot participant = some context := by
  rfl

set_option smartUnfolding true in
/-- The composed per-compile check accepts the actual export. -/
theorem compiled : checkCompiled snapshot program participant = .ok () := by decide +kernel

theorem validator_eq : context.validator = 1 := by rw [show context = _ from rfl]; rfl

set_option smartUnfolding true in
/-- Where the export returns the selected acceptance output. -/
def acceptancePosition : Nat :=
  (exportAcceptance snapshot participant).get (by decide +kernel)

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
    acceptance values = decision (values.dropLast.map some) := by
  have returnedLength : participant.returned.length = 2 := rfl
  rw [returnedLength] at length
  rcases values with _ | ⟨first, _ | ⟨second, _ | _⟩⟩ <;> simp at length
  simp only [acceptance, decision, acceptancePosition_eq, List.dropLast_cons_cons,
    List.dropLast_singleton, List.map_cons, List.map_nil, List.getElem?_cons_zero]
  rcases first with ⟨_ | _ | _⟩ | _ | _ | _ | _ <;> rfl

/-- Data inputs of the constructed validator: the policy's public inputs, the
two bases and the two statement points, in original order. -/
def inputs (firstBase firstPoint secondBase secondPoint : G) : List (Value F G) :=
  [.data (.group "bls12-381.g1" firstBase), .data (.group "bls12-381.g1" firstPoint),
    .data (.group "bls12-381.g1" secondBase), .data (.group "bls12-381.g1" secondPoint)]

/-- The validator's original inputs: the public points, absent witnesses and prover nonce service, and
the challenge service handle. -/
def verifierInputs (firstBase firstPoint secondBase secondPoint : G) (handle : Nat) :
    Values (Component (assignment F G)) program.payload.entry.inputs :=
  .cons (some firstBase) (.cons (some firstPoint) (.cons (some secondBase) (.cons (some secondPoint)
    (.cons none (.cons none (.cons none (.cons (some handle) .nil)))))))

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The constructed program's data inputs hold the validator's original inputs:
the public points at their exported positions and the handle as the replaced
service. -/
theorem inputs_related (firstBase firstPoint secondBase secondPoint : G) (handle : Nat)
    (initial : History F G) :
    HoldsValues handle (inputs firstBase firstPoint secondBase secondPoint ++ [.transcript initial])
      (inputSlots context participant.policy program.payload.entry.inputs)
      (verifierInputs (F := F) firstBase firstPoint secondBase secondPoint handle) := by
  have slotsEq : inputSlots context participant.policy program.payload.entry.inputs =
      [.held 0, .held 1, .held 2, .held 3, .absent, .absent, .absent, .service] := by
    rfl
  rw [slotsEq]
  refine ⟨⟨firstBase, rfl, ?_⟩, ⟨firstPoint, rfl, ?_⟩, ⟨secondBase, rfl, ?_⟩, ⟨secondPoint, rfl, ?_⟩,
    rfl, rfl, rfl, rfl, trivial⟩ <;>
    simp [inputs, Value.decode]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The decision among the validator's outputs is its Boolean output. -/
theorem decision_outputs (outputs : Values (Component (assignment F G)) program.payload.entry.outputs) :
    decision (validatorOutputs 1 program.payload.entry.outputScopes outputs) = outputs.get .here := by
  have scopesEq : program.payload.entry.outputScopes = [[1]] := rfl
  rw [scopesEq]
  rcases outputs with _ | ⟨value, _ | _⟩
  simp only [decision, acceptancePosition_eq]
  cases value <;> rfl

/-- The original validator, read through its Boolean output. -/
def verifier (firstBase firstPoint secondBase secondPoint : G) (handle : Nat) :
    PIR.Proc (Actions F G) (Option Bool) :=
  ((program.participant F G 1 (verifierInputs firstBase firstPoint secondBase secondPoint handle)).bind
    fun outputs => .done (outputs.get .here)).interpret CommonAdapter.project

/-- The compiled verifier, under the ideal transcript model with any challenge
function in any lawful monad, is the Fiat–Shamir transform of the original
validator: equal acceptance outcomes, stops and unread proof suffixes, for every
public input, initial transcript, proof and service handle. An instance of the
composed rules' `Zkc.Construction.compiled_transform`. -/
theorem compiled_transform {m : Type → Type} [Monad m] [LawfulMonad m] (challenge : History F G → m F)
    (firstBase firstPoint secondBase secondPoint : G) (handle : Nat) (initial : History F G)
    (proof : Proof F G) :
    (fun result => (mapOutcome acceptance result.1, result.2)) <$>
        ideal context challenge (helperTable program F G) participant.returned participant.instructions
          (inputs firstBase firstPoint secondBase secondPoint ++ [.transcript initial]) proof =
      transform context challenge (verifier firstBase firstPoint secondBase secondPoint handle) initial
        proof := by
  obtain ⟨context', found, composed⟩ :=
    Zkc.Construction.compiled_transform (F := F) (G := G) snapshot program participant compiled
  rw [context_admitted] at found
  cases found
  rw [composed challenge acceptance decision acceptance_decision handle
    (inputs firstBase firstPoint secondBase secondPoint) initial proof
    (verifierInputs firstBase firstPoint secondBase secondPoint handle)
    (inputs_related firstBase firstPoint secondBase secondPoint handle initial) rfl]
  unfold verifier
  rw [validator_eq]
  simp only [decision_outputs]

end ZkcExamples.Construction.SchnorrAndProof
