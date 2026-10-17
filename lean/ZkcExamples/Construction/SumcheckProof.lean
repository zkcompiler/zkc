module

public import ZkcExamples.Structured.SumcheckSourceVerifier
public import ZkcExamples.Construction.SumcheckProofParticipant
public import Zkc.Construction.Compiled
public import Zkc.Source.Structured.CommonAdapter

@[expose] public section

/-! The compiled non-interactive Sumcheck verifier of `example::Proof`.

The Proof Entry's original export is the admitted Sumcheck source
`SumcheckSourceData`: the bridge checks that it renders to exactly the same
data. `SumcheckProofParticipant` is the compiler's constructed validator for the
Entry: one helper call, then a loop for the source repeat inside the `reduce`
application, with two received round messages, the round check as a guard, the
challenge and its delivery, and the claim update, and finally the terminal
check as a helper call. The transcript-construction rule and the participant
projection rule both accept it (`compiled`), so by their composed soundness the
compiled verifier's ideal meaning is the Fiat–Shamir transform of the original
Sumcheck validator for every challenge function (`compiled_transform`). No
equation specific to this Entry is assumed. With a decoded verifier table and an
admitted round count, the original validator is the source rounds followed by
the multilinear terminal check (`compiled_transform_rounds`).
-/

namespace ZkcExamples.Construction.SumcheckProof
open Zkc.Source Zkc.Source.Structured Zkc.Construction

set_option smartUnfolding false

abbrev program := ZkcExamples.Structured.SumcheckSourceViews.program
abbrev participant := SumcheckProofParticipant.participant

/-- The occurrence context the check derives from the original roster and the
exported policy. -/
def context : Context :=
  (exportContext ZkcExamples.Structured.SumcheckSourceData.snapshot participant).get (by decide +kernel)

theorem context_admitted :
    exportContext ZkcExamples.Structured.SumcheckSourceData.snapshot participant = some context := by
  rfl

set_option smartUnfolding true in
/-- The per-compile construction check accepts the actual export. -/
theorem accepted : checkExport ZkcExamples.Structured.SumcheckSourceData.snapshot participant = .ok () := by
  decide +kernel

set_option smartUnfolding true in
/-- The participant projection rule accepts the actual export. -/
theorem projected : project program context participant = .ok () := by decide +kernel

set_option smartUnfolding true in
/-- The composed per-compile check accepts the actual export. -/
theorem compiled :
    checkCompiled ZkcExamples.Structured.SumcheckSourceData.snapshot program participant = .ok () := by
  decide +kernel

theorem validator_eq : context.validator = 1 := by rw [show context = _ from rfl]; rfl

set_option smartUnfolding true in
/-- Where the export returns the selected acceptance output. -/
def acceptancePosition : Nat :=
  (exportAcceptance ZkcExamples.Structured.SumcheckSourceData.snapshot participant).get (by decide +kernel)

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

/-- Data inputs of the constructed validator: the verifier's table values, the
claimed sum and the round count. -/
def inputs (values : List F) (claim : F) (rounds : Nat) : List (Value F G) :=
  [.vector "bls12-381.fr" values, .data (.field "bls12-381.fr" claim), .index rounds]

/-- The validator's original inputs: table values, claim, round count and the
challenge service handle. -/
abbrev verifierInputs (values : List F) (claim : F) (rounds handle : Nat) :=
  ZkcExamples.Structured.SumcheckSourceVerifier.sourceRootInputs (G := G) (some values) (some claim)
    (some rounds) (some handle)

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The constructed program's data inputs hold the validator's original inputs. -/
theorem inputs_related (values : List F) (claim : F) (rounds handle : Nat) (initial : History F G) :
    HoldsValues handle (inputs values claim rounds ++ [.transcript initial])
      (inputSlots context participant.policy program.payload.entry.inputs)
      (verifierInputs (G := G) values claim rounds handle) := by
  have slotsEq : inputSlots context participant.policy program.payload.entry.inputs =
      [.held 0, .held 1, .held 2, .service] := by
    rfl
  rw [slotsEq]
  refine ⟨⟨values, rfl, ?_⟩, ⟨claim, rfl, ?_⟩, ⟨rounds, rfl, ?_⟩, rfl, trivial⟩ <;>
    simp [inputs, Value.decode]

/-- The original Sumcheck validator, read through its acceptance output. -/
def verifier (values : List F) (claim : F) (rounds handle : Nat) :
    PIR.Proc (Actions F G) (Option Bool) :=
  ((program.participant F G 1 (verifierInputs values claim rounds handle)).bind fun outputs =>
    .done (outputs.get .here)).interpret CommonAdapter.project

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The decision among the validator's outputs is its acceptance output. -/
theorem decision_outputs (outputs : Values (Component (assignment F G)) program.payload.entry.outputs) :
    decision (validatorOutputs 1 program.payload.entry.outputScopes outputs) = outputs.get .here := by
  have scopesEq : program.payload.entry.outputScopes = [[1]] := rfl
  rw [scopesEq]
  rcases outputs with _ | ⟨value, _ | _⟩
  simp only [decision, acceptancePosition_eq]
  cases value <;> rfl

/-- The compiled Sumcheck verifier, under the ideal transcript model with any
challenge function in any lawful monad, is the Fiat–Shamir transform of the
original Sumcheck validator, with equal outcomes and unread proof suffixes. -/
theorem compiled_transform {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (values : List F) (claim : F) (rounds handle : Nat)
    (initial : History F G) (proof : Proof F G) :
    (fun result => (mapOutcome acceptance result.1, result.2)) <$>
        ideal context challenge (helperTable program F G) participant.returned participant.instructions
          (inputs values claim rounds ++ [.transcript initial]) proof =
      transform context challenge (verifier values claim rounds handle) initial proof := by
  obtain ⟨context', found, composed⟩ :=
    Zkc.Construction.compiled_transform (F := F) (G := G) ZkcExamples.Structured.SumcheckSourceData.snapshot
      program participant compiled
  rw [context_admitted] at found
  cases found
  rw [composed challenge acceptance decision acceptance_decision handle (inputs values claim rounds) initial
    proof (verifierInputs values claim rounds handle) (inputs_related values claim rounds handle initial) rfl]
  unfold verifier
  rw [validator_eq]
  simp only [decision_outputs]

/-- With an admitted round count and a decoded verifier table, the compiled
verifier is the Fiat–Shamir transform of the source rounds followed by the
multilinear terminal check of the final point and claim. -/
theorem compiled_transform_rounds {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (rounds : Nat) (admitted : rounds ≤ 2) (values : List F) (claim : F)
    (handle : Nat) (table : Zkc.Polynomial.Multilinear.Table F rounds)
    (decoded : Zkc.Polynomial.Multilinear.ofList? rounds values = some table)
    (vectorBound : values.length < indexLimit) (initial : History F G) (proof : Proof F G) :
    (fun result => (mapOutcome acceptance result.1, result.2)) <$>
        ideal context challenge (helperTable program F G) participant.returned participant.instructions
          (inputs values claim rounds ++ [.transcript initial]) proof =
      transform context challenge
        (((PIR.repeatN rounds (ZkcExamples.Structured.SumcheckVerifierLaws.roundPlain (G := G)
            ZkcExamples.Structured.SumcheckSourceVerifier.childContext (some handle)) (some [], some claim)).bind
          (fun pc => match pc.1, pc.2 with
            | some point, some value => .done (some (decide (point.length = rounds ∧
                Zkc.Polynomial.Multilinear.extension rounds table
                  (Zkc.Polynomial.coordinates rounds point) = value)))
            | _, _ => .halt .incomplete)).interpret CommonAdapter.project) initial proof := by
  rw [compiled_transform challenge values claim rounds handle initial proof]
  unfold verifier
  rw [ZkcExamples.Structured.SumcheckSourceVerifier.verifier_checked rounds admitted values (some claim)
    (some handle) table decoded vectorBound]
  congr 2
  rw [PIR.Proc.bind_assoc]
  congr 1
  funext pc
  rcases pc with ⟨_ | point, _ | value⟩ <;> rfl

end ZkcExamples.Construction.SumcheckProof
