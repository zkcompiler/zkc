module

public import ZkcExamples.Structured.GkrSourceViews
public import ZkcExamples.Construction.GkrProofParticipant
public import Zkc.Construction.Compiled
public import Zkc.Source.Structured.CommonAdapter

@[expose] public section

/-! The compiled non-interactive GKR verifier of `example::Proof`.

The Proof Entry's original export is the admitted GKR source `GkrSourceData`:
the construction bridge checks that it renders to exactly the same data.
`GkrProofParticipant` is the compiler's constructed validator for the Entry: the
output-point loop, then the layer loop with the two `Rounds` applications as
inner loops, the line polynomial's coefficients, the wiring check as a guard,
the line challenge and the next claim, and finally the input check. The
transcript-construction rule and the participant projection rule both accept it
(`compiled`). By their composed soundness the compiled verifier's ideal meaning
is the Fiat–Shamir transform of the original GKR validator for every challenge
function (`compiled_transform`); by the construction rule alone it is the
Fiat–Shamir transform of the interactive reading of the exported instructions
(`spec_transform`). No equation specific to this Entry is assumed.
-/

namespace ZkcExamples.Construction.GkrProof
open Zkc.Source Zkc.Source.Structured Zkc.Construction

set_option smartUnfolding false

abbrev program := ZkcExamples.Structured.GkrSourceViews.program
/-- The admitted original: the GKR source and the program it admits. -/
abbrev imported : Structured.Imported ZkcExamples.Structured.GkrSourceData.snapshot :=
  ZkcExamples.Structured.GkrSourceViews.imported
abbrev participant := GkrProofParticipant.participant

/-- The occurrence context the check derives from the original roster and the
exported policy. -/
def context : Context :=
  (exportContext ZkcExamples.Structured.GkrSourceData.snapshot participant).get (by decide +kernel)

theorem context_admitted :
    exportContext ZkcExamples.Structured.GkrSourceData.snapshot participant = some context := by
  rfl

set_option smartUnfolding true in
/-- The composed per-compile check accepts the actual export against the
admitted original. -/
theorem compiled : checkCompiled imported participant = .ok () := by
  decide +kernel

/-- The composed check's two rules, each on the actual export. -/
theorem compiled_rules : check context participant = .ok () ∧
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
    exact ⟨checked, accepted⟩
  · cases accepted
  · cases accepted

/-- The transcript-construction rule accepts the actual export. -/
theorem accepted : check context participant = .ok () := compiled_rules.1

/-- The participant projection rule accepts the actual export. -/
theorem projected : project program context participant = .ok () := compiled_rules.2

theorem validator_eq : context.validator = 1 := by rw [show context = _ from rfl]; rfl

theorem producer_eq : context.producer = 0 := by rw [show context = _ from rfl]; rfl

set_option smartUnfolding true in
/-- Where the export returns the selected acceptance output. -/
def acceptancePosition : Nat :=
  (exportAcceptance ZkcExamples.Structured.GkrSourceData.snapshot participant).get (by decide +kernel)

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

/-- Data inputs of the constructed validator: the circuit's input values, the
claimed outputs, the stacked add and mul wiring tables, the number of layers,
the number of selector coordinates and the width. -/
def inputs (values outputs add mul : List F) (layers selector width : Nat) : List (Value F G) :=
  [.vector "bls12-381.fr" values, .vector "bls12-381.fr" outputs, .vector "bls12-381.fr" add,
    .vector "bls12-381.fr" mul, .index layers, .index selector, .index width]

/-- The validator's original inputs: the public statement and the challenge
service handle. -/
abbrev verifierInputs (values outputs add mul : List F) (layers selector width handle : Nat) :
    Values (Component (assignment F G)) program.payload.entry.inputs :=
  .cons (some values) (.cons (some outputs) (.cons (some add) (.cons (some mul)
    (.cons (some layers) (.cons (some selector) (.cons (some width) (.cons (some handle) .nil)))))))

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The constructed program's data inputs hold the validator's original inputs. -/
theorem inputs_related (values outputs add mul : List F) (layers selector width handle : Nat)
    (initial : History F G) :
    HoldsValues handle (inputs values outputs add mul layers selector width ++ [.transcript initial])
      (inputSlots context participant.policy program.payload.entry.inputs)
      (verifierInputs (G := G) values outputs add mul layers selector width handle) := by
  have slotsEq : inputSlots context participant.policy program.payload.entry.inputs =
      [.held 0, .held 1, .held 2, .held 3, .held 4, .held 5, .held 6, .service] := by
    rfl
  rw [slotsEq]
  refine ⟨⟨values, rfl, ?_⟩, ⟨outputs, rfl, ?_⟩, ⟨add, rfl, ?_⟩, ⟨mul, rfl, ?_⟩,
    ⟨layers, rfl, ?_⟩, ⟨selector, rfl, ?_⟩, ⟨width, rfl, ?_⟩, rfl, trivial⟩ <;>
    simp [inputs, Value.decode]

/-- The original GKR validator, read through its acceptance output. -/
def verifier (values outputs add mul : List F) (layers selector width handle : Nat) :
    PIR.Proc (Actions F G) (Option Bool) :=
  ((program.participant F G 1 (verifierInputs values outputs add mul layers selector width handle)).bind
    fun outputs => .done (outputs.get .here)).interpret CommonAdapter.project

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The decision among the validator's outputs is its acceptance output. -/
theorem decision_outputs (outputs : Values (Component (assignment F G)) program.payload.entry.outputs) :
    decision (validatorOutputs 1 program.payload.entry.outputScopes outputs) = outputs.get .here := by
  have scopesEq : program.payload.entry.outputScopes = [[1]] := rfl
  rw [scopesEq]
  rcases outputs with _ | ⟨value, _ | _⟩
  simp only [decision, acceptancePosition_eq]
  cases value <;> rfl

/-- The compiled GKR verifier, under the ideal transcript model with any
challenge function in any lawful monad, is the Fiat–Shamir transform of the
original GKR validator, with equal outcomes and unread proof suffixes. -/
theorem compiled_transform {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (values outputs add mul : List F)
    (layers selector width handle : Nat) (initial : History F G) (proof : Proof F G) :
    (fun result => (mapOutcome acceptance result.1, result.2)) <$>
        ideal context challenge (helperTable program F G) participant.returned participant.instructions
          (inputs values outputs add mul layers selector width ++ [.transcript initial]) proof =
      transform context challenge (verifier values outputs add mul layers selector width handle)
        initial proof := by
  obtain ⟨context', found, composed⟩ :=
    Zkc.Construction.compiled_transform (F := F) (G := G) imported participant compiled
  rw [context_admitted] at found
  cases found
  dsimp only [imported, ZkcExamples.Structured.GkrSourceViews.imported] at composed
  rw [composed challenge acceptance decision acceptance_decision handle
    (inputs values outputs add mul layers selector width) initial proof
    (verifierInputs values outputs add mul layers selector width handle)
    (inputs_related values outputs add mul layers selector width handle initial) rfl]
  unfold verifier
  rw [validator_eq]
  simp only [decision_outputs]

/-- The compiled GKR verifier is the Fiat–Shamir transform of the interactive
reading of its exported instructions, read through the acceptance output, for
every service handle. -/
theorem spec_transform {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (handle : Nat) (data : List (Value F G))
    (arity : data.length = 7) (initial : History F G) (proof : Proof F G) :
    (fun result => (mapOutcome acceptance result.1, result.2)) <$>
        ideal context challenge (helperTable program F G) participant.returned participant.instructions
          (data ++ [.transcript initial]) proof =
      transform context challenge
        ((spec context handle (helperTable program F G) participant.returned participant.instructions
          (data ++ [.transcript initial])).bind fun values => .done (acceptance values))
        initial proof := by
  rw [check_sound context challenge handle (helperTable program F G) participant accepted data initial
    proof (by rw [arity]; rfl), transform_bind_done]

end ZkcExamples.Construction.GkrProof
