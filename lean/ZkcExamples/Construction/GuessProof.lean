module

public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.Construction.GuessProofData
public import ZkcExamples.Construction.GuessProofBodies
public import ZkcExamples.Construction.GuessProofParticipant
public import Zkc.Construction.Compiled
public import Zkc.Source.Structured.OpenLaws
public import Zkc.Source.Structured.CommonAdapter

@[expose] public section

/-! The compiled non-interactive verifier of the guessing fixture's `example::Proof`.

The fixture `lean/bridges/construction/fixtures/guess.zkc` declares a protocol in
which the prover sends a guess, the verifier draws a challenge, delivers it and
accepts when the guess plus the public offset is the challenge.
`GuessProofData` is the original-stage export of its Proof Entry and
`GuessProofParticipant` the compiler's constructed validator for that Entry and
its native policy. The transcript-construction rule and the participant
projection rule both accept the pair (`compiled`), so by their composed
soundness the compiled verifier's ideal meaning is the Fiat–Shamir transform of
the original verifier for every challenge function (`compiled_transform`). The
original verifier is the participant process `experiment`: receive the guess,
query the challenge, deliver it, and return whether the guess plus the offset is
the challenge (`verifier_correspondence`, by computation).
-/

namespace ZkcExamples.Construction.GuessProof
open Zkc.Source Zkc.Source.Structured Zkc.Source.Common.Native Zkc.Construction

set_option smartUnfolding false

/-! ## The original Proof Entry -/

structured_views GuessProofData.snapshot
  helpers []
  protocols [proof := GuessProofBodies.proof]

theorem admitted : Structured.check GuessProofData.snapshot = .ok program := kernel_admission

/-- The field domain of the guess, the offset and the challenge. -/
abbrev fieldDomain : String := "bls12-381.fr"

/-- The prover's guess message site. -/
abbrev guessSite : String := "label_6775657373_0"

/-- The verifier's challenge site. -/
abbrev challengeSite : String := "label_6368616c6c656e6765"

/-- The site that delivers the challenge to the prover. -/
abbrev deliverySite : String := "label_64656c6976657279_0"

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The original verifier as a participant process: receive the guess, query
the challenge on the service `service`, deliver it to the prover, and accept
when the guess plus the offset is the challenge. -/
def experiment (offset : F) (service : Nat) : PIR.Proc (Actions F G) (Option Bool) :=
  .call (.receive (.field fieldDomain) guessSite 0) fun guess =>
  .call (.query challengeSite fieldDomain (.cons service .nil)) fun challenge =>
  .call (.send (ty := .field fieldDomain) deliverySite 0 challenge) fun _ =>
  .done (some (decide (guess + offset = challenge)))

def verifierInputs (offset : F) (challengeService : Nat) :
    Values (Component (assignment F G)) program.payload.entry.inputs :=
  .cons (some offset) (.cons none (.cons (some challengeService) .nil))

/-- The admitted root's validator process. The prover's guess input is absent. -/
def process (offset : F) (challengeService : Nat) :
    PIR.Proc (participantInterface F G) (Option Bool) :=
  (program.participant F G 1 (verifierInputs offset challengeService)).bind fun outputs =>
    .done (outputs.get .here)

theorem process_equation (offset : F) (challengeService : Nat) :
    process (G := G) offset challengeService =
      (experiment offset challengeService).interpret CommonAdapter.embed := by
  rfl

def verifier (offset : F) (service : Nat) : PIR.Proc (Actions F G) (Option Bool) :=
  (process offset service).interpret CommonAdapter.project

theorem verifier_correspondence (offset : F) (service : Nat) :
    verifier (G := G) offset service = experiment offset service := by
  rw [verifier, process_equation, CommonAdapter.project_embed]

/-! ## The constructed validator -/

abbrev participant := GuessProofParticipant.participant

/-- The occurrence context the check derives from the original roster and the
exported policy. -/
def context : Context := (exportContext GuessProofData.snapshot participant).get (by decide +kernel)

theorem context_admitted : exportContext GuessProofData.snapshot participant = some context := by
  rfl

/-- The derived context: entry, roster, producer and validator positions, the
replaced service input `2`, its contract and the draw request its challenge
carries, the suite and the selected query/delivery sites. -/
theorem context_eq : context =
    ⟨GuessProofData.snapshot.entry, ["role00000000", "role00000001"], 0, 1, 2,
      "random.bls12-381.fr/0", some (.draw fieldDomain), participant.policy.suite,
      [(challengeSite, deliverySite)]⟩ := by
  rfl

set_option smartUnfolding true in
/-- The per-compile construction check accepts the actual export. -/
theorem accepted : checkExport GuessProofData.snapshot participant = .ok () := by decide +kernel

set_option smartUnfolding true in
/-- Where the export returns the selected acceptance output. -/
def acceptancePosition : Nat :=
  (exportAcceptance GuessProofData.snapshot participant).get (by decide +kernel)

theorem acceptance_admitted :
    exportAcceptance GuessProofData.snapshot participant = some acceptancePosition := by
  rfl

/-- The acceptance output selected by the policy, read from returned values. -/
def acceptance (values : List (Value F G)) : Option Bool :=
  match values[acceptancePosition]? with
  | some (.data (.boolean decision)) => some decision
  | _ => none

/-- Data inputs of the constructed validator: the public offset. -/
def inputs (offset : F) : List (Payload F G) := [.field fieldDomain offset]

/-- The validator's original inputs, by original position. -/
def originalValue (offset : F) (challengeService : Nat) (index : Nat) : Option (Payload F G) :=
  ((inputPayloads (verifierInputs (G := G) offset challengeService))[index]?).join

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The host binds exactly `inputs`: the validator's original inputs at the
checked policy's public positions, in order. -/
theorem public_values (offset : F) (challengeService : Nat) :
    publicValues participant.policy (originalValue (G := G) offset challengeService) =
      some (inputs offset) := by
  rfl

/-- Helper calls of the constructed program denote the original's checked
helpers. The guessing validator calls none. -/
abbrev table : Structured.Meanings F G := helperTable program F G

set_option smartUnfolding true in
/-- The participant projection rule accepts the actual export. -/
theorem projected : project program context participant = .ok () := by decide +kernel

set_option smartUnfolding true in
/-- The composed per-compile check accepts the actual export against the
admitted original. -/
theorem compiled : checkCompiled imported participant = .ok () := by
  decide +kernel

theorem validator_eq : context.validator = 1 := by rw [context_eq]

set_option smartUnfolding true in
theorem acceptancePosition_eq : acceptancePosition = 0 := by decide +kernel

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

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The constructed program's data inputs hold the validator's original inputs:
the offset at its exported position, and the handle as the replaced service. -/
theorem inputs_related (offset : F) (handle : Nat) (initial : History F G) :
    HoldsValues handle ((inputs offset).map .data ++ [.transcript initial])
      (inputSlots context participant.policy program.payload.entry.inputs)
      (verifierInputs (G := G) offset handle) := by
  have slotsEq : inputSlots context participant.policy program.payload.entry.inputs =
      [.held 0, .absent, .service] := by
    rw [context_eq]
    rfl
  rw [slotsEq]
  refine ⟨⟨offset, rfl, ?_⟩, rfl, rfl, trivial⟩
  simp [inputs, Value.decode]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The decision among the validator's outputs is its acceptance output. -/
theorem decision_outputs
    (outputs : Values (Component (assignment F G)) program.payload.entry.outputs) :
    decision (validatorOutputs 1 program.payload.entry.outputScopes outputs) =
      outputs.get .here := by
  have scopesEq : program.payload.entry.outputScopes = [[1]] := rfl
  rw [scopesEq]
  rcases outputs with _ | ⟨value, _ | _⟩
  simp only [decision, acceptancePosition_eq]
  cases value <;> rfl

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
suffixes, for every offset, initial transcript, proof and service handle. -/
theorem compiled_transform {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (offset : F) (handle : Nat) (initial : History F G)
    (proof : Proof F G) :
    (fun result => (mapOutcome acceptance result.1, result.2)) <$>
        ideal context challenge table participant.returned participant.instructions
          ((inputs offset).map .data ++ [.transcript initial]) proof =
      transform context challenge (verifier offset handle) initial proof := by
  obtain ⟨context', found, composed⟩ :=
    Zkc.Construction.compiled_transform (F := F) (G := G) imported participant compiled
  rw [context_admitted] at found
  cases found
  dsimp only [imported] at composed
  rw [composed challenge acceptance decision acceptance_decision handle ((inputs offset).map .data)
    initial proof (verifierInputs offset handle) (inputs_related offset handle initial) rfl,
    original_verifier]

end ZkcExamples.Construction.GuessProof
