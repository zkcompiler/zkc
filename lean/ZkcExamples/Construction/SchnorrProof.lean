module

public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.Construction.SchnorrProofData
public import ZkcExamples.Construction.SchnorrProofBodies
public import ZkcExamples.Construction.SchnorrProofParticipant
public import Zkc.Construction.Compiled
public import Zkc.Source.Structured.OpenLaws
public import Zkc.Source.Structured.CommonAdapter
public import ZkcExamples.NativePrograms.Schnorr

@[expose] public section

/-! The compiled non-interactive Schnorr verifier of `example::Proof`.

`SchnorrProofData` is the original-stage export of the Proof Entry, whose
protocol additionally retains its proof statement. `SchnorrProofParticipant` is
the compiler's constructed validator for that Entry and its native policy. The
transcript-construction rule and the participant projection rule both accept
the pair (`compiled`), so by their composed soundness the compiled verifier's
ideal meaning is the Fiat–Shamir transform of the original verifier for every
challenge function (`compiled_transform`). No equation specific to this Entry is
assumed: `spec_equation` is derived from the projection rule.
-/

namespace ZkcExamples.Construction.SchnorrProof
open Zkc.Source Zkc.Source.Structured Zkc.Construction

set_option smartUnfolding false

/-! ## The original Proof Entry -/

structured_views SchnorrProofData.snapshot
  helpers [formula := SchnorrProofBodies.formula]
  protocols [proof := SchnorrProofBodies.proof]

theorem admitted : Structured.check SchnorrProofData.snapshot = .ok program := kernel_admission

abbrev wiring := ZkcExamples.NativePrograms.Schnorr.wiring

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def verifierInputs (base key : G) (challengeService : Nat) :
    Values (Component (assignment F G)) program.payload.entry.inputs :=
  .cons (some base) (.cons (some key) (.cons none (.cons none (.cons (some challengeService) .nil))))

/-- The admitted root's validator process. Unowned secret and service inputs
are absent. -/
def process (base key : G) (challengeService : Nat) :
    PIR.Proc (participantInterface F G) (Option Bool) :=
  (program.participant F G 1 (verifierInputs base key challengeService)).bind fun outputs =>
    .done (outputs.get .here)

theorem process_equation (base key : G) (challengeService : Nat) :
    process (F := F) base key challengeService =
      (Zkc.Protocols.Schnorr.Common.experiment wiring base key challengeService).interpret
        CommonAdapter.embed := by
  rfl

def verifier : Zkc.Protocols.Schnorr.Common.Verifier F G := fun base key service =>
  (process base key service).interpret CommonAdapter.project

theorem verifier_correspondence (base key : G) (service : Nat) :
    verifier (F := F) base key service =
      Zkc.Protocols.Schnorr.Common.experiment wiring base key service := by
  rw [verifier, process_equation, CommonAdapter.project_embed]

/-! ## The constructed validator -/

abbrev participant := SchnorrProofParticipant.participant

/-- The occurrence context the check derives from the original roster and the
exported policy. -/
def context : Context := (exportContext SchnorrProofData.snapshot participant).get (by decide +kernel)

theorem context_admitted : exportContext SchnorrProofData.snapshot participant = some context := by
  rfl

/-- The derived context: entry, roster, producer and validator positions, the
replaced service input `4` and its contract, the suite and the selected
query/delivery sites. -/
theorem context_eq : context =
    ⟨SchnorrProofData.snapshot.entry, ["role00000000", "role00000001"], wiring.prover, 1, 4,
      "random.bls12-381.fr/0", participant.policy.suite,
      [(wiring.challengeSite, wiring.deliverySite)]⟩ := by
  rfl

set_option smartUnfolding true in
/-- The per-compile construction check accepts the actual export. -/
theorem accepted : checkExport SchnorrProofData.snapshot participant = .ok () := by decide +kernel

theorem checked : check context participant = .ok () := by
  obtain ⟨found, admittedContext, checks⟩ := checkExport_sound accepted
  rw [context_admitted] at admittedContext
  cases admittedContext
  exact checks

set_option smartUnfolding true in
/-- Where the export returns the selected acceptance output. -/
def acceptancePosition : Nat :=
  (exportAcceptance SchnorrProofData.snapshot participant).get (by decide +kernel)

theorem acceptance_admitted :
    exportAcceptance SchnorrProofData.snapshot participant = some acceptancePosition := by
  rfl

/-- The acceptance output selected by the policy, read from returned values. -/
def acceptance (values : List (Value F G)) : Option Bool :=
  match values[acceptancePosition]? with
  | some (.data (.boolean decision)) => some decision
  | _ => none

/-- Data inputs of the constructed validator, in original order. -/
def inputs (base key : G) : List (Payload F G) :=
  [.group "bls12-381.g1" base, .group "bls12-381.g1" key]

/-- The validator's original inputs, by original position. -/
def originalValue (base key : G) (challengeService : Nat) (index : Nat) : Option (Payload F G) :=
  ((inputPayloads (verifierInputs (F := F) base key challengeService))[index]?).join

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The host binds exactly `inputs`: the validator's original inputs at the
checked policy's public positions, in order. -/
theorem public_values (base key : G) (challengeService : Nat) :
    publicValues participant.policy (originalValue (F := F) base key challengeService) =
      some (inputs base key) := by
  rfl

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem inputs_arity (base key : G) :
    (inputs (F := F) base key).length + 1 = participant.inputs.length := rfl

/-- Helper calls of the constructed program denote the original's checked
helpers. The Schnorr validator calls none. -/
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
base and statement at their exported positions, and the handle as the replaced
service. -/
theorem inputs_related (base key : G) (handle : Nat) (initial : History F G) :
    HoldsValues handle ((inputs base key).map .data ++ [.transcript initial])
      (inputSlots context participant.policy program.payload.entry.inputs)
      (verifierInputs (F := F) base key handle) := by
  have slotsEq : inputSlots context participant.policy program.payload.entry.inputs =
      [.held 0, .held 1, .absent, .absent, .service] := by
    rw [context_eq]
    rfl
  rw [slotsEq]
  refine ⟨⟨base, rfl, ?_⟩, ⟨key, rfl, ?_⟩, rfl, rfl, rfl, trivial⟩ <;>
    simp [inputs, Value.decode]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The decision among the validator's outputs is its acceptance output. -/
theorem decision_outputs (outputs : Values (Component (assignment F G)) program.payload.entry.outputs) :
    decision (validatorOutputs 1 program.payload.entry.outputScopes outputs) = outputs.get .here := by
  have scopesEq : program.payload.entry.outputScopes = [[1]] := rfl
  rw [scopesEq]
  rcases outputs with _ | ⟨value, _ | _⟩
  simp only [decision, acceptancePosition_eq]
  cases value <;> rfl

/-- The original validator, read through its outputs, is the verifier. -/
theorem original_verifier (base key : G) (handle : Nat) :
    ((program.participant F G context.validator (verifierInputs base key handle)).bind fun outputs =>
      .done (decision (validatorOutputs context.validator program.payload.entry.outputScopes
        outputs))).interpret CommonAdapter.project = verifier base key handle := by
  unfold verifier process
  rw [validator_eq]
  simp only [decision_outputs]

/-- The constructed program's interactive reading is the original validator,
with every reply, stop and acceptance decision. Derived from the projection rule;
no computation specific to this Entry is involved. -/
theorem spec_equation (base key : G) (handle : Nat) (initial : History F G) :
    (spec context handle table participant.returned participant.instructions
        ((inputs base key).map .data ++ [.transcript initial])).bind
      (fun values => .done (acceptance values)) =
      Zkc.Protocols.Schnorr.Common.experiment wiring base key handle := by
  rw [spec_bind_congr context handle table participant.returned participant.instructions _ acceptance
    (fun values => decision (values.dropLast.map some)) acceptance_decision]
  have projected' := project_sound program context participant projected handle
    ((inputs base key).map .data) initial (verifierInputs base key handle)
    (inputs_related base key handle initial) rfl
  calc (spec context handle table participant.returned participant.instructions
          ((inputs base key).map .data ++ [.transcript initial])).bind
          (fun values => .done (decision (values.dropLast.map some)))
      = ((spec context handle table participant.returned participant.instructions
          ((inputs base key).map .data ++ [.transcript initial])).bind
          (fun values => .done (values.dropLast.map some))).bind
          (fun options => .done (decision options)) := by
        rw [PIR.Proc.bind_assoc]
        rfl
    _ = (((program.participant F G context.validator (verifierInputs base key handle)).bind
          fun outputs => .done (validatorOutputs context.validator program.payload.entry.outputScopes
            outputs)).interpret CommonAdapter.project).bind
          (fun options => .done (decision options)) := by
        rw [projected']
    _ = ((program.participant F G context.validator (verifierInputs base key handle)).bind
          fun outputs => .done (decision (validatorOutputs context.validator
            program.payload.entry.outputScopes outputs))).interpret CommonAdapter.project := by
        rw [PIR.Proc.interpret_bind, PIR.Proc.interpret_bind, PIR.Proc.bind_assoc]
        rfl
    _ = Zkc.Protocols.Schnorr.Common.experiment wiring base key handle := by
        rw [original_verifier, verifier_correspondence]

/-- The compiled verifier, under the ideal transcript model with any challenge
function in any lawful monad, is the Fiat–Shamir transform of the original
Proof Entry's validator: equal acceptance outcomes, stops and unread proof
suffixes, for every input, initial transcript, proof and service handle. -/
theorem compiled_transform {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (base key : G) (handle : Nat) (initial : History F G)
    (proof : Proof F G) :
    (fun result => (mapOutcome acceptance result.1, result.2)) <$>
        ideal context challenge table participant.returned participant.instructions
          ((inputs base key).map .data ++ [.transcript initial]) proof =
      transform context challenge (verifier base key handle) initial proof := by
  obtain ⟨context', found, composed⟩ :=
    Zkc.Construction.compiled_transform (F := F) (G := G) imported participant compiled
  rw [context_admitted] at found
  cases found
  dsimp only [imported] at composed
  rw [composed challenge acceptance decision acceptance_decision handle ((inputs base key).map .data)
    initial proof (verifierInputs base key handle) (inputs_related base key handle initial) rfl,
    original_verifier]

end ZkcExamples.Construction.SchnorrProof
