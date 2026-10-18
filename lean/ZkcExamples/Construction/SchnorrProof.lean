module

public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.Construction.SchnorrProofData
public import ZkcExamples.Construction.SchnorrProofBodies
public import ZkcExamples.Construction.SchnorrProofParticipant
public import Zkc.Construction.Soundness
public import Zkc.Construction.Structured
public import Zkc.Source.Structured.OpenLaws
public import Zkc.Source.Structured.CommonAdapter
public import ZkcExamples.NativePrograms.Schnorr

@[expose] public section

/-! The compiled non-interactive Schnorr verifier of `example::Proof`.

`SchnorrProofData` is the original-stage export of the Proof Entry, whose
protocol additionally retains its proof statement. `SchnorrProofParticipant` is
the compiler's constructed validator for that Entry and its native policy. The
construction rule accepts the pair, and the constructed program's interactive
reading is exactly the original validator process. With `check_sound`, the
compiled verifier's ideal meaning is the Fiat–Shamir transform of the original
verifier for every challenge function.
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
theorem accepted : checkExport SchnorrProofData.snapshot participant = true := by decide +kernel

theorem checked : check context participant = true := by
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

/-- The constructed program's interactive reading is the original validator,
with every reply, stop and acceptance decision. -/
theorem spec_equation (base key : G) (handle : Nat) (initial : History F G) :
    (spec context handle participant.returned participant.instructions
        ((inputs base key).map .data ++ [.transcript initial]) 0).bind
      (fun values => .done (acceptance values)) =
      Zkc.Protocols.Schnorr.Common.experiment wiring base key handle := by
  rfl

/-- The compiled verifier, under the ideal transcript model with any challenge
function in any lawful monad, is the Fiat–Shamir transform of the original
Proof Entry's validator: equal acceptance outcomes, stops and unread proof
suffixes, for every input, initial transcript, proof and service handle. -/
theorem compiled_transform {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (base key : G) (handle : Nat) (initial : History F G)
    (proof : Proof F G) :
    (fun result => (mapOutcome acceptance result.1, result.2)) <$>
        ideal challenge participant.returned participant.instructions
          ((inputs base key).map .data ++ [.transcript initial]) proof =
      transform context challenge (verifier base key handle) initial proof := by
  rw [verifier_correspondence, ← spec_equation base key handle initial, transform_bind_done,
    check_sound context participant checked challenge handle (inputs base key) initial proof
      (inputs_arity base key)]

end ZkcExamples.Construction.SchnorrProof
