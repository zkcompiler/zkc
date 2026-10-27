module

public import Zkc.Executable.DomainByteLaws
public import Zkc.Executable.DomainNativeData

@[expose] public section

/-! Property-specific byte observations and list-local codec laws. Refusals do
not expose a fictitious raw unread suffix; successful returns retain complete
unread status and all scalar query actions in their original monad. -/
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source Zkc.Construction.Uniform
variable {F G : Type}

/-- Codec contracts only at the actually paired physical types and messages.
A field-only codec need not decode Boolean or group messages. -/
def FrameCodecRows (decode : PhysicalType → List UInt8 → Option (Payload F G))
    (encode : PhysicalType → Payload F G → List UInt8) :
    List PhysicalType → Proof F G → Prop :=
  List.Forall₂ fun type payload =>
    decode type (encode type payload) = some payload ∧ (encode type payload).length ≤ proofLimit

theorem decodeProof_frames_local
    (decode : PhysicalType → List UInt8 → Option (Payload F G))
    (encode : PhysicalType → Payload F G → List UInt8) :
    ∀ (types : List PhysicalType) (payloads : Proof F G), FrameCodecRows decode encode types payloads →
      decodeProof decode types (frames encode types payloads) = payloads
  | [], [], _ => rfl
  | [], _ :: _, rows => by cases rows
  | _ :: _, [], rows => by cases rows
  | type :: types, payload :: payloads, rows => by
      cases rows with
      | cons head tail =>
          simp only [frames, decodeProof, readFrame_frame _ _ head.2, head.1,
            decodeProof_frames_local decode encode types payloads tail]

variable {m : Type → Type} [Monad m]

/-- Honest message representation is local to its selected plan. The process
and all later failures/actions are arbitrary. -/
theorem runK_frames_local {A R : Type}
    (key : Origin → Origin) (initial : History F G) (challenge : History F G → m F)
    (decode : PhysicalType → List UInt8 → Option (Payload F G))
    (encode : PhysicalType → Payload F G → List UInt8)
    (types : List PhysicalType) (payloads : Proof F G)
    (rows : FrameCodecRows decode encode types payloads)
    (process : PIR.Process (Domain.effects (Structured.uniformCarriers F G)) A)
    (next : A → Proof F G → m (PIR.Outcome R × Proof F G)) :
    DomainAdapter.runK key initial challenge process
      (decodeProof decode types (frames encode types payloads)) next =
        DomainAdapter.runK key initial challenge process payloads next := by
  rw [decodeProof_frames_local decode encode types payloads rows]

/-- Read back the complete returned scalar tuple. Only stopped unread status
is forgotten, exactly as at the retained native observation boundary. -/
def nativeObservation (suite : String) (key : Origin → Origin) (initial : History F G)
    (result : PIR.Outcome (Environment F G) × Proof F G) :
    PIR.Outcome (List (Value F G)) × Bool :=
  Executable.observation (DomainAdapter.readbackOutcome suite key initial result.1) result.2.isEmpty

@[simp] theorem nativeObservation_stopped (suite : String) (key : Origin → Origin)
    (initial : History F G) (reason : PIR.Stop) (unread : Proof F G) :
    nativeObservation suite key initial (.stopped reason, unread) = (.stopped reason, true) := rfl

/-- Scalar acceptance retains the selected returned Boolean and unread status.
A query in the surrounding monad cannot be discarded by this projection. -/
def byteAcceptance (position : Nat) (observed : PIR.Outcome (List (Value F G)) × Bool) : Bool :=
  match observed.1 with
  | .returned values => observed.2 && selectedTrue values position
  | .stopped _ => false

theorem native_acceptance (run : Run F G) (position : Nat) :
    run.accepts position = byteAcceptance position run.observe := by
  cases result : run.result <;> simp [Run.accepts, Run.observe, byteAcceptance, result,
    Executable.observation, Result.outcome]

/-- The actual 40-byte host header check composes with any body observation
proof. This statement makes no assumptions about the codec or byte string. -/
theorem validate_of_execute_observation [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
    [LawfulMonad m] (vocabulary : Vocabulary) (validator : Validator) (context : Context)
    (challenge : History F G → m F) (decode : PhysicalType → List UInt8 → Option (Payload F G))
    (budget : Nat) (binding : List UInt8) (position : Nat) (data : List (Value F G))
    (initial : History F G) (bytes : List UInt8)
    (body : m (PIR.Outcome (List (Value F G)) × Bool))
    (correspondence : Run.observe <$>
      execute vocabulary validator context challenge decode budget data initial (bytes.drop 40) = body) :
    Executable.validate vocabulary validator context challenge decode budget binding position data initial bytes =
      if bytes.take 40 = magic ++ binding then byteAcceptance position <$> body else pure false := by
  unfold Executable.validate
  split
  · rw [← correspondence, Functor.map_map]
    congr 1
    funext result
    exact native_acceptance result position
  · rfl

end Zkc.Executable.DomainVM
