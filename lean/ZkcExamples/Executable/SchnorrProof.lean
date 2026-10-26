module

public import ZkcExamples.Executable.SchnorrProofFacts
public import ZkcExamples.Construction.SchnorrProof
public import Zkc.Executable.ByteParticipantTransport
public import Zkc.Executable.StaticBudgetRejection
public import Zkc.Executable.HelperSchemas

@[expose] public section
/-! The actual Schnorr native-byte consumer, composed through canonical Domain
execution, the checked return schema, and the actual source Fiat–Shamir
connection. Arbitrary bytes, decoders, public inputs and scalar oracle replies
are retained. The caller's initial history is an opaque scalar prefix. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
namespace ZkcExamples.Executable.SchnorrProof
open Zkc.Construction Zkc.Executable Zkc.Source
open ZkcExamples.Construction
open Zkc.Construction.Uniform
open Zkc.Executable.DomainVM Zkc.Executable.ByteParticipantTransport

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- No helper needs preparation at the retained endpoint ABI. -/
theorem prepared : ∀ name ∈ Instruction.helpers SchnorrProof.participant.instructions,
    Prepared installed validator (SchnorrProof.table (F := F) (G := G)) name := by
  simp [helpers]

/-- No helper call needs its result sorts. -/
theorem helpersSorted : ∀ call ∈ Instruction.callList SchnorrProof.participant.instructions,
    HelperSorted (SchnorrProof.table (F := F) (G := G)) call.1 call.2 := by
  simp [calls]

abbrev data (base key : G) : List (Value F G) := (SchnorrProof.inputs (F := F) base key).map .data

def nominalData (base key : G) : Environment F G :=
  [.data (.group "bls12-381.g1" base), .data (.group "bls12-381.g1" key)]

theorem embedded (base key : G) : DomainAdapter.embedValues (data (F := F) base key) = some (nominalData (F := F) base key) := rfl

theorem native_prepared : ∀ name ∈ Instruction.helperList SchnorrProof.participant.instructions,
    Prepared installed validator (Domain.helperTable (Structured.ringModel F G) SchnorrProof.program) name := by
  simp [Instruction.helperList_eq, helpers]

def nativeFinal : NativeScope :=
  (checkNativeCode SchnorrProof.program SchnorrProof.context lowered.code (nativeEntryScope validator)).get
    (by decide +kernel)

theorem native_checked :
    checkNativeLowering SchnorrProof.program SchnorrProof.context installed SchnorrProof.participant validator =
      .ok (lowered, nativeFinal) := by kernel_rfl

theorem schedule_instructions : Code.instructions lowered.code = SchnorrProof.participant.instructions := by
  rw [← Code.instructionList_eq]
  decide +kernel

theorem schedule_returned : lowered.returned = SchnorrProof.participant.returned := by decide +kernel

theorem return_schema : ReturnSchema SchnorrProof.participant := by decide +kernel

/-- Connect the actual reading, including all return references, to the actual
source view using the participant's checked input and output schemas. -/
theorem schedule_source (base key : G) (handle : Nat) :
    DomainVM.observation SchnorrProof.program SchnorrProof.context
      (Code.instructions lowered.code) lowered.returned
      (nominalData (F := F) base key ++ [Domain.Value.transcript SchnorrProof.context.suite []]) =
    (SourceProcess.sourceView SchnorrProof.context (SchnorrDomainConnection.sourceDecision base key handle) []).bind
      (fun result => .done (SourceProcess.returnValues SchnorrProof.context.suite result)) := by
  rw [schedule_instructions, schedule_returned,
    ← participant_observation (F := F) (G := G) SchnorrProof.program SchnorrProof.context SchnorrProof.participant
      (nominalData (F := F) base key ++ [Domain.Value.transcript SchnorrProof.context.suite []]) rfl return_schema]
  exact SchnorrDomainConnection.participant_values base key handle

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- The two installed maps agree on actual source-generated static histories.
No claim about arbitrary coordinate-bearing origins follows from finiteness. -/
theorem schedule_keys {R : Type} (challenge : History F G → m F) (base key : G)
    (initial : History F G) (proof : Proof F G)
    (next : Environment F G → Proof F G → m (PIR.Outcome R × Proof F G)) :
    DomainAdapter.runK Origin.withoutCoordinates initial challenge
      (DomainVM.observation SchnorrProof.program SchnorrProof.context
        (Code.instructions lowered.code) lowered.returned
        (nominalData (F := F) base key ++ [Domain.Value.transcript SchnorrProof.context.suite []])) proof next =
    DomainAdapter.runK SourceProcess.legacyOrigin initial challenge
      (DomainVM.observation SchnorrProof.program SchnorrProof.context
        (Code.instructions lowered.code) lowered.returned
        (nominalData (F := F) base key ++ [Domain.Value.transcript SchnorrProof.context.suite []])) proof next := by
  rw [schedule_source base key 0, DomainAdapter.runK_bind, DomainAdapter.runK_bind]
  apply StaticSourceTransport.sourceView_keys
  · intro site sender receiver
    simp [Context.message, SourceProcess.legacyOrigin]
  · intro site field
    simp [Context.query, SourceProcess.legacyOrigin]
  · rfl

theorem acceptance_selection : SchnorrProof.acceptance (F := F) (G := G) = scalarSelected := by
  funext values
  rw [SchnorrProof.acceptance, SchnorrProof.acceptancePosition_eq]
  cases values with
  | nil => rfl
  | cons head tail => cases head with
    | data payload => cases payload <;> rfl
    | index | vector | transcript | indices | unsupported => rfl

/-- At the measured threshold the complete native observation agrees with the
actual Domain reading, for all malformed and well-formed byte strings. -/
theorem executable_observation
    (challenge : History F G → m F) (decode : PhysicalType → List UInt8 → Option (Payload F G))
    {budget : Nat} (sufficient : 25 ≤ budget) (base key : G) (initial : History F G) (bytes : List UInt8) :
    Run.observe <$> execute installed validator SchnorrProof.context challenge decode budget (data (F := F) base key) initial bytes =
      nativeObservation SchnorrProof.context.suite Origin.withoutCoordinates initial <$>
        DomainAdapter.run Origin.withoutCoordinates initial challenge
          (DomainVM.observation SchnorrProof.program SchnorrProof.context
            (Code.instructions lowered.code) lowered.returned
            (nominalData (F := F) base key ++ [Domain.Value.transcript SchnorrProof.context.suite []]))
          (decodeProof decode receives bytes) := by
  simpa only [plan_types] using checked_execute_static SchnorrProof.program SchnorrProof.context initial challenge
    installed SchnorrProof.participant validator decode budget native_prepared lowered nativeFinal native_checked
    (data (F := F) base key) bytes (admitted base key) (nominalData (F := F) base key) (embedded base key) 25 total sufficient

/-- The original byte theorem's all-byte/all-decoder/lawful-monad scope, now
through the actual Domain participant and the existing SOURCE transform. -/
theorem executable_transform
    (challenge : History F G → m F) (decode : PhysicalType → List UInt8 → Option (Payload F G))
    {budget : Nat} (sufficient : 25 ≤ budget) (base key : G) (handle : Nat) (initial : History F G)
    (bytes : List UInt8) :
    (fun result => (mapOutcome SchnorrProof.acceptance result.observe.1, result.observe.2)) <$>
        execute installed validator SchnorrProof.context challenge decode budget (data (F := F) base key) initial bytes =
      (fun result => Zkc.Executable.observation result.1 result.2.isEmpty) <$>
        transform SchnorrProof.context challenge (SchnorrProof.verifier base key handle) initial
          (decodeProof decode receives bytes) := by
  have native := executable_observation challenge decode sufficient base key initial bytes
  have selected := congrArg (fun action =>
    (fun result => (mapOutcome SchnorrProof.acceptance result.1, result.2)) <$> action) native
  simp only [Functor.map_map] at selected
  rw [selected]
  simp only [nativeObservation, mapOutcome_observation]
  rw [acceptance_selection, schedule_source base key handle,
    source_observation SchnorrProof.context Origin.withoutCoordinates initial challenge]
  have keys := StaticSourceTransport.sourceView_keys SchnorrProof.context Origin.withoutCoordinates
    SourceProcess.legacyOrigin (fun site sender receiver => by simp [Context.message, SourceProcess.legacyOrigin])
    (fun site field => by simp [Context.query, SourceProcess.legacyOrigin]) initial challenge
    (SchnorrDomainConnection.sourceDecision base key handle) [] rfl (decodeProof decode receives bytes)
    (fun result unread => pure (.returned (some result.1), unread))
  rw [keys]
  have source := SourceProcess.sourceView_transform_map SchnorrProof.context challenge
    (SchnorrDomainConnection.sourceDecision base key handle) some initial (decodeProof decode receives bytes)
  rw [← SchnorrDomainConnection.source_decision] at source
  have identity : SchnorrDomainConnection.sourceVerifier (F := F) base key handle = SchnorrProof.verifier base key handle := rfl
  rw [identity] at source
  rw [source]

/-- Exact endpoint target: the installed ScalarVerifier at the actual program,
context, participant, acceptance position, published tuple and decoding plan. -/
theorem domain_prunes
    (challenge : History F G → m F) (codec : PhysicalType → List UInt8 → Option (Payload F G))
    (budget : Nat) (binding : List UInt8) (base key : G) (initial : History F G) (bytes : List UInt8) :
    Prunes (fun decision => decision = false)
      (Zkc.Executable.validate installed validator SchnorrProof.context challenge codec budget binding
        SchnorrProof.acceptancePosition (data (F := F) base key) initial bytes)
      (scalarVerdict <$> ScalarVerifier.verify SchnorrProof.program SchnorrProof.context SchnorrProof.participant
        SchnorrProof.acceptancePosition challenge (data (F := F) base key) initial
        (decodeProof codec (Plan.types (data (F := F) base key) lowered.plan) (bytes.drop 40))) := by
  have pruning := checked_validate_prunes SchnorrProof.program SchnorrProof.context initial challenge installed
    SchnorrProof.participant validator codec budget native_prepared lowered nativeFinal native_checked binding
    SchnorrProof.acceptancePosition (data (F := F) base key) bytes (admitted base key) (nominalData (F := F) base key) (embedded base key)
  rw [run_nominalAcceptance] at pruning
  rw [schedule_keys] at pruning
  rw [ScalarVerifier.verify_eq_runK SchnorrProof.program SchnorrProof.context SchnorrProof.participant
    SchnorrProof.acceptancePosition challenge (data (F := F) base key)
    (nominalData (F := F) base key ++ [Domain.Value.transcript SchnorrProof.context.suite []]) rfl initial]
  have finite : ScalarVerifier.origin SchnorrProof.participant = SourceProcess.legacyOrigin := by kernel_rfl
  rw [finite]
  have participant := runK_participant (F := F) (G := G) SchnorrProof.program SchnorrProof.context SchnorrProof.participant
    (nominalData (F := F) base key ++ [Domain.Value.transcript SchnorrProof.context.suite []]) rfl return_schema
    SourceProcess.legacyOrigin initial challenge
    (decodeProof codec (Plan.types (data (F := F) base key) lowered.plan) (bytes.drop 40))
    (fun values unread => pure (.returned (selected SchnorrProof.acceptancePosition values), unread))
  rw [← schedule_instructions, ← schedule_returned] at participant
  convert pruning using 1
  rw [← participant]
  rfl

/-- Exact header and sufficient budget: canonical participant acceptance of the
actual decoded bytes. This replaces the old independently interpreted RHS. -/
theorem executable_validate
    (challenge : History F G → m F) (decode : PhysicalType → List UInt8 → Option (Payload F G))
    {budget : Nat} (sufficient : 25 ≤ budget) (binding : List UInt8) (base key : G)
    (initial : History F G) (bytes : List UInt8) (header : bytes.take 40 = magic ++ binding) :
    Zkc.Executable.validate installed validator SchnorrProof.context challenge decode budget binding
      SchnorrProof.acceptancePosition (data (F := F) base key) initial bytes =
    scalarVerdict <$> ScalarVerifier.verify SchnorrProof.program SchnorrProof.context SchnorrProof.participant
      SchnorrProof.acceptancePosition challenge (data (F := F) base key) initial (decodeProof decode receives (bytes.drop 40)) := by
  have transformed := executable_transform challenge decode sufficient base key 0 initial (bytes.drop 40)
  have selectedNative := congrArg (fun action => observedVerdict <$> action) transformed
  simp only [Functor.map_map] at selectedNative
  have projection : ∀ result : Run F G,
      result.accepts SchnorrProof.acceptancePosition =
        observedVerdict (mapOutcome SchnorrProof.acceptance result.observe.1, result.observe.2) := by
    intro result
    rw [native_acceptance, byteAcceptance_selection]
    rfl
  unfold Zkc.Executable.validate
  simp only [header, ite_true]
  simp_rw [projection]
  rw [selectedNative, ← SchnorrProof.compiled_transform challenge base key 0]
  simp only [SchnorrProof.compiledVerifier, observedVerdict_observation]

/-- The original effect-preserving rejection statement: oracle actions before a
later resource failure remain observable in every lawful monad. -/
theorem executable_rejects
    (challenge : History F G → m F) (decode : PhysicalType → List UInt8 → Option (Payload F G))
    {budget : Nat} (binding : List UInt8) (base key : G) (initial : History F G) (bytes : List UInt8)
    (short : budget < 25 ∨ bytes.take 40 ≠ magic ++ binding) :
    Zkc.Executable.validate installed validator SchnorrProof.context challenge decode budget binding
      SchnorrProof.acceptancePosition (data base key) initial bytes =
      (fun _ => false) <$> Zkc.Executable.validate installed validator SchnorrProof.context challenge decode budget binding
        SchnorrProof.acceptancePosition (data base key) initial bytes := by
  exact checked_validate_rejects_static SchnorrProof.program SchnorrProof.context initial challenge budget
    installed SchnorrProof.participant validator decode native_prepared lowered nativeFinal native_checked 25 total
    binding SchnorrProof.acceptancePosition (data base key) bytes (admitted base key)
    (nominalData base key) (embedded base key) short

end ZkcExamples.Executable.SchnorrProof
