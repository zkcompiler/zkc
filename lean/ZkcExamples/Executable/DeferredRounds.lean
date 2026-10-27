module

public import ZkcExamples.Executable.DeferredRoundsFacts
public import ZkcExamples.Executable.DeferredRoundsDomainNormalization
public import Zkc.Executable.ByteParticipantTransport
public import Zkc.Executable.StaticBudgetRejection

@[expose] public section
/-! Native bytes for the actual rescheduled DeferredRounds artifact. Canonical
normalization compares the real Code reading with the retained participant.
No helper is called, so the actual Structured.Program is arbitrary. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
namespace ZkcExamples.Executable.DeferredRounds
open Zkc.Construction Zkc.Executable Zkc.Source
open ZkcExamples.Construction Zkc.Construction.Uniform
open Zkc.Executable.DomainVM Zkc.Executable.ByteParticipantTransport

/-- The actual reading differs from the retained participant's schedule. -/
theorem rescheduled : Code.instructionList lowered.code ≠ DeferredRounds.participant.instructions := by
  decide +kernel

/-- Independent reader identity, without any semantic premise. -/
theorem lowered_reading : lowered = checkedReading := by
  have read := checkLowering_read installed DeferredRounds.participant validator lowered accepted
  have noHelpers : Instruction.helperList DeferredRounds.participant.instructions = [] := by
    rw [Instruction.helperList_eq, helpers]
  rw [noHelpers, reading_checked] at read
  exact (Except.ok.inj read).symm

/-- The computed final nominal scope has no helper-dependent part. -/
def nativeFinal (program : Structured.Program) : NativeScope :=
  (checkNativeCode program DeferredRounds.context lowered.code (nativeEntryScope validator)).get
    (by kernel_rfl)

theorem native_checked (program : Structured.Program) :
    checkNativeLowering program DeferredRounds.context installed DeferredRounds.participant validator =
      .ok (lowered, nativeFinal program) := by kernel_rfl

theorem return_schema : ReturnSchema DeferredRounds.participant := by decide +kernel

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- No helper needs preparation for any actual program. -/
theorem prepared (program : Structured.Program) :
    ∀ name ∈ Instruction.helperList DeferredRounds.participant.instructions,
      Prepared installed validator (Domain.helperTable (Structured.ringModel F G) program) name := by
  simp [Instruction.helperList_eq, helpers]

def nominalData (x : F) : Environment F G := [.data (.field "bls12-381.fr" x)]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem embedded (x : F) : DomainAdapter.embedValues (DeferredRounds.inputs (G := G) x) = some (nominalData x) := rfl

/-- Canonical equality is derived from the accepted normalization check on the
actual read schedule, for arbitrary input values and all action replies. -/
theorem schedule_normalized (program : Structured.Program) (x : F) :
    DomainVM.observation program DeferredRounds.context (Code.instructions lowered.code) lowered.returned
      (nominalData (G := G) x ++ [Domain.Value.transcript DeferredRounds.context.suite []]) =
    DomainVM.observation program DeferredRounds.context DeferredRounds.participant.instructions
      DeferredRounds.participant.returned
      (nominalData (G := G) x ++ [Domain.Value.transcript DeferredRounds.context.suite []]) := by
  rw [lowered_reading]
  exact normalized_schedule program x []


/-- The actual retained participant returns a scalar Boolean and a readable
scalar transcript for every typed receive/query reply. -/
theorem readable_returns (program : Structured.Program) (x : F) (key : Origin → Origin)
    (initial : History F G) :
    PIR.Yields (fun values => (DomainAdapter.readbackValues DeferredRounds.context.suite key initial values).isSome = true)
      (DomainVM.observation program DeferredRounds.context DeferredRounds.participant.instructions
        DeferredRounds.participant.returned
        (nominalData x ++ [Domain.Value.transcript DeferredRounds.context.suite []])) := by
  have multiply (field : String) (left right : F)
      (one two : (Structured.Ty.field field).isService = false) :
      Domain.calculate (Structured.ringModel F G) (.fieldMultiply field)
        [.data ⟨.field field, one, left⟩, .data ⟨.field field, two, right⟩] =
        .returned [.data (.field field (left * right))] := Domain.Calculations.fieldMultiply field left right
  have add (field : String) (left right : F)
      (one two : (Structured.Ty.field field).isService = false) :
      Domain.calculate (Structured.ringModel F G) (.fieldAdd field)
        [.data ⟨.field field, one, left⟩, .data ⟨.field field, two, right⟩] =
        .returned [.data (.field field (left + right))] := Domain.Calculations.fieldAdd field left right
  have equal (field : String) (left right : F)
      (one two : (Structured.Ty.field field).isService = false) :
      Domain.calculate (Structured.ringModel F G) (.fieldEqual field)
        [.data ⟨.field field, one, left⟩, .data ⟨.field field, two, right⟩] =
        .returned [.data (.boolean (decide (left = right)))] := Domain.Calculations.fieldEqual field left right
  rw [reading_context]
  normalize_artifact_operations [multiply, add, equal] unfolding [DomainVM.observation, DomainVM.outcome, DomainVM.readback,
    Domain.evaluate, Domain.step, DeferredRounds.participant, DeferredRoundsParticipant.participant, nominalData,
    readingContext, PIR.Process.interpret, Original.forgetCheckpoints, PIR.Yields,
    Domain.templateOrigin, Domain.queryOrigin, Template.origin, Template.qualify, Template.repeats,
    Domain.atCoordinates, Context.message, Context.query, Context.role, Context.suite, Context.contract,
    Context.request, Context.replacement?, Context.service, DomainAdapter.readbackValues,
    DomainAdapter.readbackValue, DomainAdapter.readbackData, DomainAdapter.readbackHistory,
    DomainAdapter.readbackEvent, DomainAdapter.readbackPayload, Structured.Ty.isService,
    Bool.not_false, Bool.not_true, List.isEmpty_nil, List.take_nil, List.append_assoc,
    Template.applicationPrefix, Structured.qualifyProtocolSite, Origin.message, Origin.query, Request.draw,
    decimal, decimalDigit, Domain.Payload.field, Domain.Payload.boolean, eq_mpr_eq_cast, cast_eq,
    Nat.reduceLT]
  intros
  rfl

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Scalar ABI readback and nominal selected acceptance agree on every actual
participant return; every stop and unread proof suffix is retained. -/
theorem canonical_acceptance (program : Structured.Program) (challenge : History F G → m F)
    (x : F) (initial : History F G) (proof : Proof F G) :
    (byteAcceptance DeferredRounds.acceptancePosition ∘
      nativeObservation DeferredRounds.context.suite Origin.withoutCoordinates initial) <$>
      DomainAdapter.run Origin.withoutCoordinates initial challenge
        (DomainVM.observation program DeferredRounds.context DeferredRounds.participant.instructions
          DeferredRounds.participant.returned
          (nominalData x ++ [Domain.Value.transcript DeferredRounds.context.suite []])) proof =
    nominalAcceptance DeferredRounds.acceptancePosition <$>
      DomainAdapter.run Origin.withoutCoordinates initial challenge
        (DomainVM.observation program DeferredRounds.context DeferredRounds.participant.instructions
          DeferredRounds.participant.returned
          (nominalData x ++ [Domain.Value.transcript DeferredRounds.context.suite []])) proof := by
  apply run_map_yields Origin.withoutCoordinates initial challenge _ _
    (readable_returns program x Origin.withoutCoordinates initial)
  · intro reason unread; rfl
  · intro values unread readable
    exact byteAcceptance_readable DeferredRounds.context.suite Origin.withoutCoordinates initial
      DeferredRounds.acceptancePosition values unread readable

/-- The schedule's returned references give the actual participant's complete
checked output tuple. Only administrative checkpoints are forgotten. -/
theorem participant_observation (program : Structured.Program) (x : F) :
    ((Domain.participant (Structured.ringModel F G) program DeferredRounds.context DeferredRounds.participant
        (nominalData x ++ [Domain.Value.transcript DeferredRounds.context.suite []])).bind
        (fun result => .done result.values)).interpret Original.forgetCheckpoints =
      DomainVM.observation program DeferredRounds.context DeferredRounds.participant.instructions
        DeferredRounds.participant.returned
        (nominalData x ++ [Domain.Value.transcript DeferredRounds.context.suite []]) := by
  exact DomainVM.participant_observation program DeferredRounds.context DeferredRounds.participant _ rfl return_schema

/-- Complete returned tuple and unread-emptiness observation at the native
threshold, composed with normalization of the actual nonidentical schedule. -/
theorem executable_observation (program : Structured.Program) (challenge : History F G → m F)
    (decode : PhysicalType → List UInt8 → Option (Payload F G)) {budget : Nat} (sufficient : 35 ≤ budget)
    (x : F) (initial : History F G) (bytes : List UInt8) :
    Run.observe <$> execute installed validator DeferredRounds.context challenge decode budget
      (DeferredRounds.inputs x) initial bytes =
    nativeObservation DeferredRounds.context.suite Origin.withoutCoordinates initial <$>
      DomainAdapter.run Origin.withoutCoordinates initial challenge
        (DomainVM.observation program DeferredRounds.context DeferredRounds.participant.instructions
          DeferredRounds.participant.returned
          (nominalData x ++ [Domain.Value.transcript DeferredRounds.context.suite []]))
        (decodeProof decode receives bytes) := by
  have native := checked_execute_static program DeferredRounds.context initial challenge installed
    DeferredRounds.participant validator decode budget (prepared program) lowered (nativeFinal program)
    (native_checked program) (DeferredRounds.inputs x) bytes (admitted x) (nominalData x) (embedded x) 35 total sufficient
  rw [schedule_normalized, plan_types] at native
  exact native

/-- At every budget and for every byte string/header, native acceptance prunes
the actual canonical participant's acceptance. -/
theorem executable_prunes (program : Structured.Program) (challenge : History F G → m F)
    (decode : PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat) (binding : List UInt8)
    (x : F) (initial : History F G) (bytes : List UInt8) :
    Prunes (fun decision => decision = false)
      (Zkc.Executable.validate installed validator DeferredRounds.context challenge decode budget binding
        DeferredRounds.acceptancePosition (DeferredRounds.inputs x) initial bytes)
      (nominalAcceptance DeferredRounds.acceptancePosition <$>
        DomainAdapter.run Origin.withoutCoordinates initial challenge
          (DomainVM.observation program DeferredRounds.context DeferredRounds.participant.instructions
            DeferredRounds.participant.returned
            (nominalData x ++ [Domain.Value.transcript DeferredRounds.context.suite []]))
          (decodeProof decode receives (bytes.drop 40))) := by
  have native := checked_validate_prunes program DeferredRounds.context initial challenge installed
    DeferredRounds.participant validator decode budget (prepared program) lowered (nativeFinal program)
    (native_checked program) binding DeferredRounds.acceptancePosition (DeferredRounds.inputs x) bytes
    (admitted x) (nominalData x) (embedded x)
  rw [schedule_normalized, plan_types] at native
  exact native

/-- Exact host header and sufficient budget, retaining complete returned tuple
readback and whole-proof consumption at the canonical participant boundary. -/
theorem executable_validate (program : Structured.Program) (challenge : History F G → m F)
    (decode : PhysicalType → List UInt8 → Option (Payload F G)) {budget : Nat} (sufficient : 35 ≤ budget)
    (binding : List UInt8) (x : F) (initial : History F G) (bytes : List UInt8)
    (header : bytes.take 40 = magic ++ binding) :
    Zkc.Executable.validate installed validator DeferredRounds.context challenge decode budget binding
      DeferredRounds.acceptancePosition (DeferredRounds.inputs x) initial bytes =
    nominalAcceptance DeferredRounds.acceptancePosition <$>
      DomainAdapter.run Origin.withoutCoordinates initial challenge
        (DomainVM.observation program DeferredRounds.context DeferredRounds.participant.instructions
          DeferredRounds.participant.returned
          (nominalData x ++ [Domain.Value.transcript DeferredRounds.context.suite []]))
        (decodeProof decode receives (bytes.drop 40)) := by
  have native := validate_of_execute_observation installed validator DeferredRounds.context challenge decode budget
    binding DeferredRounds.acceptancePosition (DeferredRounds.inputs x) initial bytes _
    (executable_observation program challenge decode sufficient x initial (bytes.drop 40))
  simp only [header, ite_true, Functor.map_map] at native
  rw [native]
  exact canonical_acceptance program challenge x initial (decodeProof decode receives (bytes.drop 40))

/-- Short budgets and bad headers reject while preserving preceding actions. -/
theorem executable_rejects (program : Structured.Program) (challenge : History F G → m F)
    (decode : PhysicalType → List UInt8 → Option (Payload F G)) {budget : Nat} (binding : List UInt8)
    (x : F) (initial : History F G) (bytes : List UInt8)
    (short : budget < 35 ∨ bytes.take 40 ≠ magic ++ binding) :
    Zkc.Executable.validate installed validator DeferredRounds.context challenge decode budget binding
      DeferredRounds.acceptancePosition (DeferredRounds.inputs x) initial bytes =
      (fun _ => false) <$> Zkc.Executable.validate installed validator DeferredRounds.context challenge decode budget binding
        DeferredRounds.acceptancePosition (DeferredRounds.inputs x) initial bytes := by
  exact checked_validate_rejects_static program DeferredRounds.context initial challenge budget installed
    DeferredRounds.participant validator decode (prepared program) lowered (nativeFinal program) (native_checked program)
    35 total binding DeferredRounds.acceptancePosition (DeferredRounds.inputs x) bytes (admitted x)
    (nominalData x) (embedded x) short

end ZkcExamples.Executable.DeferredRounds
