module

public import ZkcExamples.Executable.SumcheckFamilyResources
public import Zkc.Executable.DomainNativeByteTransport

@[expose] public section

/-! Parameterized honest acceptance by actual native byte validation. Static
artifact admission and local mathematical/helper obligations have separate
owners. Neither record contains a whole-program equality or success premise. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Executable.SumcheckFamily
open Zkc Zkc.Construction Zkc.Executable Zkc.Source
open Zkc.Construction.Uniform Zkc.Construction.Uniform.DomainAdapter
open SumcheckShape

/-- Method-neutral finite native admission, plus exact source shape, Code,
returned references, input schema and receive plan. The vocabulary, program,
context, nominal names, coordinate codec and maximum are all parameters. -/
structure Artifact where
  description : ProgramShape.Description
  vocabulary : Vocabulary
  participant : Participant
  validator : Validator
  lowered : Lowered
  final : DomainVM.NativeScope
  checked : DomainVM.checkNativeLowering description.program description.context vocabulary participant validator =
    .ok (lowered, final)
  instructions : participant.instructions = SumcheckShape.instructions description.names description.maximum
  returns : participant.returned = [13,10]
  inputSorts : participant.inputs = [.data (.vector description.names.scalar), .data (.field description.names.scalar),
    .data .index, .transcript description.names.suite]
  codeReading : lowered.code = code description.names description.maximum
  returned : lowered.returned = [13,10]
  coordinate : PhysicalType
  plan : lowered.plan = [.loop 2 description.maximum [.receive coordinate, .receive coordinate]]
  admitted : ∀ {F G : Type} (values : List F) (claim : F) (rounds : Nat),
    validator.admits [(.vector description.names.scalar values : Value F G),
      .data (.field description.names.scalar claim), .index rounds] = true

namespace Artifact
def dataInputs (a : Artifact) {F G : Type} (values : List F) (claim : F) (rounds : Nat) : List (Value F G) :=
  [.vector a.description.names.scalar values, .data (.field a.description.names.scalar claim), .index rounds]

def nominalInputs (a : Artifact) {F G : Type} (values : List F) (claim : F) (rounds : Nat) : DomainVM.Environment F G :=
  [.data (.vector a.description.names.scalar values), .data (.field a.description.names.scalar claim), .data (.index rounds)]

def charge (_ : Artifact) (appendBound rounds : Nat) : Nat := 72 + (appendBound + 57) * rounds
end Artifact

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- A realization supplies only actual local helper laws, bounded helper
prices, occurrence laws and preparation. Round/loop correspondence, resource
sufficiency and mathematical honesty are generated, not admission fields. -/
structure Realization (a : Artifact) (appendBound : Nat) : Prop where
  occurrences : Source.Occurrences a.description
  helpers : Source.Helpers (F := F) (G := G) a.description
  prices : Source.Prices a.description (helperCost a.vocabulary a.validator (F := F) (G := G)) appendBound
  prepared : ∀ name ∈ Instruction.helperList a.participant.instructions,
    Prepared a.vocabulary a.validator (Domain.helperTable (Structured.ringModel F G) a.description.program) name

theorem code_instructions (n : Names) (maximum : Nat) :
    Code.instructions (code n maximum) = instructions n maximum := by
  rw [← Code.instructionList_eq]
  rfl

/-- Exact success, including the nominal transcript and complete unread proof,
derived for every admitted realization by the shared mathematical induction. -/
theorem honest_metered (a : Artifact) (appendBound : Nat) (realization : Realization (F := F) (G := G) a appendBound)
    (oracle : History F G → F) (budget : Nat) (values : List F) (rounds : Nat)
    (admitted : rounds ≤ a.description.maximum) (shaped : values.length = 2 ^ rounds)
    (initial : History F G) (fits : a.charge appendBound rounds ≤ budget) :
    ∃ returned unread, Source.Success a.description returned unread ∧
      DomainVM.metered (m := Id) a.description.program a.description.context Origin.withoutCoordinates initial oracle
        (helperCost a.vocabulary a.validator) budget a.lowered
        (ProgramShape.inputs a.description values values.sum rounds [])
        ((SumcheckMessages.honestRounds (Source.transcript a.description) oracle initial values rounds).map
          (.field a.description.names.scalar)) = (.returned returned, unread) := by
  apply DomainVM.metered_success
  · have enough := ProgramShape.sufficient a.description (helperCost a.vocabulary a.validator) (36 + appendBound)
      (Source.budgetContract a.description realization.occurrences realization.helpers _ appendBound realization.prices)
      budget values values.sum rounds []
      ((SumcheckMessages.honestRounds (Source.transcript a.description) oracle initial values rounds).map
        (.field a.description.names.scalar)) shaped (by simpa only [Artifact.charge, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using fits)
    simpa only [DomainVM.Sufficient, ProgramShape.reading, a.codeReading, a.returned] using enough
  · rw [a.codeReading, a.returned, code_instructions]
    exact Source.observation_passes a.description realization.occurrences realization.helpers oracle initial values rounds admitted shaped

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem receive_types (a : Artifact) (values : List F) (claim : F) (rounds : Nat)
    (admitted : rounds ≤ a.description.maximum) :
    Plan.types (a.dataInputs (G := G) values claim rounds) a.lowered.plan = List.replicate (2 * rounds) a.coordinate := by
  rw [a.plan]
  simp only [Plan.types, Artifact.dataInputs, List.getElem?_cons_succ, List.getElem?_cons_zero, admitted, ite_true]
  clear admitted
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
      simp only [List.replicate_succ, List.flatten_cons, List.cons_append, List.nil_append]
      rw [ih]
      simp [Nat.mul_succ, List.replicate_succ]

/-- Generic native byte completeness. Only the field-coordinate codec inverse,
32-byte binding, original table shape, admitted round count and sufficient
operational budget are required of a run. Initial history is arbitrary. -/
theorem honest_accepted (a : Artifact) (appendBound : Nat) (realization : Realization (F := F) (G := G) a appendBound)
    (oracle : History F G → F) (decode : PhysicalType → List UInt8 → Option (Payload F G)) (encode : F → List UInt8)
    (roundtrip : ∀ value, decode a.coordinate (encode value) = some (.field a.description.names.scalar value))
    (bounded : ∀ value, (encode value).length ≤ proofLimit) (budget : Nat) (binding : List UInt8)
    (bindingLength : binding.length = 32) (values : List F) (rounds : Nat)
    (admitted : rounds ≤ a.description.maximum) (shaped : values.length = 2 ^ rounds)
    (initial : History F G) (fits : a.charge appendBound rounds ≤ budget) :
    validate (m := Id) a.vocabulary a.validator a.description.context oracle decode budget binding 0
      (a.dataInputs values values.sum rounds) initial
      (SumcheckMessages.honestBytes encode binding
        (SumcheckMessages.honestRounds (Source.transcript a.description) oracle initial values rounds)) = true := by
  have decoded : decodeProof decode (Plan.types (a.dataInputs (G := G) values values.sum rounds) a.lowered.plan)
      ((SumcheckMessages.honestBytes encode binding
        (SumcheckMessages.honestRounds (Source.transcript a.description) oracle initial values rounds)).drop 40) =
      (SumcheckMessages.honestRounds (Source.transcript a.description) oracle initial values rounds).map
        (.field a.description.names.scalar) := by
    rw [SumcheckMessages.honestBytes, messageBytes_body encode bindingLength, receive_types a values values.sum rounds admitted,
      ← SumcheckMessages.honestRounds_length (Source.transcript a.description) oracle initial values rounds]
    exact decodeProof_messages decode a.coordinate encode (.field a.description.names.scalar) roundtrip bounded _
  obtain ⟨returned, unread, good, executed⟩ := honest_metered a appendBound realization oracle budget values rounds admitted shaped initial fits
  obtain ⟨rfl, history, rfl, suffix, mapped⟩ := good
  rw [DomainVM.checked_validate_metered (m := Id) a.description.program a.description.context initial oracle
    a.vocabulary a.participant a.validator decode budget realization.prepared a.lowered a.final a.checked binding 0
    (a.dataInputs values values.sum rounds)
    (SumcheckMessages.honestBytes encode binding
      (SumcheckMessages.honestRounds (Source.transcript a.description) oracle initial values rounds))
    (a.admitted values values.sum rounds) (a.nominalInputs values values.sum rounds) rfl]
  rw [show (SumcheckMessages.honestBytes encode binding
      (SumcheckMessages.honestRounds (Source.transcript a.description) oracle initial values rounds)).take 40 = magic ++ binding from
    messageBytes_header encode bindingLength _, ite_eq_left rfl, decoded]
  have frameEq : a.nominalInputs (G := G) values values.sum rounds ++ [.transcript a.description.context.suite []] =
      ProgramShape.inputs a.description values values.sum rounds [] := by rw [a.description.suite]; rfl
  rw [frameEq, executed]
  change DomainVM.byteAcceptance 0 (DomainVM.nativeObservation a.description.context.suite Origin.withoutCoordinates initial
    (.returned [.data (.boolean true), .transcript a.description.names.suite history], [])) = true
  simp [DomainVM.byteAcceptance, DomainVM.nativeObservation, Executable.observation,
    Uniform.DomainAdapter.readbackOutcome, Uniform.DomainAdapter.readbackValues,
    Uniform.DomainAdapter.readbackValue, Uniform.DomainAdapter.readbackData,
    a.description.suite, mapped, selectedTrue]

end ZkcExamples.Executable.SumcheckFamily
