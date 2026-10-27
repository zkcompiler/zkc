module

public import Zkc.Executable.DomainNativeCodeScope

@[expose] public section

/-! Admission of the nominal entry scope. The native input validator supplies
all actual data sorts; the finite artifact check supplies the transcript suite.
No restriction on the values of admitted field/group/index inputs is added. -/
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source Zkc.Construction.Uniform

def nativeEntryScope (validator : Validator) : NativeScope :=
  ⟨validator.inputs.map (NativeSlot.ofSort ∘ (·.2.sort)), validator.inputs.length - 1⟩

def checkNativeEntry (context : Context) (validator : Validator) : Bool :=
  (validator.inputs.map (·.2.sort)).getLast? == some (.transcript context.suite) &&
    (validator.inputs.map (NativeSlot.ofSort ∘ (·.2.sort))).all NativeSlot.rigid

@[simp] theorem NativeSlot.sort_ofSort (sort : ValueSort) : (NativeSlot.ofSort sort).sort = sort := by
  cases sort <;> rfl

theorem nativeEntryScope_reading (validator : Validator) :
    (nativeEntryScope validator).reading =
      ⟨validator.inputs.map (·.2.sort), validator.inputs.length - 1⟩ := by
  simp [nativeEntryScope, NativeScope.reading, List.map_map, Function.comp_def]

variable {F G : Type}

/-- The suite is tied to the actual native input declaration, rather than to
an unchecked host choice. The nominal suffix starts empty, with opaque initial
scalar history supplied only to readback and the scalar oracle. -/
theorem nativeEntry_reached (context : Context) (validator : Validator)
    (checked : checkNativeEntry context validator = true)
    (data : List (Value F G)) (initial : History F G) (bytes : List UInt8)
    (key : Origin → Origin) (admitted : validator.admits data = true) :
    ∃ nominal, DomainAdapter.embedValues data = some nominal ∧
      Reached context.suite key initial data (nativeEntryScope validator).reading
        (Executable.initial validator data initial bytes)
        (nominal ++ [.transcript context.suite []]) (data ++ [.transcript initial]) ∧
      (nativeEntryScope validator).Holds (nominal ++ [.transcript context.suite []]) := by
  obtain ⟨suite, sorts, sortsEq, dataSorts⟩ := admits_sorts validator admitted
  have checks := checked
  simp only [checkNativeEntry, Bool.and_eq_true, beq_iff_eq] at checks
  obtain ⟨last, rigid⟩ := checks
  rw [sortsEq] at last
  have suiteEq : suite = context.suite := by simpa using last
  obtain ⟨actual, nominal, embedded, reached⟩ := Reached.initial validator data initial bytes key admitted
  have actualEq : actual = context.suite := by
    have liveSort : (nominal ++ [Domain.Value.transcript actual []]).map Domain.Value.sort = validator.inputs.map (·.2.sort) :=
      reached.schema
    have nominalLength : data.length = nominal.length := length_of_mapM_some embedded
    have size : validator.inputs.length = data.length + 1 := by
      have := congrArg List.length liveSort
      simp only [List.length_map, List.length_append, List.length_singleton] at this
      omega
    have sorted := congrArg (·.getLast?) liveSort
    simpa [List.getLast?_map, List.getLast?_append, last, sortsEq, Domain.Value.sort] using sorted
  subst actual
  have size : validator.inputs.length = data.length + 1 := by
    have := congrArg List.length reached.schema
    have nominalLength : data.length = nominal.length := length_of_mapM_some embedded
    simp only [List.length_map, List.length_append, List.length_singleton] at this
    omega
  have readingEq : (nativeEntryScope validator).reading = ⟨validator.inputs.map (·.2.sort), data.length⟩ := by
    rw [nativeEntryScope_reading, size]
    rfl
  refine ⟨nominal, embedded, readingEq ▸ reached, ?_⟩
  apply nativeHolds_of_schema
  · exact rigid
  · simpa [nativeEntryScope, List.map_map, Function.comp_def] using reached.schema

/-- Strengthened artifact admission. Raw checkLowering is retained unchanged;
this finite check additionally owns all nominal eligibility obligations. -/
def checkNativeLowering (program : Structured.Program) (context : Context)
    (vocabulary : Vocabulary) (participant : Participant) (validator : Validator) :
    Except Refusal (Lowered × NativeScope) := do
  let lowered ← checkLowering vocabulary participant validator
  unless checkNativeEntry context validator do throw (.different "nominal entry")
  match checkNativeCode program context lowered.code (nativeEntryScope validator) with
  | some final => pure (lowered, final)
  | none => throw (.different "nominal operation scope")

/-- Successful strengthened admission exposes only finite checks and the
original reader result. It never supplies the desired execution equation. -/
theorem checkNativeLowering_checks (program : Structured.Program) (context : Context)
    (vocabulary : Vocabulary) (participant : Participant) (validator : Validator)
    (lowered : Lowered) (final : NativeScope)
    (checked : checkNativeLowering program context vocabulary participant validator = .ok (lowered, final)) :
    checkLowering vocabulary participant validator = .ok lowered ∧
      checkNativeEntry context validator = true ∧
      checkNativeCode program context lowered.code (nativeEntryScope validator) = some final := by
  unfold checkNativeLowering at checked
  simp only [bind, Except.bind] at checked
  cases read : checkLowering vocabulary participant validator with
  | error => simp [read] at checked
  | ok candidate =>
      simp only [read] at checked
      split at checked
      · rename_i entry
        cases scope : checkNativeCode program context candidate.code (nativeEntryScope validator) with
        | none => simp [scope] at checked
        | some result =>
            simp only [scope] at checked
            obtain ⟨rfl, rfl⟩ := checked
            exact ⟨rfl, entry, scope⟩
      · cases checked

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- A successfully checked actual artifact starts in, and preserves, its
nominal scope for every admitted native tuple and every typed action reply. -/
theorem checkNativeLowering_preserves (program : Structured.Program) (context : Context)
    (vocabulary : Vocabulary) (participant : Participant) (validator : Validator)
    (lowered : Lowered) (final : NativeScope)
    (checked : checkNativeLowering program context vocabulary participant validator = .ok (lowered, final))
    (data : List (Value F G)) (initial : History F G) (bytes : List UInt8)
    (key : Origin → Origin) (admitted : validator.admits data = true) :
    ∃ nominal, DomainAdapter.embedValues data = some nominal ∧
      Reached context.suite key initial data (nativeEntryScope validator).reading
        (Executable.initial validator data initial bytes)
        (nominal ++ [.transcript context.suite []]) (data ++ [.transcript initial]) ∧
      PIR.Yields final.Holds (Domain.evaluate (Structured.ringModel F G) program context
        (Code.instructions lowered.code) (nominal ++ [.transcript context.suite []])) := by
  obtain ⟨_, entry, code⟩ := checkNativeLowering_checks program context vocabulary participant validator lowered final checked
  obtain ⟨nominal, embedded, reached, holds⟩ := nativeEntry_reached context validator entry data initial bytes key admitted
  refine ⟨nominal, embedded, reached, ?_⟩
  rw [← Code.instructionList_eq]
  exact checkNativeCode_preserves program context lowered.code (nativeEntryScope validator) final code _ holds

end Zkc.Executable.DomainVM
