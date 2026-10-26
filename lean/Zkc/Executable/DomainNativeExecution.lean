module

public import Zkc.Executable.DomainNativeSoundness
public import Zkc.Executable.DomainCompleteness

@[expose] public section
/-! Arbitrary-byte execution and host validation of nominally checked native
artifacts. Raw lowering remains a structural check; the independent finite
nominal certificate supplies the additional scope obligations. -/
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source Zkc.Construction.Uniform

/-- Extract only the raw reading, without depending on the retired semantic
interpretation of the lowering check. -/
theorem checkLowering_read (vocabulary : Vocabulary) (participant : Participant)
    (validator : Validator) (lowered : Lowered)
    (accepted : checkLowering vocabulary participant validator = .ok lowered) :
    validator.read vocabulary (Instruction.helperList participant.instructions) = .ok lowered :=
  (checkLowering_checks accepted).1



variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Every admitted tuple obtains its nominal initial state from actual native
admission; no relation-validity premise is used. The conclusion applies to all
raw bytes, malformed decoding, budgets and scalar oracle replies. -/
theorem native_execute_metered
    (program : Structured.Program) (context : Context) (initial : History F G)
    (challenge : History F G → m F) (vocabulary : Vocabulary) (validator : Validator)
    (decode : PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)
    (helpers : List String)
    (prepared : ∀ name ∈ helpers, Prepared vocabulary validator (Domain.helperTable (Structured.ringModel F G) program) name)
    (lowered : Lowered) (final : NativeScope)
    (reading : validator.read vocabulary helpers = .ok lowered)
    (entry : checkNativeEntry context validator = true)
    (checked : checkNativeCode program context lowered.code (nativeEntryScope validator) = some final)
    (data : List (Value F G)) (bytes : List UInt8)
    (admitted : validator.admits data = true)
    (nominal : Environment F G) (embedded : DomainAdapter.embedValues data = some nominal) :
    Run.observe <$> execute vocabulary validator context challenge decode budget data initial bytes =
      nativeObservation context.suite Origin.withoutCoordinates initial <$>
        metered program context Origin.withoutCoordinates initial challenge (helperCost vocabulary validator) budget lowered
          (nominal ++ [.transcript context.suite []]) (decodeProof decode (Plan.types data lowered.plan) bytes) := by
  obtain ⟨actual, actualEmbedded, reached, holds⟩ := nativeEntry_reached context validator entry data initial bytes Origin.withoutCoordinates admitted
  have equal : actual = nominal := Option.some.inj (actualEmbedded.symm.trans embedded)
  subst actual
  unfold Validator.read at reading
  dsimp only at reading
  simp only [readActionList_eq] at reading
  split_ifs at reading with conditions
  split at reading
  · rename_i code plan returned R' bodyRead
    cases reading
    obtain ⟨suite, sorts, sortsEq, dataSorts⟩ := admits_sorts validator admitted
    have inputsLength : validator.inputs.length = data.length + 1 := by
      have := congrArg List.length sortsEq
      have lengths := congrArg List.length dataSorts
      simp only [List.length_map, List.length_append, List.length_singleton] at this lengths
      omega
    have dataLength : (validator.inputs.map (·.2.sort)).length - 1 = data.length := by simp [inputsLength]
    rw [dataLength] at bodyRead
    have agrees : FrameAgrees (data ++ [.transcript initial])
        ⟨.participant, (validator.inputs.map (·.1)).zip (data ++ [.transcript initial])⟩
        ((validator.inputs.map (·.1)).zip (List.range (validator.inputs.map (·.2.sort)).length)) := by
      intro name reference found
      have lengths : (validator.inputs.map (·.1)).length = (data ++ [Value.transcript initial]).length := by simp [inputsLength]
      have same := lookup_zip_range' (outputs := validator.inputs.map (·.1))
        (results := data ++ [Value.transcript initial]) [] lengths name reference
      simp only [List.length_nil, List.nil_append, Nat.zero_add] at same
      rw [List.length_map, List.range_eq_range'] at found
      exact same (by simpa [inputsLength] using found)
    have related := native_runK_metered program context initial challenge vocabulary validator decode budget data helpers prepared
      validator.body _ (nativeEntryScope validator) code plan (.returned returned) R' final
      (by simpa only [nativeEntryScope_reading, inputsLength, Nat.add_sub_cancel] using bodyRead) checked
      (Executable.initial validator data initial bytes) (nominal ++ [.transcript context.suite []])
      (data ++ [.transcript initial]) _ [] [] (fun _ s => pure (s.stop .contract none none))
      (fun env unread used => pure (if used + 1 ≤ budget then
        match Domain.read env returned with | some results => .returned results | none => .stopped .refused
        else .stopped .exhausted, unread)) reached holds rfl agrees ⟨rfl, rfl, fun _ _ _ => rfl⟩
    unfold execute metered
    simp only [admitted, ite_true]
    convert related using 1; simp only [Executable.initial, List.append_nil]; rfl
  all_goals cases reading

/-- Finite strengthened admission discharges the raw reader and entry premises
of the generic native-to-Domain theorem. -/
theorem checked_execute_metered
    (program : Structured.Program) (context : Context) (initial : History F G)
    (challenge : History F G → m F) (vocabulary : Vocabulary) (participant : Participant) (validator : Validator)
    (decode : PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)
    (prepared : ∀ name ∈ Instruction.helperList participant.instructions,
      Prepared vocabulary validator (Domain.helperTable (Structured.ringModel F G) program) name)
    (lowered : Lowered) (final : NativeScope)
    (checked : checkNativeLowering program context vocabulary participant validator = .ok (lowered, final))
    (data : List (Value F G)) (bytes : List UInt8) (admitted : validator.admits data = true)
    (nominal : Environment F G) (embedded : DomainAdapter.embedValues data = some nominal) :
    Run.observe <$> execute vocabulary validator context challenge decode budget data initial bytes =
      nativeObservation context.suite Origin.withoutCoordinates initial <$>
        metered program context Origin.withoutCoordinates initial challenge (helperCost vocabulary validator) budget lowered
          (nominal ++ [.transcript context.suite []]) (decodeProof decode (Plan.types data lowered.plan) bytes) := by
  obtain ⟨raw, entry, scope⟩ := checkNativeLowering_checks program context vocabulary participant validator lowered final checked
  exact native_execute_metered program context initial challenge vocabulary validator decode budget _ prepared lowered final
    (checkLowering_read vocabulary participant validator lowered raw) entry scope data bytes admitted nominal embedded

/-- The exact native 40-byte magic/binding check and selected Boolean
acceptance compose with the arbitrary-byte correspondence. -/
theorem checked_validate_metered
    (program : Structured.Program) (context : Context) (initial : History F G)
    (challenge : History F G → m F) (vocabulary : Vocabulary) (participant : Participant) (validator : Validator)
    (decode : PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)
    (prepared : ∀ name ∈ Instruction.helperList participant.instructions,
      Prepared vocabulary validator (Domain.helperTable (Structured.ringModel F G) program) name)
    (lowered : Lowered) (final : NativeScope)
    (checked : checkNativeLowering program context vocabulary participant validator = .ok (lowered, final))
    (binding : List UInt8) (position : Nat) (data : List (Value F G)) (bytes : List UInt8)
    (admitted : validator.admits data = true)
    (nominal : Environment F G) (embedded : DomainAdapter.embedValues data = some nominal) :
    Executable.validate vocabulary validator context challenge decode budget binding position data initial bytes =
      if bytes.take 40 = magic ++ binding then
        (byteAcceptance position ∘ nativeObservation context.suite Origin.withoutCoordinates initial) <$>
          metered program context Origin.withoutCoordinates initial challenge (helperCost vocabulary validator) budget lowered
            (nominal ++ [.transcript context.suite []])
            (decodeProof decode (Plan.types data lowered.plan) (bytes.drop 40))
      else pure false := by
  have lifted := validate_of_execute_observation vocabulary validator context challenge decode budget binding position data initial bytes _
    (checked_execute_metered program context initial challenge vocabulary participant validator decode budget prepared lowered final checked data (bytes.drop 40) admitted nominal embedded)
  convert lifted using 1; simp only [Functor.map_map, Function.comp_def]

end Zkc.Executable.DomainVM
