module

public import Zkc.Executable.DomainNativeScopeLaws

@[expose] public section

/-! All-reply interpretation of the complete finite Code scope certificate. -/
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source Zkc.Construction.Uniform
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem NativeScope.Holds.index {scope : NativeScope} {env : Environment F G}
    (holds : scope.Holds env) {reference : Nat}
    (found : scope.slots[reference]? = some (.data .index)) :
    ∃ value, env[reference]? = some (.data (.index value)) := by
  obtain ⟨value, looked, sorted⟩ := holds.get found
  cases value with
  | transcript | indices => cases sorted
  | data payload =>
      rcases payload with ⟨ty, supported, contents⟩
      simp only [NativeSlot.Holds, Domain.Value.sort, ValueSort.data.injEq] at sorted
      subst ty
      exact ⟨contents, looked⟩

private theorem evaluate_single (program : Structured.Program) (context : Context)
    (instruction : Instruction) (env : Environment F G) (property : Environment F G → Prop)
    (holds : PIR.Yields property (Domain.step (Structured.ringModel F G) program context instruction env)) :
    PIR.Yields property (Domain.evaluate (Structured.ringModel F G) program context [instruction] env) := by
  simp only [Domain.evaluate, PIR.Yields]
  intro _
  apply holds.bind
  intro final found _
  exact found

private theorem loop_scope (program : Structured.Program) (context : Context)
    (scope innerFinal : NativeScope) (site : String) (maximum count : Nat)
    (references yielded : List Nat) (carried : List NativeSlot) (body : List Instruction)
    (countSort : scope.slots[count]? = some (.data .index))
    (readCarried : references.map (scope.slots[·]?) = carried.map some)
    (yieldedSorts : yielded.map (innerFinal.slots[·]?) = carried.map some)
    (bodyPreserves : ∀ (env : Environment F G),
      (⟨scope.slots ++ .data .index :: carried,
        match transcriptPosition (carried.map NativeSlot.sort) with
        | some position => scope.slots.length + 1 + position | none => scope.current⟩ : NativeScope).Holds env →
      PIR.Yields innerFinal.Holds
        (Domain.evaluate (Structured.ringModel F G) program context body env))
    (env : Environment F G) (holds : scope.Holds env) :
    PIR.Yields
      (⟨scope.slots ++ carried, match transcriptPosition (carried.map NativeSlot.sort) with
        | some position => scope.slots.length + position | none => scope.current⟩ : NativeScope).Holds
      (Domain.step (Structured.ringModel F G) program context
        ⟨.loop site maximum yielded, count :: references, carried.map NativeSlot.sort, body⟩ env) := by
  obtain ⟨bound, boundFound⟩ := holds.index countSort
  obtain ⟨initial, initialFound, initialHolds⟩ := holds.read readCarried
  have initialSorted : Domain.sortsMatch (carried.map NativeSlot.sort) initial = true := by
    simp only [Domain.sortsMatch, beq_iff_eq]
    exact NativeScope.Holds.schema (scope := ⟨carried, 0⟩) initialHolds
  change PIR.Yields (fun final => List.Forall₂ NativeSlot.Holds (scope.slots ++ carried) final) _
  simp only [Domain.step, boundFound, initialFound, initialSorted, and_true]
  split
  · have invariant := Domain.iterate_yields
      (Domain.evaluate (Structured.ringModel F G) program context body) env yielded
      (carried.map NativeSlot.sort)
      (fun _ values => List.Forall₂ NativeSlot.Holds carried values)
      (by
        intro index rest values valuesHolds
        have start :
            (⟨scope.slots ++ .data .index :: carried,
              match transcriptPosition (carried.map NativeSlot.sort) with
              | some position => scope.slots.length + 1 + position | none => scope.current⟩ : NativeScope).Holds
              (env ++ .data (.index index) :: values) :=
          holds.append (.cons (show NativeSlot.Holds (.data .index) (.data (.index index)) from rfl) valuesHolds)
        exact (bodyPreserves _ start).mono fun final found next nextRead _ => by
          obtain ⟨actual, actualRead, actualHolds⟩ := found.read yieldedSorts
          rw [nextRead] at actualRead
          cases actualRead
          exact actualHolds)
      (List.range bound) initial initialHolds
    apply invariant.bind
    intro final finalHolds
    have sorted : Domain.sortsMatch (carried.map NativeSlot.sort) final = true := by
      simp only [Domain.sortsMatch, beq_iff_eq]
      exact NativeScope.Holds.schema (scope := ⟨carried, 0⟩) finalHolds
    simp only [sorted, ite_true, PIR.Yields]
    exact holds.append finalHolds
  · trivial

mutual
/-- Every scope and depth annotation in a successful finite check holds at
all continuing points of canonical Code, for every typed effect reply. -/
theorem checkNativeCode_preserves (program : Structured.Program) (context : Context) :
    ∀ (code : List Code) (scope final : NativeScope),
      checkNativeCode program context code scope = some final →
      ∀ (env : Environment F G), scope.Holds env →
        PIR.Yields final.Holds
          (Domain.evaluate (Structured.ringModel F G) program context (Code.instructionList code) env)
  | [], scope, final, checked, env, holds => by
      cases checked
      exact holds
  | head :: rest, scope, final, checked, env, holds => by
      simp only [checkNativeCode] at checked
      cases first : checkNativeItem program context head scope with
      | none => simp [first] at checked
      | some middle =>
          simp only [first, bind, Option.bind] at checked
          simp only [Code.instructionList, Domain.evaluate_append]
          apply (checkNativeItem_preserves program context head scope middle first env holds).bind
          intro next nextHolds
          exact checkNativeCode_preserves program context rest middle final checked next nextHolds

theorem checkNativeItem_preserves (program : Structured.Program) (context : Context) :
    ∀ (code : Code) (scope final : NativeScope),
      checkNativeItem program context code scope = some final →
      ∀ (env : Environment F G), scope.Holds env →
        PIR.Yields final.Holds
          (Domain.evaluate (Structured.ringModel F G) program context (Code.instructionsOf code) env)
  | .charge _, scope, final, checked, env, holds => by
      cases checked
      exact holds
  | .step instruction charged, scope, final, checked, env, holds =>
      evaluate_single program context instruction env _
        (checkNativeStep_preserves program context scope final instruction charged checked env holds)
  | .helper instruction, scope, final, checked, env, holds =>
      evaluate_single program context instruction env _
        (checkNativeHelper_preserves program context scope final instruction checked env holds)
  | .loop site maximum yielded operands declared body, scope, final, checked, env, holds => by
      cases operands with
      | nil => simp [checkNativeItem] at checked
      | cons count references =>
          simp only [checkNativeItem] at checked
          split at checked
          · cases checked
          · rename_i counter
            have countSort : scope.slots[count]? = some (.data .index) := by simpa using counter
            cases read : references.mapM (scope.slots[·]?) with
            | none => simp [read] at checked
            | some carried =>
                simp only [read, bind, Option.bind] at checked
                split at checked
                · cases checked
                · rename_i admitted
                  have declaredEq : carried.map NativeSlot.sort = declared := by
                    by_contra different
                    exact admitted (Or.inl different)
                  subst declared
                  change ((checkNativeCode program context body _).bind _) = some final at checked
                  rw [Option.bind_eq_some_iff] at checked
                  obtain ⟨innerFinal, innerChecked, checked⟩ := checked
                  split at checked
                  · cases checked
                  · rename_i invariant
                    cases checked
                    have yieldedSorts : yielded.map (innerFinal.slots[·]?) = carried.map some := by
                      by_contra different
                      exact invariant (Or.inl different)
                    apply evaluate_single
                    apply loop_scope program context scope innerFinal site maximum count references yielded carried
                      (Code.instructionList body) countSort (mapM_optional _ read) yieldedSorts
                    · intro start startHolds
                      exact checkNativeCode_preserves program context body _ innerFinal innerChecked start startHolds
                    · exact holds
end

/-- The compact computed certificate has its once-proved semantic meaning. -/
theorem NativeCertificate.preserves (program : Structured.Program) (context : Context)
    (code : List Code) (scope : NativeScope)
    (certificate : NativeCertificate program context code scope)
    (env : Environment F G) (holds : scope.Holds env) :
    PIR.Yields certificate.final.Holds
      (Domain.evaluate (Structured.ringModel F G) program context (Code.instructions code) env) := by
  rw [← Code.instructionList_eq]
  exact checkNativeCode_preserves program context code scope certificate.final certificate.checked env holds

end Zkc.Executable.DomainVM
