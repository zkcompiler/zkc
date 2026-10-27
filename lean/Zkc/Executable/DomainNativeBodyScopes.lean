module

public import Zkc.Executable.DomainNativeLocalSoundness

@[expose] public section
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source

theorem nativeBody_finalReading (program : Structured.Program) (context : Context)
    (vocabulary : Vocabulary) (validator : Validator) :
    ∀ (steps : List Step) (names : List (String × Nat)) (scope : NativeScope)
      (codes : List Code) (returned : List Nat) (rawFinal : Reading) (final : NativeScope),
      readBody vocabulary validator steps names scope.reading = .ok (codes, returned, rawFinal) →
      checkNativeCode program context codes scope = some final → final.reading = rawFinal := by
  intro steps
  induction steps with
  | nil => intro names scope codes returned rawFinal final reading; simp [readBody] at reading
  | cons step rest ih =>
    intro names scope codes returned rawFinal final reading checked
    cases step with
    | ret values =>
      cases rest with
      | cons => simp [readBody, Step.name] at reading
      | nil =>
        simp only [readBody] at reading
        split at reading
        · cases reading; change some scope = some final at checked; cases checked; rfl
        · cases reading
    | operation site binding parameters inputs outputs =>
      simp only [readBody] at reading
      split at reading
      · rename_i resolved resolvedEq
        split at reading
        · rename_i references referencesRead
          split at reading
          · rename_i operation declared advances operationRead
            split at reading
            · split at reading
              · rename_i codes' returned' R'' bodyRead
                cases reading
                obtain ⟨middle, headCheck, tailCheck⟩ := checkNativeCode_cons program context _ _ _ _ checked
                have eq := nativeOperation_reading program context scope middle site resolved references operation declared advances operationRead headCheck
                exact ih _ middle _ _ _ final (by rw [eq]; exact bodyRead) tailCheck
              · cases reading
            · cases reading
          · cases reading
        · cases reading
      · cases reading
    | constant site output value =>
      simp only [readBody] at reading
      split at reading
      · rename_i codes' returned' R'' bodyRead
        cases reading
        obtain ⟨middle, headCheck, tailCheck⟩ := checkNativeCode_cons program context _ _ _ _ checked
        have eq : middle = scope.append [.data .boolean] false := by
          simpa [checkNativeItem, nativeResults, Calculation.op, Structured.Op.arguments, Structured.Op.results,
            NativeSlot.sort, dataType] using headCheck.symm
        subst middle
        exact ih _ _ _ _ _ final (by simpa [NativeScope.reading, NativeScope.append, NativeSlot.sort] using bodyRead) tailCheck
      · cases reading
    | cond site condition captures yes no outputs =>
      unfold readBody at reading
      split at reading
      · cases reading
      · rename_i heq; simp at heq
      · rename_i heq; simp at heq
      · rename_i heq; simp at heq
      · rename_i site' condition' stopSite rest' heq
        simp only [List.cons.injEq, Step.cond.injEq] at heq
        obtain ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩ := heq
        split at reading
        · split at reading
          · split at reading
            · rename_i codes' returned' R'' bodyRead
              cases reading
              obtain ⟨middle, headCheck, tailCheck⟩ := checkNativeCode_cons program context _ _ _ _ checked
              have eq : middle = scope := by
                obtain ⟨slots, moves, resultCheck, _, eq⟩ := checkNativeStep_results program context scope middle _ _ _ 2 headCheck
                simp only [nativeResults] at resultCheck
                split at resultCheck
                · cases resultCheck; simpa [NativeScope.append] using eq
                · cases resultCheck
              subst middle
              exact ih _ _ _ _ _ final bodyRead tailCheck
            · cases reading
          · cases reading
        · cases reading
      · cases reading
    | iterate => simp [readBody, Step.name] at reading
    | stop => simp [readBody, Step.name] at reading
    | yield => simp [readBody, Step.name] at reading
    | unsupported => simp [readBody, Step.name] at reading

end Zkc.Executable.DomainVM
