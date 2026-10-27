module

public import Zkc.Executable.DomainNativeReadingLaws

@[expose] public section
/-! Transparent native bodies execute through actual nominal Domain steps.
The continuation is constrained only at states reached by the structural
induction, with no numerical relationship on input data. -/
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source Zkc.Construction.Uniform
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m] [LawfulMonad m]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
private theorem nominalBoolean (env : Environment F G) (reference : Nat)
    (sorted : (env.map Domain.Value.sort)[reference]? = some (.data .boolean)) :
    ∃ value, env[reference]? = some (.data (.boolean value)) := by
  rw [List.getElem?_map] at sorted
  cases found : env[reference]? with
  | none => simp [found] at sorted
  | some value =>
    simp only [found, Option.map_some, Option.some.injEq] at sorted
    cases value with
    | indices | transcript => cases sorted
    | data payload =>
      rcases payload with ⟨ty, supported, contents⟩
      cases sorted
      exact ⟨contents, rfl⟩

theorem native_localK_metered
    (program : Structured.Program) (context : Context) (initial : History F G)
    (challenge : History F G → m F) (vocabulary : Vocabulary) (validator : Validator)
    (budget : Nat) (cost : String → List (Value F G) → Nat)
    (data : List (Value F G)) (call : String × String) :
    ∀ (steps : List Step) (names : List (String × Nat)) (scope : NativeScope)
      (codes : List Code) (returned : List Nat) (rawFinal : Reading) (final : NativeScope),
      readBody vocabulary validator steps names scope.reading = .ok (codes, returned, rawFinal) →
      checkNativeCode program context codes scope = some final →
      ∀ (named : Env F G) (state : State F G) (env : Environment F G) (scalar : List (Value F G))
        (proof : Proof F G) (exit : List (Value F G) → State F G → m (Run F G))
        (continuation : Environment F G → Proof F G → Nat → m (PIR.Outcome (Environment F G) × Proof F G)),
        Reached context.suite Origin.withoutCoordinates initial data scope.reading state env scalar →
        scope.Holds env → EnvAgrees scalar named names →
        (∀ nextState nominal values results,
          Reached context.suite Origin.withoutCoordinates initial data final.reading nextState nominal values →
          final.Holds nominal → nextState.frames = state.frames → nextState.proof = state.proof →
          (∃ more, values = scalar ++ more) → Construction.read values returned = some results →
          Run.observe <$> exit results nextState =
            nativeObservation context.suite Origin.withoutCoordinates initial <$> continuation nominal proof nextState.used) →
        Run.observe <$> Executable.localK vocabulary validator context challenge budget call true none steps named state exit =
          nativeObservation context.suite Origin.withoutCoordinates initial <$>
            meteredK program context Origin.withoutCoordinates initial challenge cost budget codes env proof state.used continuation := by
  intro steps
  induction steps with
  | nil => intro names scope codes returned rawFinal final reading; simp [readBody] at reading
  | cons step rest ih =>
    intro names scope codes returned rawFinal final reading checked named state env scalar proof exit continuation reached holds agrees exits
    cases step with
    | ret values =>
      cases rest with
      | cons => simp [readBody, Step.name] at reading
      | nil =>
        simp only [readBody] at reading
        split at reading
        · rename_i references referencesRead
          cases reading
          change some scope = some final at checked
          cases checked
          obtain ⟨lookups, bounds⟩ := lookupAll_eq agrees referencesRead
          obtain ⟨results, resultsRead⟩ := mapM_getElem?_some scalar bounds
          simp only [Executable.localK, Executable.localStep, meteredK, meteredStep]
          by_cases tick : state.used < budget
          · have fits : state.used + 1 ≤ budget := by omega
            simp only [tick, fits, ite_true, lookups, resultsRead]
            exact exits state.charge env scalar results (reached.congr rfl) holds rfl rfl ⟨[], by simp⟩ resultsRead
          · have short : ¬ state.used + 1 ≤ budget := by omega
            simp [tick, short, nativeObservation, DomainAdapter.readbackOutcome, Executable.observation]
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
            · rename_i lengths
              split at reading
              · rename_i codes' returned' R'' bodyRead
                cases reading
                obtain ⟨middle, headCheck, tailCheck⟩ := checkNativeCode_cons program context _ _ _ _ checked
                have middleReading := nativeOperation_reading program context scope middle site resolved references operation declared advances operationRead headCheck
                obtain ⟨lookups, _⟩ := lookupAll_eq agrees referencesRead
                change Run.observe <$> Executable.localStep vocabulary validator context challenge budget call true none
                  (.operation site binding parameters inputs outputs) named state _ exit = _
                apply native_operation_metered program context initial challenge vocabulary validator budget cost call site binding parameters
                  inputs outputs resolved resolvedEq scope middle operation references declared advances operationRead headCheck lengths
                  data scalar state named env reached holds lookups proof _ exit _
                intro values nominal nextState valuesLength newReached newHolds used frames proofs
                rw [← used]
                apply ih (outputs.zip (List.range' scope.reading.sorts.length declared.length) ++ names) middle codes' returned rawFinal final (by rw [middleReading]; exact bodyRead) tailCheck
                  _ nextState nominal (scalar ++ values) proof exit continuation newReached newHolds
                · have pushed := agrees.pushAll outputs values (lengths.trans valuesLength.symm)
                  simpa only [valuesLength, reached.native.length] using pushed
                · intro last nominal' scalar' results reached' holds' frames' proofs' extension resultsRead
                  obtain ⟨more, rfl⟩ := extension
                  exact exits last nominal' _ results reached' holds' (frames'.trans frames) (proofs'.trans proofs) ⟨values ++ more, by simp⟩ resultsRead
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
        have middleEq : middle = scope.append [.data .boolean] false := by
          simpa [checkNativeItem, nativeResults, Calculation.op, Structured.Op.arguments, Structured.Op.results, NativeSlot.sort, dataType] using headCheck.symm
        subst middle
        change Run.observe <$> Executable.localStep vocabulary validator context challenge budget call true none
          (.constant site output value) named state _ exit = _
        apply native_constant_metered program context Origin.withoutCoordinates initial challenge vocabulary validator budget cost call site output value
          named state env proof _ exit _
        apply ih _ (scope.append [.data .boolean] false) _ _ _ final (by simpa [NativeScope.reading, NativeScope.append, NativeSlot.sort] using bodyRead) tailCheck
          _ state.charge _ (scalar ++ [.data (.boolean value)]) proof exit continuation
          (reached.keep (embedValues_erases _ _ _ rfl) (.cons (show NativeSlot.Holds (.data .boolean) (Domain.Value.data (.boolean value)) from rfl) .nil) rfl) (holds.append (.cons (show NativeSlot.Holds (.data .boolean) (Domain.Value.data (.boolean value)) from rfl) .nil))
        · simpa only [reached.native.length, NativeScope.reading, List.length_map] using agrees.push output (.data (.boolean value))
        · intro last nominal' scalar' results reached' holds' frames' proofs' extension resultsRead
          obtain ⟨more, rfl⟩ := extension
          exact exits last nominal' _ results reached' holds' frames' proofs' ⟨[.data (.boolean value)] ++ more, by simp⟩ resultsRead
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
        · rename_i reference referenceRead
          split at reading
          · rename_i boolean
            split at reading
            · rename_i codes' returned' R'' bodyRead
              cases reading
              obtain ⟨middle, headCheck, tailCheck⟩ := checkNativeCode_cons program context _ _ _ _ checked
              have middleEq : middle = scope := by
                obtain ⟨slots, moves, resultCheck, declared, finalEq⟩ := checkNativeStep_results program context scope middle _ _ _ 2 headCheck
                simp only [nativeResults] at resultCheck
                split at resultCheck
                · cases resultCheck; simpa [NativeScope.append] using finalEq
                · cases resultCheck
              subst middle
              obtain ⟨value, nominalFound⟩ := nominalBoolean env reference (by rw [reached.schema]; exact boolean)
              have scalarFound : scalar[reference]? = some (.data (.boolean value)) := by
                rw [reached.erases.get, nominalFound]; rfl
              have lookup := (lookupName_eq agrees referenceRead).2.trans scalarFound
              change Run.observe <$> Executable.localStep vocabulary validator context challenge budget call true none
                (.cond site condition [] [.yield []] [.stop stopSite "reject"] []) named state _ exit = _
              apply native_guard_metered program context Origin.withoutCoordinates initial challenge vocabulary validator budget cost call site stopSite condition value
                named state env reference lookup nominalFound proof _ exit _
              apply ih _ scope _ _ _ final bodyRead tailCheck _ state.charge.charge env scalar proof exit continuation (reached.congr rfl) holds agrees
              intro last nominal' scalar' results reached' holds' frames' proofs' extension resultsRead
              exact exits last nominal' scalar' results reached' holds' frames' proofs' extension resultsRead
            · cases reading
          · cases reading
        · cases reading
      · cases reading
    | iterate => simp [readBody, Step.name] at reading
    | stop => simp [readBody, Step.name] at reading
    | yield => simp [readBody, Step.name] at reading
    | unsupported => simp [readBody, Step.name] at reading

end Zkc.Executable.DomainVM
