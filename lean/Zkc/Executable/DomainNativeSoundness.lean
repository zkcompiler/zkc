module

public import Zkc.Executable.DomainNativeLoopScopes
public import Zkc.Executable.DomainSoundness

@[expose] public section
/-! Native participant frame and byte correspondence with nominal Domain Code. -/
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source Zkc.Construction.Uniform
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- The induction continuation at a participant return or loop yield. This is
not artifact certificate data; the root return discharges it definitionally. -/
def NativeEnds (context : Context) (initial : History F G)
    (decode : PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)
    (data base : List (Value F G)) (ending : Ending) (final : NativeScope)
    (rest : List (Frame F G)) (after : List PhysicalType)
    (exit : List (Value F G) → State F G → m (Run F G))
    (continuation : Environment F G → Proof F G → Nat → m (PIR.Outcome (Environment F G) × Proof F G)) : Prop :=
  match ending with
  | .yielded references =>
    ∀ (state : State F G) (env : Environment F G) (scalar results : List (Value F G)) (top : Frame F G),
      Reached context.suite Origin.withoutCoordinates initial data final.reading state env scalar →
      final.Holds env → state.frames = top :: rest → (∃ more, scalar = base ++ more) → Construction.read scalar references = some results →
      Run.observe <$> (if state.used < budget then exit results state.charge else pure (state.stop .limit none none)) =
        nativeObservation context.suite Origin.withoutCoordinates initial <$>
          continuation env (decodeProof decode after state.proof) state.used
  | .returned references =>
    rest = [] ∧ after = [] ∧ ∀ env unread used,
      continuation env unread used = pure
        (if used + 1 ≤ budget then
          match Domain.read env references with
          | some results => .returned results
          | none => .stopped .refused
        else .stopped .exhausted, unread)

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] [LawfulMonad m] in
theorem NativeEnds.extend {context : Context} {initial : History F G}
    {decode : PhysicalType → List UInt8 → Option (Payload F G)} {budget : Nat}
    {data base : List (Value F G)} {ending : Ending} {final : NativeScope}
    {rest : List (Frame F G)} {after : List PhysicalType}
    {exit : List (Value F G) → State F G → m (Run F G)}
    {continuation : Environment F G → Proof F G → Nat → m (PIR.Outcome (Environment F G) × Proof F G)}
    (ends : NativeEnds context initial decode budget data base ending final rest after exit continuation)
    (more : List (Value F G)) :
    NativeEnds context initial decode budget data (base ++ more) ending final rest after exit continuation := by
  cases ending with
  | returned => exact ends
  | yielded refs =>
    intro state env scalar results top reached holds frames extension read
    obtain ⟨tail, rfl⟩ := extension
    exact ends state env _ results top reached holds frames ⟨more ++ tail, by simp⟩ read

theorem native_runK_metered
    (program : Structured.Program) (context : Context) (initial : History F G)
    (challenge : History F G → m F) (vocabulary : Vocabulary) (validator : Validator)
    (decode : PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)
    (data : List (Value F G)) (helpers : List String)
    (prepared : ∀ name ∈ helpers, Prepared vocabulary validator (Domain.helperTable (Structured.ringModel F G) program) name) :
    ∀ (actions : List Action) (names : List (String × Nat)) (scope : NativeScope)
      (codes : List Code) (plan : List Plan) (ending : Ending) (rawFinal : Reading) (final : NativeScope),
      readActions vocabulary validator helpers data.length actions names scope.reading = .ok (codes, plan, ending, rawFinal) →
      checkNativeCode program context codes scope = some final →
      ∀ (state : State F G) (env : Environment F G) (scalar : List (Value F G)) (top : Frame F G)
        (rest : List (Frame F G)) (after : List PhysicalType)
        (exit : List (Value F G) → State F G → m (Run F G))
        (continuation : Environment F G → Proof F G → Nat → m (PIR.Outcome (Environment F G) × Proof F G)),
        Reached context.suite Origin.withoutCoordinates initial data scope.reading state env scalar →
        scope.Holds env → state.frames = top :: rest → FrameAgrees scalar top names →
        NativeEnds context initial decode budget data scalar ending final rest after exit continuation →
        Run.observe <$> Executable.runK vocabulary validator context challenge decode budget actions state exit =
          nativeObservation context.suite Origin.withoutCoordinates initial <$>
            meteredK program context Origin.withoutCoordinates initial challenge (helperCost vocabulary validator) budget codes env
              (decodeProof decode (Plan.types data plan ++ after) state.proof) state.used continuation
  | [], names, scope, codes, plan, ending, rawFinal, final, reading, checked => by simp [readActions] at reading
  | [.yield values], names, scope, codes, plan, ending, rawFinal, final, reading, checked => by
    simp only [readActions] at reading
    split at reading
    · rename_i references referencesRead
      cases reading
      change some scope = some final at checked
      cases checked
      intro state env scalar top rest after exit continuation reached holds frames agrees ends
      obtain ⟨lookups, bounds⟩ := lookupAll_eq agrees referencesRead
      obtain ⟨results, resultsRead⟩ := mapM_getElem?_some scalar bounds
      have same := ends state env scalar results top reached holds frames ⟨[], by simp⟩ resultsRead
      simpa only [Executable.runK, Executable.runStep, meteredK, Plan.types, List.nil_append, frames, lookups, resultsRead] using same
    · cases reading
  | [.ret values], names, scope, codes, plan, ending, rawFinal, final, reading, checked => by
    simp only [readActions] at reading
    split at reading
    · rename_i references referencesRead
      split at reading
      · rename_i custody
        cases reading
        change some scope = some final at checked
        cases checked
        intro state env scalar top rest after exit continuation reached holds frames agrees ends
        obtain ⟨rfl, rfl, finishes⟩ := ends
        obtain ⟨lookups, bounds⟩ := lookupAll_eq agrees referencesRead
        obtain ⟨results, resultsRead⟩ := mapM_getElem?_some scalar bounds
        obtain ⟨nominal, nominalRead, erased⟩ := reached.erases.of_read resultsRead
        have kept := custody_of_read reached.native resultsRead custody
        simp only [Executable.runK, Executable.runStep, meteredK, Plan.types, List.append_nil, frames, lookups, resultsRead, finishes]
        by_cases tick : state.used < budget
        · have fits : state.used + 1 ≤ budget := by omega
          simp [tick, fits, kept, nominalRead, nativeObservation, DomainAdapter.readbackOutcome,
            show DomainAdapter.readbackValues context.suite Origin.withoutCoordinates initial nominal = some results from erased, Executable.observation, Run.observe, Result.outcome, State.done, State.charge, decodeProof_unread]
        · have short : ¬ state.used + 1 ≤ budget := by omega
          simp [tick, short, nativeObservation, DomainAdapter.readbackOutcome, Executable.observation]
      · cases reading
    · cases reading
  | .receive site schema peer output physical :: actions, names, scope, codes, plan, ending, rawFinal, final, reading, checked => by
    simp only [readActions] at reading
    split at reading
    · rename_i ty physicalSort
      split at reading
      · split at reading
        · rename_i codes' plan' ending' R'' restRead
          cases reading
          obtain ⟨middle, headCheck, tailCheck⟩ := checkNativeCode_cons program context _ _ _ _ checked
          obtain ⟨rfl, eligible, rfl⟩ := native_receive_results program context scope middle site schema peer ty headCheck
          intro state env scalar top rest after exit continuation reached holds frames agrees ends
          change Run.observe <$> Executable.runStep vocabulary validator context challenge decode budget (.receive site site peer output physical) state _ exit = _
          simp only [meteredK, Plan.types, List.cons_append]
          apply native_receive_metered program context Origin.withoutCoordinates initial challenge vocabulary validator decode _ budget site peer output physical ty physicalSort eligible
            state env (Plan.types data plan' ++ after) _ exit _
          intro encoded unread payload framed decoded typed
          have tyEq : ty = payloadType payload := ValueSort.data.inj (physicalSort.symm.trans typed)
          subst ty
          rw [State.bind_eq (by exact frames)]
          apply native_runK_metered program context initial challenge vocabulary validator decode budget data helpers prepared actions
            _ (scope.append [.data (payloadType payload)] false) _ _ _ _ final
            (by simpa [NativeScope.reading, NativeScope.append, NativeSlot.sort] using restRead) tailCheck
            _ _ (scalar ++ [.data payload]) _ rest after exit continuation
          · exact reached.keep (embedValues_erases _ _ _ (by cases payload <;> rfl)) (.cons (show NativeSlot.Holds (.data (payloadType payload))
              (Domain.Value.data (DomainAdapter.embedPayload payload)) from by cases payload <;> rfl) .nil) rfl
          · exact holds.append (.cons (show NativeSlot.Holds (.data (payloadType payload))
              (Domain.Value.data (DomainAdapter.embedPayload payload)) from by cases payload <;> rfl) .nil)
          · rfl
          · simpa [reached.native.length, NativeScope.reading] using agrees.push output (.data payload)
          · exact ends.extend [.data payload]
        · cases reading
      · cases reading
    · cases reading
  | .call site name inputs outputs :: actions, names, scope, codes, plan, ending, rawFinal, final, reading, checked => by
    simp only [readActions] at reading
    split at reading
    · rename_i callee references calleeEq referencesRead
      split at reading
      · rename_i facts
        obtain ⟨arity, formalSorts⟩ := facts
        intro state env scalar top rest after exit continuation reached holds frames agrees ends
        obtain ⟨lookups, bounds⟩ := lookupAll_eq agrees referencesRead
        obtain ⟨values, scalarRead⟩ := mapM_getElem?_some scalar bounds
        have valuesLength := length_of_mapM_some scalarRead
        have args : lookupAll top.env inputs = some values := lookups.trans scalarRead
        split at reading
        · rename_i isHelper
          split at reading
          · rename_i helperFacts
            obtain ⟨free, outputsLength, dataResults⟩ := helperFacts
            split at reading
            · rename_i codes' plan' ending' R'' restRead
              cases reading
              obtain ⟨middle, headCheck, tailCheck⟩ := checkNativeCode_cons program context _ _ _ _ checked
              obtain ⟨helper, helperCheck, inputsCheck, _, outputEligibility, declared, rfl⟩ := nativeHelper_results program context scope middle name references _ headCheck
              obtain ⟨nominal, nominalRead, embedded⟩ := holds.readData reached.erases inputsCheck scalarRead
              have sorted := sorted_read reached.native.sorted scalarRead (expected := callee.inputs.map (·.2.sort)) (by rw [← formalSorts]; simp)
              change Run.observe <$> Executable.runStep vocabulary validator context challenge decode budget (.call site name inputs outputs) state _ exit = _
              simp only [meteredK]
              rw [declared]
              apply native_helper_metered program context Origin.withoutCoordinates initial challenge vocabulary validator decode budget site name inputs outputs
                helper helperCheck outputEligibility callee calleeEq free (prepared name (by simpa using isHelper))
                state top rest frames values args (arity.trans valuesLength) sorted (by simpa using outputsLength)
                env nominal references nominalRead embedded (decodeProof decode (Plan.types data plan ++ after) state.proof) _ exit _
              intro results charge nominalResults computed called resultEmbedding resultSchema
              have count := (prepared name (by simpa using isHelper) callee calleeEq values (arity.trans valuesLength) sorted)
              rw [computed, called] at count
              obtain ⟨_, resultCount, _⟩ := count
              have outputHolds : List.Forall₂ NativeSlot.Holds (helper.outputs.map NativeSlot.data) nominalResults :=
                nativeHolds_of_schema (by simp [NativeSlot.rigid]) (by simpa [List.map_map, Function.comp_def, NativeSlot.sort] using resultSchema)
              let helperState : State F G := { state with
                used := state.used + 1 + charge
                frames := ⟨top.id, outputs.zip results ++ top.env⟩ :: rest
                events := state.events ++ [.enter (.call site name)] ++ [.leave (.call site name) .returned] }
              apply native_runK_metered program context initial challenge vocabulary validator decode budget data helpers prepared actions
                _ (scope.append (helper.outputs.map NativeSlot.data) false) _ _ _ _ final
                (by simpa [NativeScope.reading, NativeScope.append, List.map_map, Function.comp_def, NativeSlot.sort, declared] using restRead) tailCheck
                helperState _ (scalar ++ results) ⟨top.id, outputs.zip results ++ top.env⟩ rest after exit continuation
                (reached.keep (embedValues_erases _ _ _ resultEmbedding) outputHolds rfl) (holds.append outputHolds) rfl
              · have pushed := agrees.pushAll outputs results (outputsLength.trans (by simpa using resultCount.symm))
                have resultLength : results.length = helper.outputs.length := by
                  rw [← (embedValues_erases context.suite Origin.withoutCoordinates initial resultEmbedding).length]
                  simpa using congrArg List.length resultSchema
                simpa [reached.native.length, resultLength, NativeScope.reading, declared] using pushed
              · exact ends.extend results
            · cases reading
          · cases reading
        · split at reading
          · rename_i body returned R₁ bodyRead
            split at reading
            · rename_i returnedFacts
              obtain ⟨outputsLength, returnedSorts⟩ := returnedFacts
              split at reading
              · rename_i codes' plan' ending' R'' restRead
                cases reading
                obtain ⟨middle, headCheck, tailCheck⟩ := checkNativeCode_cons program context _ _ _ _ checked
                change some scope = some middle at headCheck
                cases headCheck
                change checkNativeCode program context (body ++ codes') scope = some final at tailCheck
                rw [checkNativeCode_append program context body codes' scope] at tailCheck
                obtain ⟨bodyFinal, bodyCheck, restCheck⟩ := Option.bind_eq_some_iff.mp tailCheck
                have bodyReading := nativeBody_finalReading program context vocabulary validator callee.body _ scope body returned R₁ bodyFinal bodyRead bodyCheck
                simp only [Executable.runK, Executable.runStep, frames, calleeEq, args, meteredK, meteredStep, List.cons_append]
                rw [meteredK_append]
                by_cases tick : state.used < budget
                · have fits : state.used + 1 ≤ budget := by omega
                  simp only [tick, fits, ite_true, show callee.inputs.length = values.length from arity.trans valuesLength]
                  let callState : State F G := { state with
                    used := state.used + 1
                    frames := ⟨.call site name, (callee.inputs.map (·.1)).zip values⟩ :: top :: rest
                    events := state.events ++ [.enter (.call site name)] }
                  apply native_localK_metered program context initial challenge vocabulary validator budget (helperCost vocabulary validator) data (site, name)
                    callee.body _ scope body returned R₁ bodyFinal bodyRead bodyCheck _ callState env scalar _ _ _
                    (reached.congr rfl) holds (EnvAgrees.enter _ bounds scalarRead)
                  intro nextState nominal values' results reached' holds' frames' proofs' extension resultsRead
                  simp only [frames']
                  have lengths : outputs.length = results.length := outputsLength.trans (length_of_mapM_some resultsRead)
                  simp only [lengths, ite_true]
                  obtain ⟨more, rfl⟩ := extension
                  have agrees' := agrees.extend more
                  let resumed : State F G := { nextState with
                    frames := ⟨top.id, outputs.zip results ++ top.env⟩ :: rest
                    events := nextState.events ++ [.leave (.call site name) .returned] }
                  have related := native_runK_metered program context initial challenge vocabulary validator decode budget data helpers prepared actions
                    _ bodyFinal _ _ _ _ final (by rw [bodyReading]; exact restRead) restCheck resumed nominal (scalar ++ more) ⟨top.id, outputs.zip results ++ top.env⟩ rest after exit continuation
                    (reached'.congr rfl) holds' rfl
                    (EnvAgrees.leave agrees' outputsLength (read_bounds resultsRead) resultsRead) (ends.extend more)
                  simpa [resumed, callState, proofs'] using related
                · have short : ¬ state.used + 1 ≤ budget := by omega
                  simp [tick, short, nativeObservation, DomainAdapter.readbackOutcome, Executable.observation]
              · cases reading
            · cases reading
          · cases reading
      · cases reading
    · cases reading
    · cases reading
  | .loop site count maximum induction carried captures body outputs :: actions, names, scope, codes, plan,
      ending, rawFinal, final, reading, checked => by
    simp only [readActions] at reading
    split at reading
    · rename_i counter initialRefs captured counterRead initialRead capturedRead
      split at reading
      · rename_i conditions
        split at reading
        · rename_i inner innerPlan yielded R₁ innerRead
          split at reading
          · rename_i yieldConditions
            split at reading
            · rename_i codes' plan' ending' R'' restRead
              cases reading
              obtain ⟨loopFinal, loopCheck, restCheck⟩ := checkNativeCode_cons program context _ _ _ _ checked
              obtain ⟨slots, innerFinal, countChecked, carriedChecked, declaredEq, initialCustody, bodyCheck,
                yieldedChecked, yieldedCustody, untouched, rfl⟩ := nativeLoop_results program context scope loopFinal site maximum counter initialRefs yielded _ inner loopCheck
              intro state env scalar top rest after exit continuation reached holds frames agrees ends
              obtain ⟨counterLt, counterSort, sortsLength, carriedLength, outputsLength, _, _, _⟩ := conditions
              have sortsLength' : slots.length = initialRefs.length := by
                have := congrArg List.length declaredEq
                simpa using this.symm.trans sortsLength
              obtain ⟨counterBound, counterSame⟩ := lookupName_eq agrees counterRead
              obtain ⟨bound, nominalBound⟩ := holds.index countChecked
              have boundFound : scalar[counter]? = some (.index bound) := by rw [reached.erases.get, nominalBound]; rfl
              have dataCount : data[counter]? = some (.index bound) := by rw [← reached.native.inputs counter counterLt]; exact boundFound
              rw [boundFound] at counterSame
              obtain ⟨initialLookups, initialBounds⟩ := lookupAll_eq agrees initialRead
              obtain ⟨initialValues, initialScalarRead⟩ := mapM_getElem?_some scalar initialBounds
              change Construction.read scalar initialRefs = some initialValues at initialScalarRead
              obtain ⟨initialNominal, initialNominalRead, initialHolds⟩ := holds.read carriedChecked
              have initialErases : Erases context.suite Origin.withoutCoordinates initial initialNominal initialValues := by
                have := reached.erases.read initialRefs
                rw [initialNominalRead, Option.bind_some, initialScalarRead] at this
                exact this
              have initialLength : initialValues.length = slots.length := by
                rw [← length_of_mapM_some initialScalarRead, sortsLength']
              obtain ⟨capturedLookups, capturedBounds⟩ := lookupAll_eq agrees capturedRead
              obtain ⟨capturedValues, capturedEq⟩ := mapM_getElem?_some scalar capturedBounds
              have declared : initialRefs.filterMap (scope.reading.sorts[·]?) = slots.map NativeSlot.sort := declaredEq
              rw [declared] at restRead innerRead
              have restReading : readActions vocabulary validator helpers data.length actions
                  (outputs.zip (List.range' scope.slots.length slots.length) ++ names) (scope.loopResult slots).reading =
                  .ok (codes', plan', ending, rawFinal) := by
                convert restRead using 1; simp only [NativeScope.loopResult, NativeScope.reading, List.map_append, List.length_map]; rfl
              have innerReading : readActions vocabulary validator helpers data.length body
                  ((induction, scope.slots.length) :: (carried.map (·.1)).zip (List.range' (scope.slots.length + 1) initialRefs.length) ++ captures.zip captured)
                  (scope.loopBody slots).reading = .ok (inner, innerPlan, .yielded yielded, R₁) := by
                convert innerRead using 1; simp only [NativeScope.loopBody, NativeScope.reading, List.map_append, List.map_cons, NativeSlot.sort, List.length_map]; rfl
              have initialMapRead : initialRefs.mapM (scalar[·]?) = some initialValues := initialScalarRead
              have initialSorted := NativeScope.Holds.schema (scope := ⟨slots, 0⟩) initialHolds
              have initialMatches : Domain.sortsMatch (slots.map NativeSlot.sort) initialNominal = true := by simp [Domain.sortsMatch, initialSorted]
              have current : scope.current < scalar.length := reached.native.current_bound
              have baseLength : scalar.length = scope.slots.length := by simpa [NativeScope.reading] using reached.native.length
              simp only [Executable.runK, Executable.runStep, frames, counterSame, initialLookups, initialMapRead,
                capturedLookups, capturedEq, meteredK, meteredStep, nominalBound, initialNominalRead,
                declared, initialMatches, and_true, Plan.types, dataCount, List.append_assoc]
              by_cases maxOk : bound ≤ maximum
              · by_cases tick : state.used < budget
                · have fits : state.used + 1 ≤ budget := by omega
                  simp only [maxOk, tick, fits, ite_true]
                  let LiveCarried : List (Value F G) → History F G → Prop := fun values live =>
                    match transcriptPosition (slots.map NativeSlot.sort) with
                    | some position => values[position]? = some (.transcript live)
                    | none => scalar[scope.current]? = some (.transcript live)
                  have iterate : ∀ (indices : List Nat) (values : List (Value F G)) (nominal : Environment F G) (s' : State F G),
                      s'.frames = top :: rest →
                      Erases context.suite Origin.withoutCoordinates initial nominal values →
                      List.Forall₂ NativeSlot.Holds slots nominal →
                      LiveCarried values s'.live →
                      Run.observe <$> Executable.loopK (fun s exit => Executable.runK vocabulary validator context challenge decode budget body s exit)
                        site induction (carried.map (·.1)) (captures.zip capturedValues) indices values s'
                        (fun results s'' => Executable.runK vocabulary validator context challenge decode budget actions (s''.bind outputs results) exit) =
                        nativeObservation context.suite Origin.withoutCoordinates initial <$>
                          meteredIterate budget (fun start unread used next => meteredK program context Origin.withoutCoordinates initial challenge
                            (helperCost vocabulary validator) budget inner start unread used next) env yielded (slots.map NativeSlot.sort)
                            indices nominal (decodeProof decode ((List.replicate indices.length (Plan.types data innerPlan)).flatten ++
                              (Plan.types data plan' ++ after)) s'.proof) s'.used
                            (fun final unread used => if Domain.sortsMatch (slots.map NativeSlot.sort) final then
                              meteredK program context Origin.withoutCoordinates initial challenge (helperCost vocabulary validator) budget codes'
                                (env ++ final) unread used continuation else pure (.stopped .refused, unread)) := by
                    intro indices
                    induction indices with
                    | nil =>
                      intro values nominal s' frames' erased nominalHolds live
                      have schema := NativeScope.Holds.schema (scope := ⟨slots, 0⟩) nominalHolds
                      have sortsMatchProof : Domain.sortsMatch (slots.map NativeSlot.sort) nominal = true := by simp [Domain.sortsMatch, schema]
                      have length : values.length = slots.length := by rw [← erased.length]; simpa using congrArg List.length schema
                      simp only [Executable.loopK, meteredIterate, List.length_nil, List.replicate_zero, List.flatten_nil,
                        List.nil_append, sortsMatchProof, ite_true]
                      rw [State.bind_eq frames']
                      apply native_runK_metered program context initial challenge vocabulary validator decode budget data helpers prepared actions
                        _ (scope.loopResult slots) _ _ _ _ final
                        restReading restCheck
                        _ (env ++ nominal) (scalar ++ values) _ rest after exit continuation
                      · apply reached.extendSlots erased nominalHolds
                        change (scalar ++ values)[(scope.loopResult slots).current]? = _
                        simp only [LiveCarried] at live
                        split at live
                        · rename_i position positionEq
                          simp only [NativeScope.loopResult, positionEq]
                          rw [List.getElem?_append_right (by simp [baseLength])]
                          simpa [baseLength, NativeScope.reading] using live
                        · rename_i positionEq
                          simp only [NativeScope.loopResult, positionEq]
                          rw [List.getElem?_append_left current]
                          exact live
                      · exact holds.append nominalHolds
                      · rfl
                      · have pushed := agrees.pushAll outputs values (by omega)
                        simpa [baseLength, NativeScope.reading, length] using pushed
                      · exact ends.extend values
                    | cons index indices ih =>
                      intro values nominal s' frames' erased nominalHolds live
                      have schema := NativeScope.Holds.schema (scope := ⟨slots, 0⟩) nominalHolds
                      have length : values.length = slots.length := by rw [← erased.length]; simpa using congrArg List.length schema
                      simp only [Executable.loopK, meteredIterate]
                      have proofSplit : (List.replicate (indices.length + 1) (Plan.types data innerPlan)).flatten ++
                          (Plan.types data plan' ++ after) = Plan.types data innerPlan ++
                            ((List.replicate indices.length (Plan.types data innerPlan)).flatten ++
                              (Plan.types data plan' ++ after)) := by simp [List.replicate_succ, List.flatten_cons, List.append_assoc]
                      rw [List.length_cons, proofSplit]
                      apply native_runK_metered program context initial challenge vocabulary validator decode budget data helpers prepared body
                        _ (scope.loopBody slots) inner innerPlan (.yielded yielded) R₁ innerFinal
                        innerReading bodyCheck
                        _ (env ++ Domain.Value.data (.index index) :: nominal) (scalar ++ .index index :: values) _ (s'.frames)
                        ((List.replicate indices.length (Plan.types data innerPlan)).flatten ++ (Plan.types data plan' ++ after)) _ _
                      · apply reached.extendSlots (show Erases context.suite Origin.withoutCoordinates initial
                            (Domain.Value.data (.index index) :: nominal) (.index index :: values) from by
                              simp only [Erases, DomainAdapter.readbackValues, List.mapM_cons, DomainAdapter.readbackValue, DomainAdapter.readbackData]
                              change (do let tail ← DomainAdapter.readbackValues context.suite Origin.withoutCoordinates initial nominal
                                         pure (Value.index index :: tail)) = some (Value.index index :: values)
                              rw [show DomainAdapter.readbackValues context.suite Origin.withoutCoordinates initial nominal = some values from erased]
                              rfl)
                          (.cons (show NativeSlot.Holds (.data .index) (Domain.Value.data (.index index)) from rfl) nominalHolds)
                        change (scalar ++ .index index :: values)[(scope.loopBody slots).current]? = _
                        simp only [LiveCarried] at live
                        split at live
                        · rename_i position positionEq
                          simp only [NativeScope.loopBody, positionEq]
                          rw [List.getElem?_append_right (by simp only [baseLength]; omega)]
                          have shift : scope.slots.length + 1 + position - scalar.length = position + 1 := by
                            simp only [baseLength]; omega
                          simpa [shift] using live
                        · rename_i positionEq
                          simp only [NativeScope.loopBody, positionEq]
                          rw [List.getElem?_append_left current]
                          exact live
                      · exact holds.append (.cons (show NativeSlot.Holds (.data .index) (Domain.Value.data (.index index)) from rfl) nominalHolds)
                      · rfl
                      · have keys : (induction, scope.slots.length) ::
                            ((carried.map (·.1)).zip (List.range' (scope.slots.length + 1) initialRefs.length) ++ captures.zip captured) =
                            (induction :: (carried.map (·.1) ++ captures)).zip
                              (scope.slots.length :: (List.range' (scope.slots.length + 1) initialRefs.length ++ captured)) := by
                          rw [List.zip_cons_cons, List.zip_append (by simp [carriedLength])]
                        have frameEnv : (induction, Value.index index) ::
                            ((carried.map (·.1)).zip values ++ captures.zip capturedValues) =
                            (induction :: (carried.map (·.1) ++ captures)).zip (.index index :: (values ++ capturedValues)) := by
                          rw [List.zip_cons_cons, List.zip_append (by simp [carriedLength, length, sortsLength'])]
                        change EnvAgrees _ ((induction, Value.index index) ::
                          ((carried.map (·.1)).zip values ++ captures.zip capturedValues)) _
                        simp only [List.cons_append]
                        rw [frameEnv, keys]
                        apply EnvAgrees.enter
                        · intro reference member
                          simp only [List.mem_cons, List.mem_append, List.mem_range'] at member
                          simp only [List.length_append, List.length_cons, baseLength]
                          rcases member with rfl | ⟨offset, offsetLt, rfl⟩ | member
                          · omega
                          · omega
                          · have := capturedBounds reference member; rw [baseLength] at this; omega
                        · simp only [List.mapM_cons]
                          have readValues := read_range' (scalar ++ [.index index]) values
                          simp only [List.length_append, List.length_cons, List.length_nil, List.append_assoc, List.singleton_append] at readValues
                          rw [baseLength] at readValues
                          have readCaptured := read_extend (.index index :: values) capturedEq
                          have head : (scalar ++ Value.index index :: values)[scope.slots.length]? = some (.index index) := by
                            rw [← baseLength, List.getElem?_append_right (le_refl _)]; simp
                          rw [head, show initialRefs.length = values.length by omega, List.mapM_append, readValues, readCaptured]
                          rfl
                      · intro s₃ nominal₃ scalar₃ results loopTop reached₃ holds₃ frames₃ extension resultsRead
                        obtain ⟨more, rfl⟩ := extension
                        obtain ⟨nextNominal, nextRead, nextHolds⟩ := holds₃.read yieldedChecked
                        have nextErases : Erases context.suite Origin.withoutCoordinates initial nextNominal results := by
                          have := reached₃.erases.read yielded
                          rw [nextRead, Option.bind_some, resultsRead] at this
                          exact this
                        have nextSchema := NativeScope.Holds.schema (scope := ⟨slots, 0⟩) nextHolds
                        have sortsMatchProof : Domain.sortsMatch (slots.map NativeSlot.sort) nextNominal = true := by simp [Domain.sortsMatch, nextSchema]
                        have nextLength : results.length = slots.length := by rw [← nextErases.length]; simpa using congrArg List.length nextSchema
                        change Run.observe <$> (if s₃.used < budget then _ else _) = _
                        by_cases tick₃ : s₃.used < budget
                        · have fits₃ : s₃.used + 1 ≤ budget := by omega
                          simp only [tick₃, ite_true, State.charge, frames₃, fits₃, nextRead, sortsMatchProof]
                          have namesLength : results.length = (carried.map (·.1)).length := by simp [nextLength]; omega
                          simp only [namesLength, ite_true]
                          apply ih results nextNominal _ (by simpa [frames₃] using frames') nextErases nextHolds
                          simp only [LiveCarried]
                          split
                          · rename_i position positionEq
                            have yieldedSorts : yielded.map (innerFinal.reading.sorts[·]?) = (slots.map NativeSlot.sort).map some := by
                              have := congrArg (List.map (Option.map NativeSlot.sort)) yieldedChecked
                              simpa [List.map_map, Function.comp_def, NativeScope.reading, List.getElem?_map] using this
                            obtain ⟨suite, suiteFound⟩ := transcriptPosition_sort positionEq
                            obtain ⟨reference, referenceAt, referenceSort⟩ := position_read yieldedSorts suiteFound
                            have isCurrent := custody_at yieldedCustody (List.mem_of_getElem? referenceAt) referenceSort
                            rw [value_at resultsRead referenceAt, isCurrent]
                            exact reached₃.native.live
                          · rename_i positionEq
                            have same := untouched (by simpa [declared] using positionEq)
                            have live₃ := reached₃.native.live
                            change (scalar ++ .index index :: values ++ more)[innerFinal.current]? = some (.transcript s₃.live) at live₃
                            rw [same] at live₃
                            have prefixBound : scope.current < (scalar ++ Value.index index :: values).length := by simp only [List.length_append, List.length_cons]; omega
                            rw [List.getElem?_append_left prefixBound, List.getElem?_append_left current] at live₃
                            exact live₃
                        · have short : ¬ s₃.used + 1 ≤ budget := by omega
                          simp [tick₃, short, nativeObservation, DomainAdapter.readbackOutcome, Executable.observation]
                  have initialLive : LiveCarried initialValues state.live := by
                    simp only [LiveCarried]
                    split
                    · rename_i position positionEq
                      have initialSorts : initialRefs.map (scope.reading.sorts[·]?) = (slots.map NativeSlot.sort).map some := by
                        have := congrArg (List.map (Option.map NativeSlot.sort)) carriedChecked
                        simpa [List.map_map, Function.comp_def, NativeScope.reading, List.getElem?_map] using this
                      obtain ⟨suite, suiteFound⟩ := transcriptPosition_sort positionEq
                      obtain ⟨reference, referenceAt, referenceSort⟩ := position_read initialSorts suiteFound
                      have isCurrent := custody_at initialCustody (List.mem_of_getElem? referenceAt) referenceSort
                      rw [value_at initialScalarRead referenceAt, isCurrent]
                      exact reached.native.live
                    · exact reached.native.live
                  have start := iterate (List.range bound) initialValues initialNominal state.charge (by simpa [State.charge] using frames) initialErases initialHolds initialLive
                  simpa only [List.length_range, State.charge] using start
                · have short : ¬ state.used + 1 ≤ budget := by omega
                  simp [maxOk, tick, short, nativeObservation, DomainAdapter.readbackOutcome, Executable.observation]
              · simp [maxOk, nativeObservation, DomainAdapter.readbackOutcome, Executable.observation]
            · cases reading
          · cases reading
        · cases reading
        · cases reading
      · cases reading
    · cases reading
    · cases reading
    · cases reading
  | .yield _ :: _ :: _, names, scope, codes, plan, ending, rawFinal, final, reading, checked => by simp [readActions] at reading
  | .ret _ :: _ :: _, names, scope, codes, plan, ending, rawFinal, final, reading, checked => by simp [readActions] at reading
  | .unsupported _ :: _, names, scope, codes, plan, ending, rawFinal, final, reading, checked => by simp [readActions] at reading

end Zkc.Executable.DomainVM
