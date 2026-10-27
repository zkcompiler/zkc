module

public import Zkc.Executable.DomainNativeTranscriptSteps

@[expose] public section

/-! Generic transparent native operation soundness. Structural reader results
and the finite nominal check supply every leaf premise. The CPS obligation is
only at actual reached successors, for induction over the remaining body. -/
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source Zkc.Construction.Uniform
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m] [LawfulMonad m]

private theorem readReferences_bounds {A : Type} {env : List A} :
    ∀ {references : List Nat} {values : List A},
      references.mapM (env[·]?) = some values → ∀ reference ∈ references, reference < env.length
  | [], _, _ => by simp
  | reference :: references, values, found => by
    simp only [List.mapM_cons] at found
    cases first : env[reference]? with
    | none => simp [first] at found
    | some value =>
      cases others : references.mapM (env[·]?) with
      | none => simp [first, others] at found
      | some rest =>
        intro target member
        rcases List.mem_cons.mp member with rfl | member
        · exact (List.getElem?_eq_some_iff.mp first).1
        · exact readReferences_bounds others target member

theorem native_operation_metered
    (program : Structured.Program) (context : Context) (initial : History F G)
    (challenge : History F G → m F) (vocabulary : Vocabulary) (validator : Validator)
    (budget : Nat) (cost : String → List (Value F G) → Nat)
    (call : String × String) (site binding : String) (parameters : List Parameter)
    (inputs outputs : List String) (resolvedOperation : Resolved)
    (resolved : validator.binding? binding >>= (vocabulary.resolve · parameters) = some resolvedOperation)
    (scope final : NativeScope) (operation : Operation) (references : List Nat)
    (declared : List ValueSort) (advances : Bool)
    (reading : readOperation scope.reading.sorts scope.current site resolvedOperation references =
      .ok (operation, declared, advances))
    (checked : checkNativeItem program context (.step ⟨operation, references, declared, []⟩ 1) scope = some final)
    (outputCount : outputs.length = declared.length)
    (data scalar : List (Value F G)) (state : State F G) (named : Env F G) (env : Environment F G)
    (reached : Reached context.suite Origin.withoutCoordinates initial data scope.reading state env scalar)
    (holds : scope.Holds env)
    (lookups : lookupAll named inputs = Construction.read scalar references)
    (proof : Proof F G) (next : Env F G → State F G → m (Run F G))
    (exit : List (Value F G) → State F G → m (Run F G))
    (continuation : Environment F G → Proof F G → Nat → m (PIR.Outcome (Environment F G) × Proof F G))
    (continues : ∀ values nominal nextState,
      values.length = declared.length →
      Reached context.suite Origin.withoutCoordinates initial data final.reading nextState nominal (scalar ++ values) →
      final.Holds nominal → nextState.used = state.used + 1 →
      nextState.frames = state.frames → nextState.proof = state.proof →
      Run.observe <$> next (outputs.zip values ++ named) nextState =
        nativeObservation context.suite Origin.withoutCoordinates initial <$>
          continuation nominal proof (state.used + 1)) :
    Run.observe <$> Executable.localStep vocabulary validator context challenge budget call true none
      (.operation site binding parameters inputs outputs) named state next exit =
      nativeObservation context.suite Origin.withoutCoordinates initial <$>
        meteredStep program context Origin.withoutCoordinates initial challenge cost budget
          (.step ⟨operation, references, declared, []⟩ 1) env proof state.used continuation := by
  obtain ⟨slots, moves, resultCheck, declaredEq, finalEq⟩ :=
    checkNativeStep_results program context scope final operation references declared 1 checked
  cases resolvedOperation with
  | indicesEmpty =>
    cases references with
    | cons => simp [readOperation] at reading
    | nil =>
      cases reading
      cases resultCheck
      subst final
      have args : lookupAll named inputs = some [] := lookups
      -- A native empty-coordinate operation reads no names; its source list
      -- is empty by the successful named reader at the caller.
      simp only [Executable.localStep, meteredStep]
      by_cases tick : state.used < budget
      · have fits : state.used + 1 ≤ budget := by omega
        simp only [tick, fits, ite_true, resolved, args, Resolved.apply, pure_bind,
          outputCount, List.length_singleton, Nat.add_zero]
        rw [Domain.Correspondence.indicesEmpty]
        simp only [Domain.View.indicesEmpty, Domain.View.append, Domain.sortsMatch, List.map_cons,
          Domain.Value.sort, List.map_nil, beq_self_eq_true, ite_true, DomainAdapter.runK]
        change Run.observe <$> next (outputs.zip [.indices []] ++ named) state.charge = _
        apply continues [.indices []] (env ++ [Domain.Value.indices []]) state.charge rfl
        · exact reached.keep rfl (.cons (show NativeSlot.Holds (.indices 0) (Domain.Value.indices []) from ⟨[], rfl, rfl⟩) .nil) rfl
        · exact holds.append (.cons (show NativeSlot.Holds (.indices 0) (Domain.Value.indices []) from ⟨[], rfl, rfl⟩) .nil)
        all_goals rfl
      · have short : ¬ state.used + 1 ≤ budget := by omega
        simp [tick, short, nativeObservation, DomainAdapter.readbackOutcome, Executable.observation]
  | indicesAppend =>
    rcases references with _ | ⟨coordinates, _ | ⟨index, _ | ⟨extra, more⟩⟩⟩
    all_goals try (simp [readOperation] at reading; done)
    simp only [readOperation] at reading
    split at reading
    · cases reading
      simp only [nativeResults] at resultCheck
      split at resultCheck
      · rename_i depth pathSort indexSort
        cases resultCheck
        subst final
        obtain ⟨path, pathFound, pathLength⟩ := holds.coordinates pathSort
        obtain ⟨value, indexFound⟩ := holds.index indexSort
        have pathScalar : scalar[coordinates]? = some (.indices path) := by rw [reached.erases.get, pathFound]; rfl
        have indexScalar : scalar[index]? = some (.index value) := by rw [reached.erases.get, indexFound]; rfl
        have args : lookupAll named inputs = some [.indices path, .index value] := by
          simpa [Construction.read, pathScalar, indexScalar] using lookups
        apply native_indicesAppend_metered program context Origin.withoutCoordinates initial challenge vocabulary validator
          budget cost call site binding parameters inputs outputs resolved (by simpa using outputCount)
          named state env coordinates index path value pathFound indexFound args proof next exit continuation
        apply continues [.indices (path ++ [value])] (env ++ [Domain.Value.indices (path ++ [value])]) state.charge rfl
        · exact reached.keep rfl (.cons (show NativeSlot.Holds (.indices (depth + 1)) (Domain.Value.indices (path ++ [value])) from ⟨_, rfl, by simp [pathLength]⟩) .nil) rfl
        · exact holds.append (.cons (show NativeSlot.Holds (.indices (depth + 1)) (Domain.Value.indices (path ++ [value])) from ⟨_, rfl, by simp [pathLength]⟩) .nil)
        all_goals rfl
      · cases resultCheck
    · cases reading
  | calculate calculation =>
    simp only [readOperation] at reading
    split at reading
    · cases reading
      simp only [nativeResults] at resultCheck
      split at resultCheck
      · rename_i facts
        obtain ⟨operandsChecked, _, eligible⟩ := facts
        cases resultCheck
        subst final
        have checkedSlots : references.map (scope.slots[·]?) =
            (calculation.op.arguments.map NativeSlot.data).map some := by
          simpa only [List.map_map] using operandsChecked
        obtain ⟨selected, selectedRead, _⟩ := holds.read checkedSlots
        have bounds := readReferences_bounds selectedRead
        obtain ⟨values, scalarRead⟩ := mapM_getElem?_some scalar (by
          intro reference member
          have := bounds reference member
          rw [reached.erases.length] at this
          exact this)
        obtain ⟨nominal, nominalRead, embedded⟩ := holds.readData reached.erases operandsChecked scalarRead
        have args : lookupAll named inputs = some values := lookups.trans scalarRead
        apply native_calculate_metered program context Origin.withoutCoordinates initial challenge vocabulary validator
          budget cost call site binding parameters inputs outputs calculation resolved eligible named state values args
          (by simpa using outputCount) env nominal references nominalRead embedded proof next exit continuation
        intro results values computed resultEmbedding schema
        have outputHolds : List.Forall₂ NativeSlot.Holds (calculation.op.results.map NativeSlot.data) values :=
          nativeHolds_of_schema (by simp [NativeSlot.rigid]) (by simpa [List.map_map, Function.comp_def, NativeSlot.sort] using schema)
        apply continues results (env ++ values) _ (by simpa using Uniform.calculate_length calculation computed)
        · exact reached.keep (embedValues_erases _ _ _ resultEmbedding) outputHolds rfl
        · exact holds.append outputHolds
        all_goals rfl
      · cases resultCheck
    · cases reading
  | observe suite ty template =>
    rcases references with _ | ⟨stateRef, _ | ⟨valueRef, _ | ⟨coordinates, _ | ⟨extra, more⟩⟩⟩⟩
    all_goals try (simp [readOperation] at reading; done)
    simp only [readOperation] at reading
    split at reading
    · rename_i facts
      obtain ⟨_, _, leafSort, _⟩ := facts
      cases reading
      have shape : slots = [.transcript suite] ∧ moves = true := by
        simp only [nativeResults] at resultCheck
        split at resultCheck
        · split at resultCheck
          · cases resultCheck; exact ⟨rfl, rfl⟩
          · cases resultCheck
        · cases resultCheck
      obtain ⟨rfl, rfl⟩ := shape
      subst final
      apply native_observe_metered program context initial challenge vocabulary validator budget cost call site binding parameters
        inputs outputs suite ty template resolved scope stateRef valueRef coordinates resultCheck leafSort
        (by simpa using outputCount) data scalar state named env reached holds lookups proof next exit continuation
      intro live nominal newReached newHolds
      apply continues [.transcript live] nominal _ rfl newReached newHolds
      all_goals rfl
    · cases reading
  | challenge suite field template =>
    rcases references with _ | ⟨stateRef, _ | ⟨coordinates, _ | ⟨extra, more⟩⟩⟩
    all_goals try (simp [readOperation] at reading; done)
    simp only [readOperation] at reading
    split at reading
    · cases reading
      have shape : slots = [.data (.field field), .transcript suite] ∧ moves = true := by
        simp only [nativeResults] at resultCheck
        split at resultCheck
        · split at resultCheck
          · cases resultCheck; exact ⟨rfl, rfl⟩
          · cases resultCheck
        · cases resultCheck
      obtain ⟨rfl, rfl⟩ := shape
      subst final
      apply native_challenge_metered program context initial challenge vocabulary validator budget cost call site binding parameters
        inputs outputs suite field template resolved scope stateRef coordinates resultCheck
        (by simpa using outputCount) data scalar state named env reached holds lookups proof next exit continuation
      intro answer live nominal newReached newHolds
      apply continues [.data (.field field answer), .transcript live] nominal _ rfl newReached newHolds
      all_goals rfl
    · cases reading
  | compute => simp [readOperation] at reading

end Zkc.Executable.DomainVM
