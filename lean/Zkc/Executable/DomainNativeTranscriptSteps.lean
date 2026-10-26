module

public import Zkc.Executable.DomainNativeLocalOperations

@[expose] public section

/-! Checked native transcript operations with their reached-state successors.
Scalar oracle calls remain outside the result observation, so an eventual
false result retains every preceding query action. -/
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source Zkc.Construction.Uniform
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem native_observe_metered
    (program : Structured.Program) (context : Context) (initial : History F G)
    (challenge : History F G → m F) (vocabulary : Vocabulary) (validator : Validator)
    (budget : Nat) (cost : String → List (Value F G) → Nat)
    (call : String × String) (site binding : String) (parameters : List Parameter)
    (inputs outputs : List String) (suite : String) (ty : Structured.Ty) (template : Template)
    (resolved : validator.binding? binding >>= (vocabulary.resolve · parameters) = some (.observe suite ty template))
    (scope : NativeScope) (stateRef valueRef coordinatesRef : Nat)
    (checked : nativeResults program context scope (.observe suite template)
      [stateRef, valueRef, coordinatesRef] = some ([.transcript suite], true))
    (leafSort : scope.reading.sorts[valueRef]? = some (.data ty))
    (outputCount : outputs.length = 1)
    (data scalar : List (Value F G)) (state : State F G) (named : Env F G) (env : Environment F G)
    (reached : Reached context.suite Origin.withoutCoordinates initial data scope.reading state env scalar)
    (holds : scope.Holds env)
    (lookups : lookupAll named inputs = Construction.read scalar [stateRef, valueRef, coordinatesRef])
    (proof : Proof F G) (next : Env F G → State F G → m (Run F G))
    (exit : List (Value F G) → State F G → m (Run F G))
    (continuation : Environment F G → Proof F G → Nat → m (PIR.Outcome (Environment F G) × Proof F G))
    (continues : ∀ live final,
      Reached context.suite Origin.withoutCoordinates initial data
        (scope.append [.transcript suite] true).reading
        { state.charge with live := live, transitions := state.transitions + 1 }
        final (scalar ++ [.transcript live]) →
      (scope.append [.transcript suite] true).Holds final →
      Run.observe <$> next (outputs.zip [.transcript live] ++ named)
        { state.charge with live := live, transitions := state.transitions + 1 } =
      nativeObservation context.suite Origin.withoutCoordinates initial <$>
        continuation final proof (state.used + 1)) :
    Run.observe <$> Executable.localStep vocabulary validator context challenge budget call true none
      (.operation site binding parameters inputs outputs) named state next exit =
      nativeObservation context.suite Origin.withoutCoordinates initial <$>
        meteredStep program context Origin.withoutCoordinates initial challenge cost budget
          (.step ⟨.observe suite template, [stateRef, valueRef, coordinatesRef], [.transcript suite], []⟩ 1)
          env proof state.used continuation := by
  obtain ⟨history, suffix, path, payload, localEntry, messageSite, sender, receiver,
    suiteEq, _, _, liveEq, mapped, stateFound, valueFound, coordinatesFound, domainEq, nativeEq, event⟩ :=
      checked_observe program context initial challenge scope suite template stateRef valueRef coordinatesRef _ _ checked
        env holds data scalar state reached proof (fun final unread => continuation final unread (state.used + 1))
  have payloadTy : payloadType payload = ty :=
    sorted_payload (reached.native.sorted valueRef (.data payload) (.data ty) valueFound leafSort) rfl
  have argumentsFound : lookupAll named inputs = some [.transcript state.live, .data payload, .indices path] := by
    simpa [Construction.read, stateFound, valueFound, coordinatesFound] using lookups
  simp only [Executable.localStep, meteredStep]
  by_cases tick : state.used < budget
  · have fits : state.used + 1 ≤ budget := by omega
    simp only [tick, fits, ite_true, resolved, argumentsFound]
    rw [← payloadTy, nativeEq, pure_bind, domainEq]
    simp only [List.length_singleton, outputCount, ite_true]
    apply continues
    · have mappedNext := mapped_message history suffix
        (Origin.message context.entry (template.qualify messageSite) sender receiver) path payload rfl mapped
      have advanced := reached.advance (slots := []) (values := []) (results := []) rfl .nil
        (history ++ [.message
          (Domain.atCoordinates (Origin.message context.entry (template.qualify messageSite) sender receiver) path)
          (DomainAdapter.embedPayload payload)])
        (suffix ++ [.message (Origin.message context.entry (template.qualify messageSite) sender receiver) payload])
        mappedNext
        (next := { state.charge with
          live := state.live ++ [.message
            (Origin.message context.entry (template.qualify messageSite) sender receiver) payload]
          transitions := state.transitions + 1 })
        (by simp [liveEq, List.append_assoc])
      simpa [suiteEq] using advanced
    · exact holds.append
        (.cons (show NativeSlot.Holds (.transcript suite)
          (Domain.Value.transcript suite _) from rfl) .nil) true
  · have short : ¬ state.used + 1 ≤ budget := by omega
    simp [tick, short, nativeObservation, DomainAdapter.readbackOutcome, Executable.observation]

/-- The arbitrary scalar reply is quantified in the native continuation. The
same oracle action is made only after projecting the actual nominal key. -/
theorem native_challenge_metered
    (program : Structured.Program) (context : Context) (initial : History F G)
    (challenge : History F G → m F) (vocabulary : Vocabulary) (validator : Validator)
    (budget : Nat) (cost : String → List (Value F G) → Nat)
    (call : String × String) (site binding : String) (parameters : List Parameter)
    (inputs outputs : List String) (suite field : String) (template : Template)
    (resolved : validator.binding? binding >>= (vocabulary.resolve · parameters) = some (.challenge suite field template))
    (scope : NativeScope) (stateRef coordinatesRef : Nat)
    (checked : nativeResults program context scope (.challenge suite field template)
      [stateRef, coordinatesRef] = some ([.data (.field field), .transcript suite], true))
    (outputCount : outputs.length = 2)
    (data scalar : List (Value F G)) (state : State F G) (named : Env F G) (env : Environment F G)
    (reached : Reached context.suite Origin.withoutCoordinates initial data scope.reading state env scalar)
    (holds : scope.Holds env)
    (lookups : lookupAll named inputs = Construction.read scalar [stateRef, coordinatesRef])
    (proof : Proof F G) (next : Env F G → State F G → m (Run F G))
    (exit : List (Value F G) → State F G → m (Run F G))
    (continuation : Environment F G → Proof F G → Nat → m (PIR.Outcome (Environment F G) × Proof F G))
    (continues : ∀ answer live final,
      Reached context.suite Origin.withoutCoordinates initial data
        (scope.append [.data (.field field), .transcript suite] true).reading
        { state.charge with live := live, transitions := state.transitions + 1 }
        final (scalar ++ [.data (.field field answer), .transcript live]) →
      (scope.append [.data (.field field), .transcript suite] true).Holds final →
      Run.observe <$> next (outputs.zip [.data (.field field answer), .transcript live] ++ named)
        { state.charge with live := live, transitions := state.transitions + 1 } =
      nativeObservation context.suite Origin.withoutCoordinates initial <$>
        continuation final proof (state.used + 1)) :
    Run.observe <$> Executable.localStep vocabulary validator context challenge budget call true none
      (.operation site binding parameters inputs outputs) named state next exit =
      nativeObservation context.suite Origin.withoutCoordinates initial <$>
        meteredStep program context Origin.withoutCoordinates initial challenge cost budget
          (.step ⟨.challenge suite field template, [stateRef, coordinatesRef],
            [.data (.field field), .transcript suite], []⟩ 1) env proof state.used continuation := by
  obtain ⟨history, suffix, path, localEntry, querySite, port, contract, owner,
    suiteEq, _, _, liveEq, mapped, request, stateFound, coordinatesFound, domainEq, event⟩ :=
      checked_challenge program context initial challenge scope suite field template stateRef coordinatesRef _ _ checked
        env holds data scalar state reached proof (fun final unread => continuation final unread (state.used + 1))
  have argumentsFound : lookupAll named inputs = some [.transcript state.live, .indices path] := by
    simpa [Construction.read, stateFound, coordinatesFound] using lookups
  simp only [Executable.localStep, meteredStep]
  by_cases tick : state.used < budget
  · have fits : state.used + 1 ≤ budget := by omega
    simp only [tick, fits, ite_true, resolved, argumentsFound]
    rw [resolved_challenge_native context challenge state.live suite field template path
      localEntry querySite port contract owner request event, domainEq]
    simp only [bind_map_left, map_bind]
    rw [liveEq]
    congr 1
    funext answer
    simp only [List.length_cons, List.length_nil, outputCount, ite_true]
    apply continues
    · have mappedNext := mapped_challenge history suffix
        (context.query (template.qualify querySite) (.draw field)) path rfl mapped
      have advanced := reached.advance (slots := [.data (.field field)])
        (values := [.data (.field field answer)]) (results := [.data (.field field answer)])
        rfl (.cons (show NativeSlot.Holds (.data (.field field))
          (Domain.Value.data (.field field answer)) from rfl) .nil)
        (history ++ [.challenge (Domain.atCoordinates (context.query (template.qualify querySite) (.draw field)) path)])
        (suffix ++ [.challenge (context.query (template.qualify querySite) (.draw field))]) mappedNext
        (next := { state.charge with
          live := initial ++ suffix ++ [.challenge (context.query (template.qualify querySite) (.draw field))]
          transitions := state.transitions + 1 })
        (by simp [List.append_assoc])
      simpa [suiteEq] using advanced
    · exact holds.append
        (.cons (show NativeSlot.Holds (.data (.field field))
          (Domain.Value.data (.field field answer)) from rfl)
          (.cons (show NativeSlot.Holds (.transcript suite)
            (Domain.Value.transcript suite _) from rfl) .nil)) true
  · have short : ¬ state.used + 1 ≤ budget := by omega
    simp [tick, short, nativeObservation, DomainAdapter.readbackOutcome, Executable.observation]

end Zkc.Executable.DomainVM
