module

public import Zkc.Executable.DomainNativeCodeScope

@[expose] public section

/-! Checked occurrence metadata is unpacked once at the native boundary. -/
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source Zkc.Construction.Uniform

theorem nativeTemplate_facts (context : Context) (depth : Nat) (template : Template)
    (checked : nativeTemplate context depth template = true) :
    template.entry = context.entry ∧ template.repeats = depth ∧
      template.steps.all (fun step => step.kind == "apply" || step.kind == "repeat") = true := by
  simpa only [nativeTemplate, Bool.and_eq_true, beq_iff_eq, and_assoc] using checked

theorem nativeMessageEvent_facts (event : List String) (checked : nativeMessageEvent event = true) :
    ∃ localEntry site sender receiver,
      event = ["message", localEntry, site, site, sender, receiver] := by
  unfold nativeMessageEvent at checked
  split at checked
  · rename_i original localEntry site schema sender receiver
    have same : site = schema := by simpa using checked
    subst schema
    exact ⟨localEntry, site, sender, receiver, rfl⟩
  · cases checked

theorem nativeQueryEvent_facts (event : List String) (checked : nativeQueryEvent event = true) :
    ∃ localEntry site port contract owner,
      event = ["query", localEntry, site, port, contract, "draw", owner] := by
  unfold nativeQueryEvent at checked
  split at checked
  · exact ⟨_, _, _, _, _, rfl⟩
  · cases checked

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m] [LawfulMonad m]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Every payload admitted by the native message ABI is the exact nominal
Boolean/field/group payload, with its nominal domain retained. -/
theorem scalarPayload_of_sort (value : Domain.Value (Structured.uniformCarriers F G))
    (ty : Structured.Ty) (sorted : value.sort = .data ty)
    (eligible : (scalarType ty).isSome = true) :
    ∃ payload : Payload F G, value = .data (DomainAdapter.embedPayload payload) ∧ payloadType payload = ty := by
  cases value with
  | transcript | indices => cases sorted
  | data payload =>
    rcases payload with ⟨actual, supported, contents⟩
    simp only [Domain.Value.sort, ValueSort.data.injEq] at sorted
    subst ty
    cases actual with
    | boolean => exact ⟨.boolean contents, rfl, rfl⟩
    | field domain => exact ⟨.field domain contents, rfl, rfl⟩
    | group domain => exact ⟨.group domain contents, rfl, rfl⟩
    | _ => cases eligible

omit [LawfulMonad m] in
/-- Structural message metadata, current transcript custody and coordinate
depth are all obtained from the finite check and actual reached state. -/
theorem checked_observe {R : Type} (program : Structured.Program) (context : Context)
    (initial : History F G) (challenge : History F G → m F)
    (scope : NativeScope) (suite : String) (template : Template) (state value coordinates : Nat)
    (results : List NativeSlot) (advances : Bool)
    (checked : nativeResults program context scope (.observe suite template)
      [state, value, coordinates] = some (results, advances))
    (env : Environment F G) (holds : scope.Holds env)
    (data scalar : List (Value F G)) (native : State F G)
    (reached : Reached context.suite Origin.withoutCoordinates initial data scope.reading native env scalar)
    (proof : Proof F G) (next : Environment F G → Proof F G → m (PIR.Outcome R × Proof F G)) :
    ∃ history suffix path payload localEntry site sender receiver,
      suite = context.suite ∧ results = [.transcript suite] ∧ advances = true ∧
      native.live = initial ++ suffix ∧
      DomainAdapter.readbackHistory Origin.withoutCoordinates history = some suffix ∧
      scalar[state]? = some (.transcript native.live) ∧
      scalar[value]? = some (.data payload) ∧ scalar[coordinates]? = some (.indices path) ∧
      DomainAdapter.runK Origin.withoutCoordinates initial challenge
        (Domain.step (Structured.ringModel F G) program context
          ⟨.observe suite template, [state, value, coordinates], [.transcript suite], []⟩ env) proof next =
        next (env ++ [.transcript suite (history ++ [.message
          (Domain.atCoordinates (Origin.message context.entry (template.qualify site) sender receiver) path)
          (DomainAdapter.embedPayload payload)])]) proof ∧
      Resolved.apply context challenge native.live (.observe suite (payloadType payload) template)
        [.transcript native.live, .data payload, .indices path] =
        pure (.returned ([.transcript (native.live ++ [.message
          (Origin.message context.entry (template.qualify site) sender receiver) payload])],
          native.live ++ [.message (Origin.message context.entry (template.qualify site) sender receiver) payload], 1)) ∧
      template.event = ["message", localEntry, site, site, sender, receiver] := by
  simp only [nativeResults] at checked
  split at checked
  · rename_i actual ty depth stateSort valueSort coordinatesSort
    split at checked
    · rename_i facts
      obtain ⟨current, suiteActual, suiteEq, eligible, templ, event⟩ := facts
      cases checked
      obtain ⟨entry, repeats, kinds⟩ := nativeTemplate_facts context depth template templ
      obtain ⟨localEntry, site, sender, receiver, eventEq⟩ := nativeMessageEvent_facts template.event event
      obtain ⟨path, pathFound, pathLength⟩ := holds.coordinates coordinatesSort
      obtain ⟨observed, valueFound, sorted⟩ := holds.get valueSort
      obtain ⟨payload, rfl, payloadTy⟩ := scalarPayload_of_sort observed ty sorted eligible
      obtain ⟨history, suffix, liveFound, mapped, liveEq⟩ := reached.live
      refine ⟨history, suffix, path, payload, localEntry, site, sender, receiver,
        suiteEq, rfl, rfl, liveEq, mapped, ?_, ?_, ?_, ?_, ?_, eventEq⟩
      · simpa [NativeScope.reading, current] using reached.native.live
      · rw [reached.erases.get, valueFound]
        cases payload <;> rfl
      · rw [reached.erases.get, pathFound]
        rfl
      · subst suite
        rw [suiteEq]
        apply step_observe_native program context initial challenge template state value coordinates env
          history path payload localEntry site sender receiver proof next
        · simpa [NativeScope.reading, current] using liveFound
        · exact valueFound
        · exact pathFound
        · exact entry
        · exact repeats.trans pathLength.symm
        · exact kinds
        · exact eventEq
      · exact resolved_observe_native context challenge native.live suite template path payload
          localEntry site sender receiver eventEq
    · cases checked
  · cases checked

/-- The checked depth is the length of the actual reached nominal path.
The key map is applied before the arbitrary scalar oracle is invoked. -/
theorem checked_challenge {R : Type} (program : Structured.Program) (context : Context)
    (initial : History F G) (challenge : History F G → m F)
    (scope : NativeScope) (suite field : String) (template : Template) (state coordinates : Nat)
    (results : List NativeSlot) (advances : Bool)
    (checked : nativeResults program context scope (.challenge suite field template)
      [state, coordinates] = some (results, advances))
    (env : Environment F G) (holds : scope.Holds env)
    (data scalar : List (Value F G)) (native : State F G)
    (reached : Reached context.suite Origin.withoutCoordinates initial data scope.reading native env scalar)
    (proof : Proof F G) (next : Environment F G → Proof F G → m (PIR.Outcome R × Proof F G)) :
    ∃ history suffix path localEntry site port contract owner,
      suite = context.suite ∧ results = [.data (.field field), .transcript suite] ∧ advances = true ∧
      native.live = initial ++ suffix ∧
      DomainAdapter.readbackHistory Origin.withoutCoordinates history = some suffix ∧
      context.request = some (.draw field) ∧
      scalar[state]? = some (.transcript native.live) ∧ scalar[coordinates]? = some (.indices path) ∧
      DomainAdapter.runK Origin.withoutCoordinates initial challenge
        (Domain.step (Structured.ringModel F G) program context
          ⟨.challenge suite field template, [state, coordinates],
            [.data (.field field), .transcript suite], []⟩ env) proof next = (do
        let answer ← challenge (initial ++ suffix ++ [.challenge (context.query (template.qualify site) (.draw field))])
        next (env ++ [.data (.field field answer), .transcript suite
          (history ++ [.challenge (Domain.atCoordinates (context.query (template.qualify site) (.draw field)) path)])]) proof) ∧
      template.event = ["query", localEntry, site, port, contract, "draw", owner] := by
  simp only [nativeResults] at checked
  split at checked
  · rename_i actual depth stateSort coordinatesSort
    split at checked
    · rename_i facts
      obtain ⟨current, actualEq, suiteEq, contractEq, requestEq, templ, event⟩ := facts
      cases checked
      obtain ⟨entry, repeats, kinds⟩ := nativeTemplate_facts context depth template templ
      obtain ⟨localEntry, site, port, contract, owner, eventEq⟩ := nativeQueryEvent_facts template.event event
      obtain ⟨path, pathFound, pathLength⟩ := holds.coordinates coordinatesSort
      obtain ⟨history, suffix, liveFound, mapped, liveEq⟩ := reached.live
      refine ⟨history, suffix, path, localEntry, site, port, contract, owner, suiteEq, rfl, rfl, liveEq,
        mapped, requestEq, ?_, ?_, ?_, eventEq⟩
      · simpa [NativeScope.reading, current] using reached.native.live
      · rw [reached.erases.get, pathFound]
        rfl
      · apply step_challenge_native program context initial challenge suite field template state coordinates env
          history path localEntry site port contract owner suffix proof next
        · simpa [NativeScope.reading, current, suiteEq] using liveFound
        · exact pathFound
        · exact entry
        · exact repeats.trans pathLength.symm
        · exact kinds
        · exact suiteEq
        · exact contractEq
        · exact requestEq
        · exact eventEq
        · exact mapped
    · cases checked
  · cases checked

end Zkc.Executable.DomainVM
