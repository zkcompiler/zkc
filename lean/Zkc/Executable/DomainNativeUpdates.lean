module

public import Zkc.Executable.DomainNativeOccurrences
public import Zkc.Executable.DomainNativeCalculations

@[expose] public section

/-! Reached-state rules used by native control-flow induction. Every scalar
output is the partial readback of actual nominal outputs. -/
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source Zkc.Construction.Uniform
variable {F G : Type}

theorem Reached.congr {suite : String} {key : Origin → Origin} {initial : History F G}
    {data scalar : List (Value F G)} {reading : Reading} {state next : State F G}
    {env : Environment F G}
    (reached : Reached suite key initial data reading state env scalar)
    (live : next.live = state.live) : Reached suite key initial data reading next env scalar :=
  ⟨reached.erases, reached.native.congr live, reached.schema⟩

theorem Reached.keep {suite : String} {key : Origin → Origin} {initial : History F G}
    {data scalar : List (Value F G)} {scope : NativeScope} {state next : State F G}
    {env values : Environment F G} {results : List (Value F G)}
    (reached : Reached suite key initial data scope.reading state env scalar)
    {slots : List NativeSlot}
    (erases : Erases suite key initial values results)
    (holds : List.Forall₂ NativeSlot.Holds slots values)
    (live : next.live = state.live) :
    Reached suite key initial data (scope.append slots false).reading next (env ++ values) (scalar ++ results) := by
  apply reached.write false erases holds
  change (scalar ++ results)[scope.current]? = some (.transcript next.live)
  rw [List.getElem?_append_left (show scope.current < scalar.length from reached.native.current_bound), live]
  exact reached.native.live

theorem Erases.transcript (suite : String) (key : Origin → Origin) (initial : History F G)
    (history : Domain.History (Structured.uniformCarriers F G)) (suffix : History F G)
    (mapped : DomainAdapter.readbackHistory key history = some suffix) :
    Erases suite key initial [.transcript suite history] [.transcript (initial ++ suffix)] := by
  simp [Erases, DomainAdapter.readbackValues, DomainAdapter.readbackValue, mapped]

/-- Advancing the transcript after arbitrary data results preserves actual
native custody at the new nominal reference. -/
theorem Reached.advance {suite : String} {key : Origin → Origin} {initial : History F G}
    {data scalar : List (Value F G)} {scope : NativeScope} {state next : State F G}
    {env values : Environment F G} {results : List (Value F G)}
    (reached : Reached suite key initial data scope.reading state env scalar)
    {slots : List NativeSlot}
    (erases : Erases suite key initial values results)
    (holds : List.Forall₂ NativeSlot.Holds slots values)
    (history : Domain.History (Structured.uniformCarriers F G)) (suffix : History F G)
    (mapped : DomainAdapter.readbackHistory key history = some suffix)
    (live : next.live = initial ++ suffix) :
    Reached suite key initial data (scope.append (slots ++ [.transcript suite]) true).reading next
      (env ++ (values ++ [.transcript suite history]))
      (scalar ++ (results ++ [.transcript next.live])) := by
  have restHolds : List.Forall₂ NativeSlot.Holds (slots ++ [.transcript suite])
      (values ++ [.transcript suite history]) :=
    NativeScope.Holds.append (scope := ⟨slots, 0⟩) holds
      (.cons (show NativeSlot.Holds (.transcript suite) (Domain.Value.transcript suite history) from rfl) .nil)
  have restErases : Erases suite key initial (values ++ [.transcript suite history])
      (results ++ [.transcript next.live]) := by
    rw [live]
    exact erases.append (Erases.transcript suite key initial history suffix mapped)
  apply reached.write true restErases restHolds
  have baseLength : scalar.length = scope.slots.length := by
    simpa only [NativeScope.reading, List.length_map] using reached.native.length
  have resultLength : results.length = slots.length := by
    have sorted := NativeScope.Holds.schema (scope := ⟨slots, 0⟩) holds
    have lengths := congrArg List.length sorted
    simp only [List.length_map] at lengths
    exact erases.length.symm.trans lengths
  change (scalar ++ (results ++ [.transcript next.live]))[
    scope.slots.length + (slots ++ [NativeSlot.transcript suite]).length - 1]? = _
  simp [List.length_append, ← baseLength, ← resultLength]

theorem checkNativeCode_cons (program : Structured.Program) (context : Context)
    (head : Code) (rest : List Code) (scope final : NativeScope)
    (checked : checkNativeCode program context (head :: rest) scope = some final) :
    ∃ middle, checkNativeItem program context head scope = some middle ∧
      checkNativeCode program context rest middle = some final := by
  change (checkNativeItem program context head scope).bind _ = some final at checked
  exact Option.bind_eq_some_iff.mp checked

theorem checkNativeStep_results (program : Structured.Program) (context : Context)
    (scope final : NativeScope) (operation : Operation) (operands : List Nat)
    (declared : List ValueSort) (charged : Nat)
    (checked : checkNativeItem program context (.step ⟨operation, operands, declared, []⟩ charged) scope = some final) :
    ∃ results advances, nativeResults program context scope operation operands = some (results, advances) ∧
      declared = results.map NativeSlot.sort ∧ final = scope.append results advances := by
  change (nativeResults program context scope operation operands).bind _ = some final at checked
  obtain ⟨⟨results, advances⟩, found, checked⟩ := Option.bind_eq_some_iff.mp checked
  change (if results.map NativeSlot.sort = declared then some (scope.append results advances) else none) = some final at checked
  by_cases same : results.map NativeSlot.sort = declared
  · simp only [same, ite_true, Option.some.injEq] at checked
    exact ⟨results, advances, found, same.symm, checked.symm⟩
  · simp [same] at checked

end Zkc.Executable.DomainVM
