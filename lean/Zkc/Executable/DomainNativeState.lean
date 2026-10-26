module

public import Zkc.Executable.DomainNativeScope

@[expose] public section

/-! Preservation rules for the native/nominal reached-state invariant. -/
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source Zkc.Construction.Uniform
variable {F G : Type}

theorem Erases.append {suite : String} {key : Origin → Origin} {initial : History F G}
    {first second : Environment F G} {one two : List (Value F G)}
    (left : Erases suite key initial first one) (right : Erases suite key initial second two) :
    Erases suite key initial (first ++ second) (one ++ two) := by
  simp only [Erases, DomainAdapter.readbackValues, List.mapM_append] at left right ⊢
  simp [left, right]

theorem Erases.length {suite : String} {key : Origin → Origin} {initial : History F G}
    {nominal : Environment F G} {scalar : List (Value F G)}
    (erases : Erases suite key initial nominal scalar) : nominal.length = scalar.length :=
  length_of_mapM_some erases

theorem readbackValue_sorted (suite : String) (key : Origin → Origin) (initial : History F G)
    (nominal : Domain.Value (Structured.uniformCarriers F G)) (scalar : Value F G)
    (found : DomainAdapter.readbackValue suite key initial nominal = some scalar) :
    HasSort scalar nominal.sort := by
  cases nominal with
  | indices path => cases found; trivial
  | transcript actual history =>
      simp only [DomainAdapter.readbackValue] at found
      split at found
      · cases mapped : DomainAdapter.readbackHistory key history with
        | none => simp [mapped] at found
        | some suffix => simp only [mapped, Option.map_some, Option.some.injEq] at found; subst scalar; trivial
      · cases found
  | data payload =>
      rcases payload with ⟨ty, supported, contents⟩
      cases ty <;> simp only [DomainAdapter.readbackValue, DomainAdapter.readbackData] at found
      all_goals first
        | cases found
          exact ⟨_, rfl⟩
        | cases found

theorem Erases.sorted {suite : String} {key : Origin → Origin} {initial : History F G}
    {nominal : Environment F G} {scalar : List (Value F G)}
    (erases : Erases suite key initial nominal scalar)
    {sorts : List ValueSort} (schema : nominal.map Domain.Value.sort = sorts) :
    ∀ (index : Nat) (value : Value F G) (sort : ValueSort), scalar[index]? = some value →
      sorts[index]? = some sort → HasSort value sort := by
  intro index value sort found sorted
  have projected := (erases.get index).symm.trans found
  cases looked : nominal[index]? with
  | none => simp [looked] at projected
  | some nominalValue =>
      simp only [looked, Option.bind_some] at projected
      have actual : nominalValue.sort = sort := by
        rw [← schema, List.getElem?_map, looked, Option.map_some, Option.some.injEq] at sorted
        exact sorted
      rw [← actual]
      exact readbackValue_sorted suite key initial nominalValue value projected

theorem NativeScope.Holds.length {scope : NativeScope} {env : Environment F G}
    (holds : scope.Holds env) : scope.slots.length = env.length := by
  simpa using (congrArg List.length holds.schema).symm

/-- Reading a coordinate slot derives its depth from checked nominal data. -/
theorem NativeScope.Holds.coordinates {scope : NativeScope} {env : Environment F G}
    (holds : scope.Holds env) {reference depth : Nat}
    (found : scope.slots[reference]? = some (.indices depth)) :
    ∃ path, env[reference]? = some (.indices path) ∧ path.length = depth := by
  obtain ⟨value, looked, path, rfl, length⟩ := holds.get found
  exact ⟨path, looked, length⟩

theorem NativeScope.Holds.append {scope : NativeScope} {env : Environment F G}
    (holds : scope.Holds env) {slots : List NativeSlot} {values : Environment F G}
    (more : List.Forall₂ NativeSlot.Holds slots values) (advances : Bool := false) :
    (scope.append slots advances).Holds (env ++ values) := by
  change List.Forall₂ NativeSlot.Holds (scope.slots ++ slots) (env ++ values)
  unfold NativeScope.Holds at holds
  generalize scope.slots = first at holds ⊢
  induction holds with
  | nil => exact more
  | cons head tail ih => exact .cons head ih

/-- Erasure and checked nominal result sorts establish the complete native
sort invariant, independently of any numerical input relationship. -/
theorem Reached.write {suite : String} {key : Origin → Origin} {initial : History F G}
    {data scalar : List (Value F G)} {scope : NativeScope} {state next : State F G}
    {env values : Environment F G} {results : List (Value F G)}
    (reached : Reached suite key initial data scope.reading state env scalar)
    {slots : List NativeSlot} (advances : Bool)
    (erases : Erases suite key initial values results)
    (holds : List.Forall₂ NativeSlot.Holds slots values)
    (live : (scalar ++ results)[(scope.append slots advances).current]? = some (.transcript next.live)) :
    Reached suite key initial data (scope.append slots advances).reading next
      (env ++ values) (scalar ++ results) := by
  have schema : values.map Domain.Value.sort = slots.map NativeSlot.sort :=
    NativeScope.Holds.schema (scope := ⟨slots, 0⟩) holds
  refine ⟨reached.erases.append erases, ?_, ?_⟩
  · simpa [NativeScope.reading, NativeScope.append, List.map_append] using
      reached.native.extend (by rw [← erases.length]; simpa using congrArg List.length schema) (erases.sorted schema) live
  · simp [NativeScope.reading, NativeScope.append, List.map_append, reached.schema, schema]

end Zkc.Executable.DomainVM
