module

public import Zkc.Executable.DomainNativeData
public import Zkc.Executable.DomainProcesses
public import Zkc.Executable.DomainLowering

@[expose] public section

/-! Interpretation of the finite nominal scope certificate. These are
all-reply invariants of actual Domain steps, not assumptions about execution. -/
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source Zkc.Construction.Uniform
variable {F G : Type}

def NativeSlot.rigid : NativeSlot → Bool
  | .indices _ => false
  | _ => true

theorem NativeSlot.Holds.of_sort {slot : NativeSlot} {value : Domain.Value (Structured.uniformCarriers F G)}
    (rigid : slot.rigid = true) (sorted : value.sort = slot.sort) : slot.Holds value := by
  cases slot with
  | data | transcript => exact sorted
  | indices => cases rigid

theorem nativeHolds_of_schema :
    ∀ {slots : List NativeSlot} {values : Environment F G},
      slots.all NativeSlot.rigid = true →
      values.map Domain.Value.sort = slots.map NativeSlot.sort →
      List.Forall₂ NativeSlot.Holds slots values
  | [], [], _, _ => .nil
  | [], _ :: _, _, sorted => by simp at sorted
  | _ :: _, [], _, sorted => by simp at sorted
  | slot :: slots, value :: values, rigid, sorted => by
      simp only [List.all_cons, Bool.and_eq_true] at rigid
      simp only [List.map_cons, List.cons.injEq] at sorted
      exact .cons (NativeSlot.Holds.of_sort rigid.1 sorted.1) (nativeHolds_of_schema rigid.2 sorted.2)

theorem nativeResults_rigid (program : Structured.Program) (context : Context) (scope : NativeScope)
    (operation : Operation) (operands : List Nat) (results : List NativeSlot) (advances : Bool)
    (checked : nativeResults program context scope operation operands = some (results, advances))
    (notEmpty : operation ≠ .indicesEmpty) (notAppend : operation ≠ .indicesAppend) :
    results.all NativeSlot.rigid = true := by
  cases operation <;> unfold nativeResults at checked
  all_goals repeat' first
    | split at checked
    | (cases checked; simp [NativeSlot.rigid])
    | contradiction

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The operation checker implies scope preservation for every permitted
receive/query reply and every arithmetic input. Stopped paths need no successor. -/
theorem nativeResults_preserves (program : Structured.Program) (context : Context)
    (scope : NativeScope) (operation : Operation) (operands : List Nat)
    (results : List NativeSlot) (advances : Bool)
    (checked : nativeResults program context scope operation operands = some (results, advances))
    (env : Environment F G) (holds : scope.Holds env) :
    PIR.Yields (fun final => (scope.append results advances).Holds final)
      (Domain.step (Structured.ringModel F G) program context
        ⟨operation, operands, results.map NativeSlot.sort, []⟩ env) := by
  by_cases empty : operation = .indicesEmpty
  · subst operation
    cases operands with
    | nil =>
        cases checked
        simp only [Domain.step, Domain.sortsMatch, List.map_cons, NativeSlot.sort,
          Domain.Value.sort, List.map_nil, beq_self_eq_true, ite_true, PIR.Yields]
        exact holds.append (.cons (show NativeSlot.Holds (.indices 0) (.indices []) from ⟨[], rfl, rfl⟩) .nil)
    | cons => simp [nativeResults] at checked
  · by_cases append : operation = .indicesAppend
    · subst operation
      rcases operands with _ | ⟨coordinates, _ | ⟨index, _ | ⟨extra, rest⟩⟩⟩
      all_goals try (simp [nativeResults] at checked; done)
      simp only [nativeResults] at checked
      split at checked
      · rename_i depth coordinatesSort indexSort
        cases checked
        obtain ⟨path, pathFound, length⟩ := holds.coordinates coordinatesSort
        obtain ⟨value, indexFound, indexHolds⟩ := holds.get indexSort
        obtain ⟨decoded, decodedEq⟩ := decode_of_sort indexHolds
        cases value with
        | transcript | indices => cases indexHolds
        | data payload =>
          rcases payload with ⟨ty, supported, contents⟩
          simp only [NativeSlot.Holds, Domain.Value.sort, ValueSort.data.injEq] at indexHolds
          subst ty
          simp only [Domain.step, pathFound, indexFound, Domain.sortsMatch,
            List.map_cons, NativeSlot.sort, Domain.Value.sort, List.map_nil,
            beq_self_eq_true, ite_true, PIR.Yields]
          have next : NativeSlot.Holds (.indices (depth + 1))
              (.indices (path ++ [contents]) : Domain.Value (Structured.uniformCarriers F G)) :=
            ⟨path ++ [contents], rfl, by simp [length]⟩
          exact holds.append (.cons next .nil)
      · cases checked
    · have rigid := nativeResults_rigid program context scope operation operands results advances checked empty append
      exact (step_schema (Structured.ringModel F G) program context
        ⟨operation, operands, results.map NativeSlot.sort, []⟩ env).mono fun final found => by
          obtain ⟨values, rfl, sorted⟩ := found
          simp only [Domain.sortsMatch, beq_iff_eq] at sorted
          exact holds.append (nativeHolds_of_schema rigid sorted)

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Checked reference lists select actual nominal values with their complete
slot predicates, including coordinate depths and transcript suites. -/
theorem NativeScope.Holds.read {scope : NativeScope} {env : Environment F G}
    (holds : scope.Holds env) :
    ∀ {references : List Nat} {slots : List NativeSlot},
      references.map (scope.slots[·]?) = slots.map some →
      ∃ values, Domain.read env references = some values ∧ List.Forall₂ NativeSlot.Holds slots values
  | [], [], _ => ⟨[], rfl, .nil⟩
  | [], _ :: _, found => by simp at found
  | _ :: _, [], found => by simp at found
  | reference :: references, slot :: slots, found => by
      simp only [List.map_cons, List.cons.injEq] at found
      obtain ⟨value, looked, head⟩ := holds.get found.1
      obtain ⟨values, read, tail⟩ := holds.read found.2
      exact ⟨value :: values, by simp [Domain.read, looked, show references.mapM (env[·]?) = some values from read],
        .cons head tail⟩

/-- Successful list traversal supplies the equivalent list of optional slots. -/
theorem mapM_optional {A B : Type} (lookup : A → Option B) :
    ∀ {references : List A} {values : List B}, references.mapM lookup = some values →
      references.map lookup = values.map some
  | [], values, found => by cases found; rfl
  | reference :: references, values, found => by
      simp only [List.mapM_cons] at found
      cases head : lookup reference with
      | none => simp [head] at found
      | some value =>
          cases tail : references.mapM lookup with
          | none => simp [head, tail] at found
          | some rest =>
              simp [head, tail] at found
              subst values
              simp only [List.map_cons, head, mapM_optional lookup tail]

/-- The nominal checker has no unchecked nonloop body case. -/
theorem checkNativeStep_preserves (program : Structured.Program) (context : Context)
    (scope final : NativeScope) (instruction : Instruction) (charged : Nat)
    (checked : checkNativeItem program context (.step instruction charged) scope = some final)
    (env : Environment F G) (holds : scope.Holds env) :
    PIR.Yields final.Holds (Domain.step (Structured.ringModel F G) program context instruction env) := by
  rcases instruction with ⟨operation, operands, declared, body⟩
  cases body with
  | cons => simp [checkNativeItem] at checked
  | nil =>
      simp only [checkNativeItem] at checked
      cases parsed : nativeResults program context scope operation operands with
      | none => simp [parsed] at checked
      | some pair =>
          rcases pair with ⟨results, advances⟩
          simp only [parsed, bind, Option.bind] at checked
          split at checked
          · rename_i declaredEq
            cases checked
            subst declared
            exact nativeResults_preserves program context scope operation operands results advances parsed env holds
          · cases checked

/-- Helper declaration and body-shape checking has the same all-reply scope
law as ordinary steps. Invocation is still the actual Domain helper call. -/
theorem checkNativeHelper_preserves (program : Structured.Program) (context : Context)
    (scope final : NativeScope) (instruction : Instruction)
    (checked : checkNativeItem program context (.helper instruction) scope = some final)
    (env : Environment F G) (holds : scope.Holds env) :
    PIR.Yields final.Holds (Domain.step (Structured.ringModel F G) program context instruction env) := by
  rcases instruction with ⟨operation, operands, declared, body⟩
  cases operation <;> cases body <;> try (simp [checkNativeItem] at checked; done)
  apply checkNativeStep_preserves program context scope final _ 1 (env := env) (holds := holds)
  simpa only [checkNativeItem] using checked

end Zkc.Executable.DomainVM
