module

public import Zkc.Construction.Scalar

@[expose] public section

/-! Elementary scalar ABI tuple, lookup and extension laws. No constructed
instruction interpretation or construction checker is imported here. -/
set_option autoImplicit false
namespace Zkc.Construction.Uniform
open Zkc.Source
variable {F G : Type}

section Environment
variable {env : List (Value F G)}

theorem getElem?_append_left' {values : List (Value F G)} {index : Nat}
    (bound : index < env.length) : (env ++ values)[index]? = env[index]? :=
  List.getElem?_append_left bound

theorem lt_of_getElem?_eq_some {index : Nat} {value : Value F G}
    (found : env[index]? = some value) : index < env.length := by
  by_contra outside
  rw [List.getElem?_eq_none (by omega)] at found
  cases found

theorem transcriptAt_append {values : List (Value F G)} {index : Nat} {history : History F G}
    (found : transcriptAt env index = some history) :
    transcriptAt (env ++ values) index = some history := by
  unfold transcriptAt at found ⊢
  split at found
  · rename_i found'
    rw [getElem?_append_left' (lt_of_getElem?_eq_some found'), found']
    exact found
  · cases found

theorem dataAt_append {values : List (Value F G)} {index : Nat} {payload : Payload F G}
    (found : dataAt env index = some payload) :
    dataAt (env ++ values) index = some payload := by
  unfold dataAt at found ⊢
  split at found
  · rename_i found'
    rw [getElem?_append_left' (lt_of_getElem?_eq_some found'), found']
    exact found
  · cases found

theorem transcriptAt_last (history : History F G) (values : List (Value F G)) :
    transcriptAt (env ++ .transcript history :: values) env.length = some history := by
  simp [transcriptAt]

theorem dataAt_last (payload : Payload F G) (values : List (Value F G)) :
    dataAt (env ++ .data payload :: values) env.length = some payload := by
  simp [dataAt]

end Environment

theorem read_length {env values : List (Value F G)} {references : List Nat}
    (found : read env references = some values) : values.length = references.length := by
  induction references generalizing values with
  | nil => simp [read] at found; simp [← found]
  | cons reference rest ih =>
    simp only [read, List.mapM_cons, Option.bind_eq_bind] at found
    cases first : env[reference]? with
    | none => simp [first] at found
    | some value =>
      cases others : rest.mapM (env[·]?) with
      | none => simp [first, others] at found
      | some tail =>
        simp [first, others] at found
        subst found
        simp [ih (show read env rest = some tail from others)]

theorem read_getElem? {env values : List (Value F G)} {references : List Nat}
    (found : read env references = some values) (index : Nat) :
    values[index]? = references[index]?.bind (env[·]?) := by
  induction references generalizing values index with
  | nil => simp [read] at found; subst found; simp
  | cons reference rest ih =>
    simp only [read, List.mapM_cons, Option.bind_eq_bind] at found
    cases first : env[reference]? with
    | none => simp [first] at found
    | some value =>
      cases others : rest.mapM (env[·]?) with
      | none => simp [first, others] at found
      | some tail =>
        simp [first, others] at found
        subst found
        cases index with
        | zero => simp [first]
        | succ index => simpa using ih (show read env rest = some tail from others) index

theorem read_some {env : List (Value F G)} {references : List Nat}
    (bounded : ∀ reference ∈ references, reference < env.length) :
    ∃ values, read env references = some values := by
  induction references with
  | nil => exact ⟨[], rfl⟩
  | cons reference rest ih =>
    obtain ⟨tail, found⟩ := ih (fun other member => bounded other (List.mem_cons_of_mem _ member))
    have bound := bounded reference List.mem_cons_self
    refine ⟨env[reference] :: tail, ?_⟩
    simp only [read, List.mapM_cons, Option.bind_eq_bind, List.getElem?_eq_getElem bound]
    simp only [read] at found
    simp [found]

/-- References with known sorts are within a synchronized environment. -/
theorem bounded_of_sorts {sorts : List ValueSort} {env : List (Value F G)}
    (length : env.length = sorts.length) {references : List Nat} {expected : List ValueSort}
    (typed : references.map (sorts[·]?) = expected.map some) :
    ∀ reference ∈ references, reference < env.length := by
  intro reference member
  have := List.mem_map_of_mem (f := (sorts[·]?)) member
  rw [typed] at this
  obtain ⟨sort, _, found⟩ := List.mem_map.mp this
  rw [length]
  by_contra outside
  rw [List.getElem?_eq_none (by omega)] at found
  cases found

theorem transcriptAt_block {env carried : List (Value F G)} (index position : Nat) :
    transcriptAt (env ++ .index index :: carried) (env.length + 1 + position) =
      transcriptAt carried position := by
  unfold transcriptAt
  rw [List.getElem?_append_right (by omega)]
  simp [show env.length + 1 + position - env.length = position + 1 by omega]

theorem transcriptAt_suffix {env carried : List (Value F G)} (position : Nat) :
    transcriptAt (env ++ carried) (env.length + position) = transcriptAt carried position := by
  unfold transcriptAt
  rw [List.getElem?_append_right (by omega)]
  simp

theorem encodeValues_length {tys : List Structured.Ty}
    (values : Values (Structured.assignment F G) tys) : (encodeValues values).length = tys.length := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp [encodeValues, ih]

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

theorem calculate_length (calculation : Calculation) {arguments results : List (Value F G)}
    (computed : Zkc.Construction.calculate calculation arguments = .returned results) :
    results.length = calculation.op.results.length := by
  unfold Zkc.Construction.calculate at computed
  split at computed
  · cases computed
  · split at computed
    · cases computed
      exact encodeValues_length _
    · cases computed


end Zkc.Construction.Uniform
