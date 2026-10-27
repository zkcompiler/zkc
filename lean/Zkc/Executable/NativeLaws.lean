module

public import Zkc.Executable.Evaluation

@[expose] public section

/-! Native frame/scope, lookup, local evaluation and prepared-helper laws.
These laws are independent of constructed instruction execution. Prepared
helpers compare exact typed results and stop classes, and helperCost retains
the actual native evaluation cost on the supplied arguments. -/
set_option autoImplicit false
namespace Zkc.Executable
open Zkc.Construction Zkc.Source
variable {F G : Type}

section Invariant
variable {data : List (Value F G)} {R : Reading} {s : State F G} {env : List (Value F G)}

theorem Simulates.congr (sim : Simulates data R s env) {s' : State F G} (live : s'.live = s.live) :
    Simulates data R s' env where
  length := sim.length
  sorted := sim.sorted
  live := by rw [live]; exact sim.live
  inputs := sim.inputs

theorem Simulates.input_bound (sim : Simulates data R s env) {index : Nat} (lt : index < data.length) :
    index < env.length := by
  have := sim.inputs index lt
  rw [List.getElem?_eq_getElem lt] at this
  exact (List.getElem?_eq_some_iff.mp this).1

theorem Simulates.current_bound (sim : Simulates data R s env) : R.current < env.length :=
  (List.getElem?_eq_some_iff.mp sim.live).1

/-- Extend the environment by values of the given sorts. -/
theorem Simulates.extend (sim : Simulates data R s env) {values : List (Value F G)}
    {sorts : List ValueSort} (lengths : values.length = sorts.length)
    (sorted : ∀ (index : Nat) (value : Value F G) (sort : ValueSort), values[index]? = some value →
      sorts[index]? = some sort → HasSort value sort)
    {current : Nat} {s' : State F G} (live : (env ++ values)[current]? = some (.transcript s'.live)) :
    Simulates data ⟨R.sorts ++ sorts, current⟩ s' (env ++ values) where
  length := by simp [sim.length, lengths]
  sorted := sorted_extend sim.length sim.sorted sorted
  live := live
  inputs := by
    intro index lt
    rw [List.getElem?_append_left (sim.input_bound lt)]
    exact sim.inputs index lt

/-- Extend the environment, keeping the live transcript. -/
theorem Simulates.keep (sim : Simulates data R s env) {values : List (Value F G)}
    {sorts : List ValueSort} (lengths : values.length = sorts.length)
    (sorted : ∀ (index : Nat) (value : Value F G) (sort : ValueSort), values[index]? = some value →
      sorts[index]? = some sort → HasSort value sort)
    {s' : State F G} (live : s'.live = s.live) :
    Simulates data ⟨R.sorts ++ sorts, R.current⟩ s' (env ++ values) :=
  sim.extend lengths sorted (by rw [List.getElem?_append_left sim.current_bound, live]; exact sim.live)

theorem Simulates.indices (sim : Simulates data R s env) {index : Nat}
    (sortEq : R.sorts[index]? = some .indices) :
    ∃ coordinates, env[index]? = some (.indices coordinates) := by
  obtain ⟨value, found, sorted⟩ := sim.value sortEq
  cases value with
  | unsupported => cases sorted
  | indices coordinates => exact ⟨coordinates, found⟩
  | data => cases sorted
  | index => cases sorted
  | vector => cases sorted
  | transcript => cases sorted

theorem Simulates.index (sim : Simulates data R s env) {index : Nat}
    (sortEq : R.sorts[index]? = some (.data .index)) :
    ∃ value, env[index]? = some (.index value) := by
  obtain ⟨value, found, sorted⟩ := sim.value sortEq
  obtain ⟨decoded, encoded⟩ := sorted
  exact ⟨decoded, by rw [found, ← encoded]; rfl⟩

theorem Simulates.boolean (sim : Simulates data R s env) {index : Nat}
    (sortEq : R.sorts[index]? = some (.data .boolean)) :
    ∃ value, env[index]? = some (.data (.boolean value)) := by
  obtain ⟨value, found, sorted⟩ := sim.value sortEq
  obtain ⟨decoded, encoded⟩ := sorted
  exact ⟨decoded, by rw [found, ← encoded]; rfl⟩

theorem State.bind_eq {s : State F G} {top : Frame F G} {rest : List (Frame F G)}
    (frames : s.frames = top :: rest) (names : List String) (values : List (Value F G)) :
    s.bind names values = { s with frames := ⟨top.id, names.zip values ++ top.env⟩ :: rest } := by
  simp [State.bind, frames]

theorem read_bounds {env : List (Value F G)} :
    ∀ {references : List Nat} {values : List (Value F G)},
      references.mapM (fun reference => env[reference]?) = some values →
      ∀ reference ∈ references, reference < env.length
  | [], _, _ => by simp
  | reference :: references, values, found => by
      simp only [List.mapM_cons] at found
      cases first : env[reference]? with
      | none => simp [first] at found
      | some value =>
          cases others : references.mapM (fun reference => env[reference]?) with
          | none => simp [first, others] at found
          | some rest =>
              intro target member
              rcases List.mem_cons.mp member with rfl | member
              · exact (List.getElem?_eq_some_iff.mp first).1
              · exact read_bounds others target member

theorem sorted_read {env : List (Value F G)} {sorts : List ValueSort}
    (sorted : ∀ (index : Nat) (value : Value F G) (sort : ValueSort),
      env[index]? = some value → sorts[index]? = some sort → HasSort value sort) :
    ∀ {references : List Nat} {values : List (Value F G)} {expected : List ValueSort},
      references.mapM (fun reference => env[reference]?) = some values →
      references.map (sorts[·]?) = expected.map some →
      ∀ (index : Nat) (value : Value F G) (sort : ValueSort), values[index]? = some value →
        expected[index]? = some sort → HasSort value sort
  | [], values, expected, found, sortsEq => by
      change some [] = some values at found
      cases found
      simp
  | reference :: references, values, expected, found, sortsEq => by
      simp only [List.mapM_cons] at found
      cases first : env[reference]? with
      | none => simp [first] at found
      | some value =>
          cases others : references.mapM (fun reference => env[reference]?) with
          | none => simp [first, others] at found
          | some rest =>
              simp [first, others] at found
              subst found
              cases expected with
              | nil => simp at sortsEq
              | cons head tail =>
                  simp only [List.map_cons, List.cons.injEq] at sortsEq
                  intro index v sort vFound sortFound
                  cases index with
                  | zero =>
                      simp only [List.getElem?_cons_zero, Option.some.injEq] at vFound sortFound
                      subst vFound sortFound
                      exact sorted reference value head first sortsEq.1
                  | succ index =>
                      simp only [List.getElem?_cons_succ] at vFound sortFound
                      exact sorted_read sorted others sortsEq.2 index v sort vFound sortFound

theorem read_extend {env : List (Value F G)} (more : List (Value F G)) :
    ∀ {references : List Nat} {values : List (Value F G)},
      references.mapM (fun reference => env[reference]?) = some values →
      references.mapM (fun reference => (env ++ more)[reference]?) = some values
  | [], _, found => found
  | reference :: references, values, found => by
      simp only [List.mapM_cons] at found ⊢
      cases first : env[reference]? with
      | none => simp [first] at found
      | some value =>
          have bound : reference < env.length := (List.getElem?_eq_some_iff.mp first).1
          rw [List.getElem?_append_left bound, first]
          cases others : references.mapM (fun reference => env[reference]?) with
          | none => simp [first, others] at found
          | some rest =>
              simp [first, others] at found
              subst found
              simp [read_extend more others]

theorem read_range' (env : List (Value F G)) :
    ∀ (values : List (Value F G)),
      (List.range' env.length values.length).mapM (fun reference => (env ++ values)[reference]?) =
        some values
  | [] => rfl
  | value :: values => by
      simp only [List.length_cons, List.range'_succ, List.mapM_cons]
      have tail := read_range' (env ++ [value]) values
      simp only [List.length_append, List.length_cons, List.length_nil, List.append_assoc,
        List.singleton_append] at tail
      rw [tail]
      simp

theorem map_filterMap_length {α β : Type} (f : α → Option β) :
    ∀ (xs : List α), (xs.filterMap f).length = xs.length → xs.map f = (xs.filterMap f).map some
  | [], _ => rfl
  | x :: xs, lengths => by
      cases fx : f x with
      | none =>
          simp only [List.filterMap_cons, fx, List.length_cons] at lengths
          have := List.length_filterMap_le f xs
          omega
      | some y =>
          simp only [List.filterMap_cons, fx, List.length_cons, Nat.add_right_cancel_iff] at lengths
          simp [fx, map_filterMap_length f xs lengths]

theorem transcriptPosition_sort {sorts : List ValueSort} {position : Nat}
    (found : transcriptPosition sorts = some position) :
    ∃ suite, sorts[position]? = some (.transcript suite) := by
  have entry := List.of_findIdx?_eq_some found
  cases sortEq : sorts[position]? with
  | none => simp [sortEq] at entry
  | some sort =>
      rw [sortEq] at entry
      cases sort with
      | transcript suite => exact ⟨suite, rfl⟩
      | data => simp at entry
      | indices => simp at entry

theorem custody_at {sorts : List ValueSort} {current : Nat} {references : List Nat}
    (kept : custody sorts current references = true) {reference : Nat} (member : reference ∈ references)
    {suite : String} (sortEq : sorts[reference]? = some (.transcript suite)) : reference = current := by
  simp only [custody, List.all_eq_true] at kept
  have := kept reference member
  simp only [sortEq, beq_iff_eq] at this
  exact this

theorem position_read {references : List Nat} {sorts sorts' : List ValueSort}
    (sortsEq : references.map (sorts[·]?) = sorts'.map some) {position : Nat} {sort : ValueSort}
    (found : sorts'[position]? = some sort) :
    ∃ reference, references[position]? = some reference ∧ sorts[reference]? = some sort := by
  have lengths : references.length = sorts'.length := by simpa using congrArg List.length sortsEq
  have bound : position < references.length := by
    rw [lengths]; exact (List.getElem?_eq_some_iff.mp found).1
  refine ⟨references[position], List.getElem?_eq_getElem bound, ?_⟩
  have := congrArg (·[position]?) sortsEq
  simp only [List.getElem?_map, List.getElem?_eq_getElem bound, found, Option.map_some] at this
  simpa using this

theorem value_at {env : List (Value F G)} {references : List Nat} {values : List (Value F G)}
    (found : references.mapM (fun reference => env[reference]?) = some values)
    {position reference : Nat} (entry : references[position]? = some reference) :
    values[position]? = env[reference]? := by
  induction references generalizing values position with
  | nil => simp at entry
  | cons head tail ih =>
      simp only [List.mapM_cons] at found
      cases first : env[head]? with
      | none => simp [first] at found
      | some value =>
          cases others : tail.mapM (fun reference => env[reference]?) with
          | none => simp [first, others] at found
          | some rest =>
              simp [first, others] at found
              subst found
              cases position with
              | zero =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at entry
                  subst entry
                  simp [first]
              | succ position =>
                  simp only [List.getElem?_cons_succ] at entry ⊢
                  exact ih others entry

end Invariant

theorem admits_sorts (validator : Validator) {data : List (Value F G)} (admitted : validator.admits data = true) :
    ∃ suite, ∃ sorts : List ValueSort, validator.inputs.map (·.2.sort) = sorts ++ [.transcript suite] ∧
      sorts.map some = data.map dataSort? := by
  unfold Validator.admits at admitted
  simp only [Bool.and_eq_true, beq_iff_eq] at admitted
  obtain ⟨dropped, last⟩ := admitted
  cases lastEq : validator.inputs.getLast? with
  | none => simp [lastEq] at last
  | some pair =>
      obtain ⟨name, type⟩ := pair
      simp only [lastEq] at last
      cases sortEq : type.sort with
      | transcript suite =>
          have mapped : (validator.inputs.map (·.2.sort)).getLast? = some (.transcript suite) := by
            simp [List.getLast?_map, lastEq, sortEq]
          obtain ⟨front, frontEq⟩ := List.getLast?_eq_some_iff.mp mapped
          refine ⟨suite, front, frontEq, ?_⟩
          rw [frontEq] at dropped
          simpa using dropped
      | data => simp [sortEq] at last
      | indices => simp [sortEq] at last


/-- Actual entry admission establishes the native scalar frame invariant.
No restriction on a rejected data tuple is introduced by this lemma. -/
theorem initial_simulates (validator : Validator) (data : List (Value F G))
    (history : History F G) (bytes : List UInt8) (admitted : validator.admits data = true) :
    Simulates data ⟨validator.inputs.map (·.2.sort), data.length⟩
      (initial validator data history bytes) (data ++ [.transcript history]) := by
  obtain ⟨suite, sorts, sortsEq, dataSorts⟩ := admits_sorts validator admitted
  have inputsLength : validator.inputs.length = data.length + 1 := by
    have := congrArg List.length sortsEq
    have lengths := congrArg List.length dataSorts
    simp only [List.length_map, List.length_append, List.length_singleton] at this lengths
    omega
  refine ⟨by simp [inputsLength], ?_, ?_, ?_⟩
  · intro index value sort found sortFound
    simp only [sortsEq] at sortFound
    rcases Nat.lt_or_ge index data.length with lt | ge
    · rw [List.getElem?_append_left lt] at found
      have sortsLength : sorts.length = data.length := by
        simpa using congrArg List.length dataSorts
      rw [List.getElem?_append_left (by omega)] at sortFound
      have reported : dataSort? value = some sort := by
        have := congrArg (·[index]?) dataSorts
        simp only [List.getElem?_map, sortFound, found, Option.map_some] at this
        exact (Option.some.inj this).symm
      exact dataSort_sorted reported
    · have sortsLength : sorts.length = data.length := by
        simpa using congrArg List.length dataSorts
      rw [List.getElem?_append_right ge] at found
      rw [List.getElem?_append_right (by omega), sortsLength] at sortFound
      cases offset : index - data.length with
      | zero =>
          simp [offset] at found sortFound
          subst found sortFound
          trivial
      | succ k => simp [offset] at found
  · simp [initial]
  · intro index lt
    rw [List.getElem?_append_left lt]

section Field
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The work a helper call charges: what its body charges on the arguments. -/
def helperCost (vocabulary : Vocabulary) (validator : Validator) (symbol : String)
    (arguments : List (Value F G)) : Nat :=
  (validator.evaluateCall vocabulary symbol arguments).cost

/-- The executable body of the local function `symbol` implements the helper of
the same name in `table`: on arguments of its declared input sorts, its
unbounded evaluation hands back exactly the values the helper returns, at the
function's declared result sorts, or stops in the class the helper stops in. -/
def Prepared (vocabulary : Vocabulary) (validator : Validator)
    (table : Structured.Evaluation.Meanings F G Structured.closedInterface) (symbol : String) : Prop :=
  ∀ callee, validator.function? symbol = some callee →
    ∀ arguments : List (Value F G), callee.inputs.length = arguments.length →
      (∀ (index : Nat) (value : Value F G) (sort : ValueSort), arguments[index]? = some value →
        (callee.inputs.map (·.2.sort))[index]? = some sort → HasSort value sort) →
      match evalSteps vocabulary validator callee.body ((callee.inputs.map (·.1)).zip arguments),
          callHelper table symbol arguments with
      | .values results _, .returned results' =>
          results = results' ∧ results.length = callee.results.length ∧
            ∀ (index : Nat) (value : Value F G) (sort : ValueSort), results[index]? = some value →
              (callee.results.map (·.sort))[index]? = some sort → HasSort value sort
      | .stopped cause _, .stopped reason => cause.outcome = reason
      | _, _ => False


end Field
end Zkc.Executable
