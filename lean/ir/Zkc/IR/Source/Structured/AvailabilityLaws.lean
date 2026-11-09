module

public import Zkc.IR.Source.Structured.Availability

@[expose] public section

/-! Successful budgeted footprint computations retain their mathematical meaning.
No lemma here turns presence into termination or grants a projection equation. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.Availability

/-- A successful analysis result at some pair of budgets. -/
def RunsTo {α : Type} (action : Analysis α) (result : α) : Prop :=
  ∃ before after, action.run before = .ok (result, after)

theorem RunsTo.bind {α β : Type} {first : Analysis α} {next : α → Analysis β}
    {result : β} (success : RunsTo (first >>= next) result) :
    ∃ value, RunsTo first value ∧ RunsTo (next value) result := by
  obtain ⟨before, after, success⟩ := success
  change (first before >>= fun pair : α × Budget => next pair.1 pair.2) =
    .ok (result, after) at success
  cases firstRun : first before with
  | error code => rw [firstRun] at success; cases success
  | ok pair =>
    obtain ⟨value, middle⟩ := pair
    rw [firstRun] at success
    exact ⟨value, ⟨before, middle, firstRun⟩, ⟨middle, after, success⟩⟩

theorem RunsTo.pure {α : Type} {value result : α}
    (success : RunsTo (pure value) result) : result = value := by
  obtain ⟨before, after, success⟩ := success
  exact (Prod.mk.inj (Except.ok.inj success)).1.symm

/-- Transfer a successful budgeted fold to its pure value computation. -/
theorem foldlM_value {α β : Type} (step : α → β → Analysis α) (value : α → β → α)
    (stepValue : ∀ acc item result, RunsTo (step acc item) result → result = value acc item)
    (items : List β) (initial result : α)
    (success : RunsTo (items.foldlM step initial) result) :
    result = items.foldl value initial := by
  induction items generalizing initial with
  | nil => exact RunsTo.pure success
  | cons item rest ih =>
    obtain ⟨middle, first, next⟩ := RunsTo.bind success
    rw [List.foldl_cons, ← stepValue initial item middle first]
    exact ih middle next

/-- Union's successful value retains insertion order and deduplicates only the right side. -/
def join (left right : Footprint) : Footprint :=
  right.foldl (fun acc index => if acc.contains index then acc else acc ++ [index]) left

theorem union_value {left right result : Footprint} (success : RunsTo (union left right) result) :
    result = join left right := by
  apply foldlM_value _ _ ?_ right left result success
  intro acc index result success
  obtain ⟨_, _, next⟩ := RunsTo.bind success
  have same : (if acc.contains index then pure acc else pure (acc ++ [index]) :
      Analysis Footprint) = pure (if acc.contains index then acc else acc ++ [index]) := by
    split <;> rfl
  rw [same] at next
  exact RunsTo.pure next

@[simp] theorem mem_join (left right : Footprint) (index : Nat) :
    index ∈ join left right ↔ index ∈ left ∨ index ∈ right := by
  induction right generalizing left with
  | nil => simp [join]
  | cons head tail ih =>
    simp only [join, List.foldl_cons]
    change index ∈ join (if left.contains head then left else left ++ [head]) tail ↔ _
    rw [ih]
    by_cases contains : head ∈ left
    · simp only [List.contains_iff_mem.mpr contains, ite_true, List.mem_cons]
      constructor
      · intro member; exact member.imp_right Or.inr
      · rintro (member | same | member)
        · exact Or.inl member
        · exact Or.inl (same ▸ contains)
        · exact Or.inr member
    · simp [contains, List.mem_append, or_assoc]

/-- Successful helper lookup cannot replace a missing formal position with an empty set. -/
theorem argument_value {arguments : List Footprint} {index : Nat} {result : Footprint}
    (success : RunsTo (argument arguments index) result) : arguments[index]? = some result := by
  obtain ⟨_, _, next⟩ := RunsTo.bind success
  cases found : arguments[index]? with
  | none => obtain ⟨before, after, next⟩ := next; simp only [found] at next; cases next
  | some value =>
    have same : result = value := RunsTo.pure (by simpa [found] using next)
    simp only [same]

/-- Successful substitution is the actual ordered union of actual argument footprints. -/
theorem substitute_value {arguments : List Footprint} {footprint result : Footprint}
    (success : RunsTo (substitute arguments footprint) result) :
    result = footprint.foldl (fun acc index => join acc (arguments[index]?.getD [])) [] := by
  apply foldlM_value _ _ ?_ footprint [] result success
  intro acc index result success
  obtain ⟨value, first, next⟩ := RunsTo.bind success
  rw [argument_value first]
  exact union_value next

/-- Union membership is exact even when the operand footprints alias. -/
theorem union_mem {left right result : Footprint} (success : RunsTo (union left right) result)
    (index : Nat) : index ∈ result ↔ index ∈ left ∨ index ∈ right := by
  rw [union_value success, mem_join]

theorem mem_substitution_fold (arguments : List Footprint) (footprint initial : Footprint)
    (index : Nat) :
    index ∈ footprint.foldl (fun acc formal => join acc (arguments[formal]?.getD [])) initial ↔
      index ∈ initial ∨ ∃ formal ∈ footprint, index ∈ arguments[formal]?.getD [] := by
  induction footprint generalizing initial with
  | nil => simp
  | cons formal rest ih =>
    rw [List.foldl_cons, ih, mem_join]
    simp only [List.mem_cons]
    constructor
    · rintro ((member | member) | ⟨position, member, inner⟩)
      · exact Or.inl member
      · exact Or.inr ⟨formal, Or.inl rfl, member⟩
      · exact Or.inr ⟨position, Or.inr member, inner⟩
    · rintro (member | ⟨position, same | member, inner⟩)
      · exact Or.inl (Or.inl member)
      · subst position; exact Or.inl (Or.inr inner)
      · exact Or.inr ⟨position, member, inner⟩

/-- Both result dependencies and operation requirements use this same substitution law. -/
theorem substitute_mem {arguments : List Footprint} {footprint result : Footprint}
    (success : RunsTo (substitute arguments footprint) result) (index : Nat) :
    index ∈ result ↔ ∃ formal ∈ footprint,
      ∃ actual, arguments[formal]? = some actual ∧ index ∈ actual := by
  rw [substitute_value success, mem_substitution_fold]
  simp only [List.not_mem_nil, false_or]
  apply exists_congr
  intro formal
  apply and_congr_right
  intro _
  cases arguments[formal]? <;> simp

/-- A successful fold visited every stored item, irrespective of its result. -/
theorem foldlM_inputs {α β : Type} (step : α → β → Analysis α) (property : β → Prop)
    (stepProperty : ∀ acc item result, RunsTo (step acc item) result → property item)
    (items : List β) (initial result : α)
    (success : RunsTo (items.foldlM step initial) result) :
    ∀ item ∈ items, property item := by
  induction items generalizing initial with
  | nil => simp
  | cons head tail ih =>
    obtain ⟨middle, first, next⟩ := RunsTo.bind success
    intro item member
    rcases List.mem_cons.mp member with same | member
    · subst item; exact stepProperty initial head middle first
    · exact ih middle next item member

theorem substitute_in_bounds {arguments : List Footprint} {footprint result : Footprint}
    (success : RunsTo (substitute arguments footprint) result) :
    ∀ formal ∈ footprint, ∃ actual, arguments[formal]? = some actual := by
  apply foldlM_inputs _ (fun formal => ∃ actual, arguments[formal]? = some actual)
    ?_ footprint [] result success
  intro acc formal result success
  obtain ⟨actual, first, _⟩ := RunsTo.bind success
  exact ⟨actual, argument_value first⟩

/-- Availability is conditional presence; it says nothing about return or truth. -/
def Ready (held : Nat → Prop) (footprint : Footprint) : Prop :=
  ∀ index ∈ footprint, held index

theorem substitute_ready (held : Nat → Prop) {arguments : List Footprint}
    {footprint result : Footprint} (success : RunsTo (substitute arguments footprint) result) :
    Ready held result ↔ ∀ formal ∈ footprint,
      ∃ actual, arguments[formal]? = some actual ∧ Ready held actual := by
  constructor
  · intro ready formal member
    obtain ⟨actual, found⟩ := substitute_in_bounds success formal member
    exact ⟨actual, found, fun index inner =>
      ready index ((substitute_mem success index).mpr ⟨formal, member, actual, found, inner⟩)⟩
  · intro ready index member
    obtain ⟨formal, member, actual, found, inner⟩ := (substitute_mem success index).mp member
    obtain ⟨other, same, held⟩ := ready formal member
    have equal : actual = other := Option.some.inj (found.symm.trans same)
    exact held index (equal ▸ inner)

/-- Successful SSA lookup preserves the actual de Bruijn position. -/
theorem lookup_value {environment : Environment} {index : Nat} {result : Footprint}
    (success : RunsTo (lookup environment index) result) :
    ∃ bound : index < environment.size,
      result = environment[environment.size - 1 - index]'(by omega) := by
  obtain ⟨_, _, next⟩ := RunsTo.bind success
  by_cases bound : index < environment.size
  · exact ⟨bound, RunsTo.pure (by simpa only [dite_eq_left bound] using next)⟩
  · obtain ⟨before, after, next⟩ := next
    simp only [dite_eq_right bound] at next
    cases next

/-- Replay computes each requirement's intersection separately. -/
theorem available_value {roles : Nat} {arguments : List Footprint}
    {footprint result : Footprint} (success : RunsTo (available roles arguments footprint) result) :
    result = footprint.foldl (fun scope formal =>
      scope.filter (arguments[formal]?.getD []).contains) (List.range roles) := by
  obtain ⟨_, _, next⟩ := RunsTo.bind success
  apply foldlM_value _ _ ?_ footprint (List.range roles) result next
  intro scope formal result success
  obtain ⟨_, _, next⟩ := RunsTo.bind success
  cases found : arguments[formal]? with
  | none =>
    obtain ⟨before, after, next⟩ := next
    simp only [found] at next
    cases next
  | some actual =>
    simp only [found] at next
    obtain ⟨_, _, next⟩ := RunsTo.bind next
    exact RunsTo.pure next

theorem mem_available_fold (arguments : List Footprint) (footprint initial : Footprint)
    (role : Nat) :
    role ∈ footprint.foldl (fun scope formal =>
      scope.filter (arguments[formal]?.getD []).contains) initial ↔
      role ∈ initial ∧ ∀ formal ∈ footprint, role ∈ arguments[formal]?.getD [] := by
  induction footprint generalizing initial with
  | nil => simp
  | cons formal rest ih =>
    simp [List.foldl_cons, ih, List.mem_filter, and_assoc]

/-- A role witnesses exactly the actual joint operand presence of this requirement. -/
theorem available_mem {roles : Nat} {arguments : List Footprint}
    {footprint result : Footprint} (success : RunsTo (available roles arguments footprint) result)
    (role : Nat) :
    role ∈ result ↔ role < roles ∧ ∀ formal ∈ footprint,
      ∃ actual, arguments[formal]? = some actual ∧ role ∈ actual := by
  rw [available_value success, mem_available_fold, List.mem_range]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro formal
  apply forall_congr'
  intro _
  cases arguments[formal]? <;> simp

theorem extendEnvironment_size (environment : Environment) (results : List Footprint) :
    (extendEnvironment environment results).size = environment.size + results.length := by
  simp [extendEnvironment]

/-- Array storage is the reverse of the typed context's declared operand order. -/
theorem extendEnvironment_order (environment : Environment) (results : List Footprint) :
    (extendEnvironment environment results).toList.reverse =
      results ++ environment.toList.reverse := by
  induction results with
  | nil => rfl
  | cons result rest ih =>
    simp only [extendEnvironment, List.foldr_cons, Array.toList_push,
      List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append]
    change result :: (extendEnvironment environment rest).toList.reverse = _
    rw [ih]
    rfl

theorem lookup_position {environment : Environment} {index : Nat} {result : Footprint}
    (success : RunsTo (lookup environment index) result) :
    environment.toList.reverse[index]? = some result := by
  obtain ⟨bound, same⟩ := lookup_value success
  rw [List.getElem?_reverse (by simpa using bound), Array.getElem?_toList]
  simp only [Array.length_toList]
  rw [Array.getElem?_eq_getElem (by omega)]
  exact congrArg some same.symm

/-- Typed operand traversal reads the exact SSA positions, including aliases. -/
theorem operands_value {context types : List Ty} (environment : Environment)
    (refs : Operands context types) {result : List Footprint}
    (success : RunsTo (operands environment refs) result) :
    result = refs.indices.map (fun index => environment.toList.reverse[index]?.getD []) := by
  induction refs generalizing result with
  | nil => exact RunsTo.pure success
  | cons ref rest ih =>
    obtain ⟨_, _, next⟩ := RunsTo.bind success
    obtain ⟨value, found, next⟩ := RunsTo.bind next
    obtain ⟨tail, computed, next⟩ := RunsTo.bind next
    have same := RunsTo.pure next
    rw [same, ih computed]
    simp only [Operands.indices, List.map_cons, lookup_position found, Option.getD_some]

end Zkc.Source.Structured.Availability
