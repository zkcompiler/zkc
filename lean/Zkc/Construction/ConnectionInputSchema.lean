module

public import Zkc.Construction.ConnectionInputs

@[expose] public section

/-! Total decoding under a finite, nominally checked source ABI. A sorted
physical row supplies the complete source tuple, including hidden components
and fixed capabilities; no per-protocol decoding theorem is needed. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionInputs
open Zkc.Source Zkc.Source.Structured NormalForm

/-- Every data selector has exactly the declared nominal source type. -/
def Shape.sortsValid (sorts : List ValueSort) : {types : List Ty} →
    {pattern : InputPattern types} → {locations : List Original.Location} → Shape pattern locations → Bool
  | _, _, _, .nil => true
  | _, _, _, .absent tail => tail.sortsValid sorts
  | _, _, _, @Shape.data ty _ _ _ reference _ tail =>
      (sorts[reference]? == some (.data ty)) && tail.sortsValid sorts
  | _, _, _, .capability tail => tail.sortsValid sorts

private theorem decode_of_sort {carriers : Carriers} {physical : Domain.Value carriers} {ty : Ty}
    (same : physical.sort = .data ty) : ∃ value, physical.decode ty = some value := by
  cases physical with
  | data payload =>
    cases payload with
    | mk actual allowed value =>
      cases same
      exact ⟨value, by simp [Domain.Value.decode, Domain.Payload.value]⟩
  | transcript => cases same
  | indices => cases same

/-- A sort-checked physical position yields a complete, nominally typed input. -/
theorem read_sorted {carriers : Carriers} {sorts : List ValueSort}
    {frame : Domain.Environment carriers} (matched : Domain.sortsMatch sorts frame = true)
    {reference : Nat} {ty : Ty} (selected : sorts[reference]? = some (.data ty)) :
    ∃ value, (frame[reference]?).bind (Domain.Value.decode ty) = some value := by
  have same : frame.map Domain.Value.sort = sorts := by
    simpa only [Domain.sortsMatch, beq_iff_eq] using matched
  rw [← same, List.getElem?_map] at selected
  cases found : frame[reference]? with
  | none => simp only [found, Option.map_none, reduceCtorEq] at selected
  | some physical =>
    have nominal : physical.sort = .data ty := by simpa only [found, Option.map_some, Option.some.injEq] using selected
    obtain ⟨value, decoded⟩ := decode_of_sort nominal
    exact ⟨value, by simp only [Option.bind_some, decoded]⟩

/-- Sorted physical inputs cannot fail decoding under the checked source ABI. -/
theorem Shape.values {carriers : Carriers} {types : List Ty} {pattern : InputPattern types}
    {locations : List Original.Location} (shape : Shape pattern locations)
    {sorts : List ValueSort} (valid : shape.sortsValid sorts = true)
    (frame : Domain.Environment carriers) (matched : Domain.sortsMatch sorts frame = true) :
    ∃ values : Values (Component carriers.Value) types, Original.ValuesHolds frame locations values := by
  induction shape with
  | nil => exact ⟨.nil, trivial⟩
  | absent tail ih =>
    obtain ⟨values, related⟩ := ih valid
    exact ⟨.cons none values, rfl, related⟩
  | data reference allowed tail ih =>
    obtain ⟨selected, valid⟩ := Bool.and_eq_true_iff.mp valid
    obtain ⟨value, read⟩ := read_sorted matched (by simpa only [beq_iff_eq] using selected)
    obtain ⟨values, related⟩ := ih valid
    exact ⟨.cons (some value) values, ⟨value, rfl, read⟩, related⟩
  | @capability service handle types pattern locations tail ih =>
    obtain ⟨values, related⟩ := ih valid
    exact ⟨.cons (some handle) values, rfl, related⟩

/-- Every physical source selector is within the declared row. This fact is
computed from the same sort checks, rather than supplied per protocol. -/
theorem Shape.bounds {types : List Ty} {pattern : InputPattern types}
    {locations : List Original.Location} (shape : Shape pattern locations)
    {sorts : List ValueSort} (valid : shape.sortsValid sorts = true) :
    Original.LocationsBound sorts.length locations := by
  induction shape with
  | nil => intro reference member; cases member
  | absent tail ih =>
    intro reference member
    exact ih valid reference (by simpa only [List.mem_cons, reduceCtorEq, false_or] using member)
  | @data ty _ _ _ reference allowed tail ih =>
    obtain ⟨selected, valid⟩ := Bool.and_eq_true_iff.mp valid
    have selected : sorts[reference]? = some (.data ty) := by simpa only [beq_iff_eq] using selected
    have inside := (List.getElem?_eq_some_iff.mp selected).1
    intro candidate member
    rcases List.mem_cons.mp member with same | later
    · cases same; exact inside
    · exact ih valid candidate later
  | capability tail ih =>
    intro reference member
    exact ih valid reference (by simpa only [List.mem_cons, reduceCtorEq, false_or] using member)

theorem Shape.physicalBounds {carriers : Carriers} {types : List Ty} {pattern : InputPattern types}
    {locations : List Original.Location} (shape : Shape pattern locations)
    {sorts : List ValueSort} (valid : shape.sortsValid sorts = true)
    {frame : Domain.Environment carriers} (matched : Domain.sortsMatch sorts frame = true) :
    Original.LocationsBound frame.length locations := by
  have same : frame.map Domain.Value.sort = sorts := by
    simpa only [Domain.sortsMatch, beq_iff_eq] using matched
  have length : frame.length = sorts.length := by simpa only [List.length_map] using congrArg List.length same
  rw [length]
  exact shape.bounds valid

/-- The same finite data supplies the symbolic input binders, with no literal
data specialization and no extra assumption on runtime input values. -/
theorem Shape.binders_of_sorts {model : DomainModel} {types : List Ty} {pattern : InputPattern types}
    {locations : List Original.Location} (shape : Shape pattern locations)
    {sorts : List ValueSort} (valid : shape.sortsValid sorts = true)
    (frame : Domain.Environment model.toCarriers) (matched : Domain.sortsMatch sorts frame = true) :
    ∃ binders : Binders model pattern.scope,
      Original.ValuesHolds frame locations (pattern.environment model binders) := by
  obtain ⟨values, related⟩ := shape.values valid frame matched
  obtain ⟨binders, same⟩ := shape.binders frame values related
  exact ⟨binders, same.symm ▸ related⟩

end Zkc.Construction.ConnectionInputs
