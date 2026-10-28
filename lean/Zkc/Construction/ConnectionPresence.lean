module

public import Zkc.Construction.ConnectionFrame

@[expose] public section

/-! Presence refinement for a symbolic physical frame. These operations reuse
the normalizer's own substitutions. A presence split changes the names used
for an existing value, not the physical environment or the source meaning. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionFrame
open Zkc.Source Zkc.Source.Structured NormalForm

/-- Substitute a known-absent component in the tracked source expressions. -/
def Cell.absentAt {scope : Scope} {ty : Ty} (subject : Subject scope ty) : Cell scope → Cell scope
  | .data component => .data (component.absentAt subject)
  | .guarded component => .guarded (component.absentAt subject)
  | cell => cell

/-- Substitute a known-present component and bind its value once. History and
coordinate entries are weakened through the same source scope change. -/
def Cell.presentAt {scope : Scope} {ty : Ty} (subject : Subject scope ty) :
    Cell scope → Cell (.value ty :: scope)
  | .data component => .data (component.presentAt subject)
  | .guarded component => .guarded (component.presentAt subject)
  | cell => cell.rename .there

theorem Cell.Holds.absentAt {model : DomainModel} {scope : Scope} {ty : Ty}
    (subject : Subject scope ty) {binders : Binders model scope}
    (absent : subject.comp.eval (LawResults.empty model) binders = none)
    {history : Domain.History model.toCarriers} {cell : Cell scope} {physical : Domain.Value model.toCarriers}
    (related : Cell.Holds model binders history cell physical) :
    Cell.Holds model binders history (cell.absentAt subject) physical := by
  cases cell with
  | data component =>
    obtain ⟨value, present, encoded⟩ := related
    exact ⟨value, (comp_eval_absentAt _ subject binders absent component).trans present, encoded⟩
  | guarded component =>
    exact ⟨by simpa only [Cell.Holds, comp_eval_absentAt _ subject binders absent component] using related.1, related.2⟩
  | history | coordinates | unused => exact related

theorem Cell.Holds.presentAt {model : DomainModel} {scope : Scope} {ty : Ty}
    (subject : Subject scope ty) (value : model.Value ty) {binders : Binders model scope}
    (present : subject.comp.eval (LawResults.empty model) binders = some value)
    {history : Domain.History model.toCarriers} {cell : Cell scope} {physical : Domain.Value model.toCarriers}
    (related : Cell.Holds model binders history cell physical) :
    Cell.Holds model (.cons value binders) history (cell.presentAt subject) physical := by
  cases cell with
  | data component =>
    obtain ⟨actual, evaluated, encoded⟩ := related
    exact ⟨actual, (comp_eval_presentAt _ subject value binders present component).trans evaluated, encoded⟩
  | guarded component =>
    exact ⟨by simpa only [Cell.Holds, comp_eval_presentAt _ subject value binders present component] using related.1, related.2⟩
  | history | coordinates | unused => exact related.rename .there (fun _ => rfl)

theorem Holds.absentAt {model : DomainModel} {scope : Scope} {ty : Ty}
    (subject : Subject scope ty) {binders : Binders model scope}
    (absent : subject.comp.eval (LawResults.empty model) binders = none)
    {history : Domain.History model.toCarriers} {layout : Layout scope}
    {environment : Domain.Environment model.toCarriers}
    (related : Holds model binders history layout environment) :
    Holds model binders history (layout.map (Cell.absentAt subject)) environment := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.absentAt subject absent) ih

theorem Holds.presentAt {model : DomainModel} {scope : Scope} {ty : Ty}
    (subject : Subject scope ty) (value : model.Value ty) {binders : Binders model scope}
    (present : subject.comp.eval (LawResults.empty model) binders = some value)
    {history : Domain.History model.toCarriers} {layout : Layout scope}
    {environment : Domain.Environment model.toCarriers}
    (related : Holds model binders history layout environment) :
    Holds model (.cons value binders) history (layout.map (Cell.presentAt subject)) environment := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.presentAt subject value present) ih

/-- A physical readback rules out the absent branch. This follows from an
actual frame relation; a candidate cannot simply label an input present. -/
theorem Holds.not_absent {model : DomainModel} {scope : Scope} {binders : Binders model scope}
    {history : Domain.History model.toCarriers} {layout : Layout scope}
    {environment : Domain.Environment model.toCarriers}
    (related : Holds model binders history layout environment) {reference : Nat} {ty : Ty}
    {component : Comp [] scope ty} (checked : layout[reference]? = some (.data component)) :
    component.eval (LawResults.empty model) binders ≠ none := by
  obtain ⟨value, physical, present, encoded, read⟩ := related.data checked
  rw [present]
  intro impossible
  cases impossible

end Zkc.Construction.ConnectionFrame
