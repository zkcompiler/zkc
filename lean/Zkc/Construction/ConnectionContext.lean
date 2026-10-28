module

public import Zkc.Construction.ConnectionCoordinates
public import Zkc.Construction.ConnectionOrigins

@[expose] public section

/-! The reached source stack in the same symbolic scope as physical values.
A loop index is a source binder, not a guessed constant or an independently
quantified frame value. Static site checks therefore cover every runtime index,
while ordered coordinate readback ties the constructed transcript to that stack.
-/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionFrame
open Zkc.Source Zkc.Source.Structured NormalForm

structure ScopedFrame (scope : Scope) where
  site : String
  index : Term [] scope .index

abbrev ScopedFrames (scope : Scope) := List (ScopedFrame scope)

def ScopedFrames.sites {scope : Scope} (frames : ScopedFrames scope) : List String :=
  frames.map (·.site)
def ScopedFrames.coordinates {scope : Scope} (frames : ScopedFrames scope) : List (Term [] scope .index) :=
  frames.map (·.index)
def ScopedFrames.eval (model : DomainModel) {scope : Scope} (binders : Binders model scope)
    (frames : ScopedFrames scope) : Original.Frames :=
  frames.map fun frame => ⟨frame.site, frame.index.eval (LawResults.empty model) binders⟩
def ScopedFrames.rename {scope target : Scope} (rename : Rename scope target)
    (frames : ScopedFrames scope) : ScopedFrames target :=
  frames.map fun frame => ⟨frame.site, frame.index.rename rename⟩

theorem ScopedFrames.sites_eval (model : DomainModel) {scope : Scope} (binders : Binders model scope)
    (frames : ScopedFrames scope) : (frames.eval model binders).map (·.site) = frames.sites := by
  simp only [eval, sites, List.map_map, Function.comp_def]

theorem ScopedFrames.coordinates_eval (model : DomainModel) {scope : Scope} (binders : Binders model scope)
    (frames : ScopedFrames scope) :
    (frames.eval model binders).map (·.index) =
      frames.coordinates.map (fun term => term.eval (LawResults.empty model) binders) := by
  simp only [eval, coordinates, List.map_map, Function.comp_def]

theorem ScopedFrames.eval_rename {model : DomainModel} {scope target : Scope}
    (rename : Rename scope target) (binders : Binders model scope) (next : Binders model target)
    (same : ∀ {slot : Slot} (binder : Var scope slot), next.get (rename binder) = binders.get binder)
    (frames : ScopedFrames scope) : (frames.rename rename).eval model next = frames.eval model binders := by
  simp only [eval, ScopedFrames.rename, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro frame _
  simp only [term_eval_rename (LawResults.empty model) rename binders next same]

theorem ScopedFrames.eval_append (model : DomainModel) {scope : Scope} (binders : Binders model scope)
    (first last : ScopedFrames scope) :
    (first ++ last).eval model binders = first.eval model binders ++ last.eval model binders :=
  List.map_append

/-- One static route certificate covers all valuations of the index terms. -/
theorem ScopedFrames.resolve {model : DomainModel} {scope : Scope}
    (binders : Binders model scope) (frames : ScopedFrames scope)
    {snapshot : Snapshot} {context : Context} {expected : Origin}
    {candidates : List Template} {template : Template}
    (checked : OccurrenceResolution.resolveStatic snapshot context expected frames.sites candidates = some template) :
    OccurrenceResolution.resolve snapshot context expected (frames.eval model binders) candidates =
      some (Domain.atCoordinates expected
        (frames.coordinates.map fun term => term.eval (LawResults.empty model) binders)) := by
  simpa only [frames.coordinates_eval model binders] using
    OccurrenceResolution.resolve_of_static checked (frames.eval model binders) (frames.sites_eval model binders)

/-- A physical path has precisely the reached source coordinates, in order.
Equal runtime indices do not justify swapping the underlying source binders. -/
theorem Holds.reachedCoordinates {model : DomainModel} {scope : Scope}
    {binders : Binders model scope} {history : Domain.History model.toCarriers}
    {layout : Layout scope} {environment : Domain.Environment model.toCarriers}
    (related : Holds model binders history layout environment)
    (frames : ScopedFrames scope) (reference : Nat)
    (checked : layout[reference]? = some (.coordinates frames.coordinates)) :
    environment[reference]? = some (.indices ((frames.eval model binders).map (·.index))) := by
  rw [ScopedFrames.coordinates_eval]
  exact related.coordinates checked

end Zkc.Construction.ConnectionFrame
