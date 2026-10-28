module

public import Zkc.Construction.ConnectionStaticRoutes
public import Zkc.Construction.ConnectionTranscript

@[expose] public section

/-! Shared symbolic frame and route consequences for the finite engine. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionFrame
open Zkc.Source Zkc.Source.Structured NormalForm

def observedLayout {scope : Scope} (layout : Layout scope) (suite : String) : Layout scope :=
  layout.map Cell.retireHistory ++ [.history suite]

def queryLayout {scope : Scope} (layout : Layout scope) (field suite : String) :
    Layout (.value (.field field) :: scope) :=
  (layout.map Cell.retireHistory).map (Cell.rename .there) ++
    [.data (.present (.var .here)), .history suite]

def observedReceiveLayout {scope : Scope} (layout : Layout scope) (ty : Ty) (suite : String) :
    Layout (.value ty :: scope) :=
  (layout.map Cell.retireHistory).map (Cell.rename .there) ++
    [.data (.present (.var .here)), .history suite]

def deliveryLayout {scope : Scope} (layout : Layout scope) (field suite : String) :
    Layout (.value (.field field) :: scope) :=
  (layout.map Cell.retireHistory).map (Cell.rename .there) ++
    [.data (.present (.var .here)), .unused, .history suite]

/-- Nominal payload readback uses the existing source model and encoder. -/
theorem Readback.payload {model : DomainModel} {scope : Scope}
    {binders : Binders model scope} {history : Domain.History model.toCarriers}
    {layout : Layout scope} {environment : Domain.Environment model.toCarriers}
    {ty : Ty} {term : Term [] scope ty} {reference : Nat}
    (checked : Readback layout (.cons (.present term) .nil) [.data reference])
    (related : Holds model binders history layout environment) :
    ∃ payload, Domain.Payload.ofValue ty (term.eval (LawResults.empty model) binders) = some payload ∧
      environment[reference]? = some (.data payload) := by
  obtain ⟨value, physical, present, encoded, read⟩ := checked.component related
  have same : value = term.eval (LawResults.empty model) binders := Option.some.inj present.symm
  subst value
  unfold Domain.Value.encode at encoded
  cases found : Domain.Payload.ofValue ty (term.eval (LawResults.empty model) binders) with
  | none => simp only [found, Option.map_none] at encoded; cases encoded
  | some payload =>
    exact ⟨payload, rfl, read.trans (congrArg some (Option.some.inj (by simpa only [found, Option.map_some] using encoded)).symm)⟩

inductive IndexReadback {scope : Scope} (layout : Layout scope) :
    List (Term [] scope .index) → List Nat → Type where
  | nil : IndexReadback layout [] []
  | cons {terms : List (Term [] scope .index)} {references : List Nat}
      (term : Term [] scope .index) (reference : Nat)
      (checked : layout[reference]? = some (.data (.present term)))
      (tail : IndexReadback layout terms references) :
      IndexReadback layout (term :: terms) (reference :: references)

theorem IndexReadback.read {model : DomainModel} {scope : Scope}
    {binders : Binders model scope} {history : Domain.History model.toCarriers}
    {layout : Layout scope} {environment : Domain.Environment model.toCarriers}
    {terms : List (Term [] scope .index)} {references : List Nat}
    (checked : IndexReadback layout terms references)
    (related : Holds model binders history layout environment) :
    Domain.localCoordinates environment references =
      some (terms.map fun term => term.eval (LawResults.empty model) binders) := by
  induction checked with
  | nil => rfl
  | cons term reference checked tail ih =>
    simp only [Domain.localCoordinates, List.mapM_cons, related.index checked, bind, Option.bind]
    change _ = _ at ih
    simp only [Domain.localCoordinates] at ih
    rw [ih]
    rfl

theorem template_reached {model : DomainModel} {scope : Scope}
    (frames : ScopedFrames scope) (binders : Binders model scope)
    {snapshot : Snapshot} {context : Context} {expected : Origin}
    {candidates : List Template} {template : Template}
    (checked : OccurrenceResolution.resolveStatic snapshot context expected frames.sites candidates = some template) :
    Domain.templateOrigin context template ((frames.eval model binders).map (·.index)) =
      some (Domain.atCoordinates expected ((frames.eval model binders).map (·.index))) :=
  OccurrenceResolution.template_of_static checked _ (frames.sites_eval model binders)

theorem query_reached {model : DomainModel} {scope : Scope}
    (frames : ScopedFrames scope) (binders : Binders model scope)
    {routing : Original.Routing} {site field : String} {template : Template}
    (contract : routing.context.contract = "random." ++ field ++ "/0")
    (request : routing.context.request = some (.draw field))
    (checked : OccurrenceResolution.resolveStatic routing.snapshot routing.context
      (routing.context.query site (.draw field)) frames.sites routing.draws = some template) :
    Domain.queryOrigin routing.context routing.context.suite field template
      ((frames.eval model binders).map (·.index)) =
      some (Domain.atCoordinates (routing.context.query site (.draw field))
        ((frames.eval model binders).map (·.index))) := by
  rw [Domain.queryOrigin, ite_eq_left ⟨rfl, contract, request⟩, template_reached frames binders checked]
  have asked : (Domain.atCoordinates (routing.context.query site (.draw field))
      ((frames.eval model binders).map (·.index))).request = some (.draw field) := by
    unfold Domain.atCoordinates
    split <;> rfl
  simp only [asked, ↓reduceIte]

end Zkc.Construction.ConnectionFrame
