module

public import Zkc.Construction.OriginalRouting
public import Zkc.Construction.OriginProjection

@[expose] public section

/-! Reindexing preserves checked static source routes. The resolver still
constructs each key from the complete reached dynamic coordinate stack. -/
set_option autoImplicit false
namespace Zkc.Construction.OccurrenceResolution
open Zkc.Source

theorem matches_reindex (snapshot : Structured.Snapshot) (context : Context)
    (expected : Origin) (frames other : Frames) (template : Template)
    (sites : frames.map (·.site) = other.map (·.site)) :
    matchesOccurrence snapshot context expected frames template =
      matchesOccurrence snapshot context expected other template := by
  have lengths : frames.length = other.length := by
    simpa only [List.length_map] using congrArg List.length sites
  unfold matchesOccurrence Domain.templateOrigin
  rw [sites]
  by_cases origin : template.origin context = some expected
  · simp only [origin, beq_self_eq_true, Bool.and_true, List.length_map, lengths]
    split <;> simp
  · have unequal : (template.origin context == some expected) = false := by
      exact beq_eq_false_iff_ne.mpr origin
    simp only [unequal, Bool.and_false, Bool.false_and]

theorem resolve_reindex (snapshot : Structured.Snapshot) (context : Context)
    (expected : Origin) (frames other : Frames) (candidates : List Template)
    (sites : frames.map (·.site) = other.map (·.site))
    (static : expected.event.length = 6) :
    resolve snapshot context expected other candidates =
      (resolve snapshot context expected frames candidates).map
        (fun origin => Domain.atCoordinates origin.withoutCoordinates (other.map (·.index))) := by
  have filters : candidates.filter (matchesOccurrence snapshot context expected frames) =
      candidates.filter (matchesOccurrence snapshot context expected other) := by
    apply List.filter_congr
    intro template _
    exact matches_reindex snapshot context expected frames other template sites
  unfold resolve
  rw [← filters]
  split <;> simp only [Option.map_none, Option.map_some,
    Origin.withoutCoordinates_atCoordinates _ _ static]

end Zkc.Construction.OccurrenceResolution

namespace Zkc.Construction.Original
open Zkc.Source

theorem Routing.message_reindex (routing : Routing) (frames other : Frames)
    (sites : frames.map (·.site) = other.map (·.site))
    (site : String) (sender receiver : Nat) :
    routing.message other site sender receiver =
      (routing.message frames site sender receiver).map
        (fun origin => Domain.atCoordinates origin.withoutCoordinates (other.map (·.index))) :=
  OccurrenceResolution.resolve_reindex _ _ _ _ _ _ sites rfl

theorem Routing.draw_reindex (routing : Routing) (frames other : Frames)
    (sites : frames.map (·.site) = other.map (·.site))
    (site field : String) (handle : Nat) :
    routing.draw other site field handle =
      (routing.draw frames site field handle).map
        (fun origin => Domain.atCoordinates origin.withoutCoordinates (other.map (·.index))) := by
  unfold Routing.draw
  split
  · exact OccurrenceResolution.resolve_reindex _ _ _ _ _ _ sites rfl
  · rfl

theorem Routing.delivery_reindex (routing : Routing) (frames other : Frames)
    (sites : frames.map (·.site) = other.map (·.site))
    (site field : String) (sender : Nat) :
    routing.delivery other site field sender =
      (routing.delivery frames site field sender).map
        (fun origins =>
          (Domain.atCoordinates origins.1.withoutCoordinates (other.map (·.index)),
           Domain.atCoordinates origins.2.withoutCoordinates (other.map (·.index)))) := by
  unfold Routing.delivery
  split
  · rfl
  · simp only [pure, Bind.bind, Option.bind]
    split
    · rename_i candidate found
      rw [OccurrenceResolution.resolve_reindex _ _ _ frames other _ sites rfl]
      rw [OccurrenceResolution.resolve_reindex _ _ _ frames other _ sites rfl]
      cases OccurrenceResolution.resolve routing.snapshot routing.context
        (routing.context.message site sender routing.context.producer) frames [candidate.message] <;>
        cases OccurrenceResolution.resolve routing.snapshot routing.context
          (routing.context.query (candidate.draw.qualify (candidate.draw.event[2]?.getD "")) (.draw field))
          frames [candidate.draw] <;> rfl
    · rfl

end Zkc.Construction.Original
