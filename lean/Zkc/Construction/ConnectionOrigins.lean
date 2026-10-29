module

public import Zkc.Construction.ConnectionRouting

@[expose] public section

/-! Static route validation with a theorem for every reached dynamic index.
The certificate checks actual source identity, ordered enclosing repeat sites,
nominal origin, and template structure. Runtime indices remain arbitrary and
are inserted by the existing resolver; no loop is unrolled to prove a route.
-/
set_option autoImplicit false
namespace Zkc.Construction.OccurrenceResolution

/-- The static part of an occurrence match, including the template's full
coordinate schema. This is checked against the source, not a supplied digest. -/
def matchesStatic (snapshot : Zkc.Source.Structured.Snapshot) (context : Context)
    (expected : Origin) (sites : List String) (template : Template) : Bool :=
  SourceOccurrences.valid snapshot context template &&
    (SourceOccurrences.repeatSites template == sites) &&
    (template.origin context == some expected) &&
    (template.entry == context.entry) &&
    (template.repeats == sites.length) &&
    template.steps.all (fun step => step.kind == "apply" || step.kind == "repeat")

/-- Static checking is exactly the dynamic resolver's test for all frames with
these ordered sites. Dynamic coordinates are neither guessed nor bounded. -/
theorem matchesOccurrence_eq_static (snapshot : Zkc.Source.Structured.Snapshot)
    (context : Context) (expected : Origin) (frames : Frames) (template : Template) :
    matchesOccurrence snapshot context expected frames template =
      matchesStatic snapshot context expected (frames.map (·.site)) template := by
  apply Bool.eq_iff_iff.mpr
  simp only [matchesOccurrence, matchesStatic, Bool.and_eq_true, beq_iff_eq,
    List.length_map]
  constructor
  · rintro ⟨⟨⟨valid, sites⟩, origin⟩, resolved⟩
    unfold Domain.templateOrigin at resolved
    split at resolved
    · rename_i shape
      exact ⟨⟨⟨⟨⟨valid, sites⟩, origin⟩, shape.1⟩, by simpa using shape.2.1⟩, shape.2.2⟩
    · cases resolved
  · rintro ⟨⟨⟨⟨⟨valid, sites⟩, origin⟩, entry⟩, count⟩, steps⟩
    refine ⟨⟨⟨valid, sites⟩, origin⟩, ?_⟩
    simp only [Domain.templateOrigin, entry, List.length_map, count, steps,
      and_self, ↓reduceIte, origin, Option.map_some]

/-- The unique candidate is checked once at the static loop/call interface.
Omitted and duplicate matching routes both fail. -/
def resolveStatic (snapshot : Zkc.Source.Structured.Snapshot) (context : Context)
    (expected : Origin) (sites : List String) (candidates : List Template) : Option Template :=
  match candidates.filter (matchesStatic snapshot context expected sites) with
  | [template] => some template
  | _ => none

/-- A finite passing route check supplies the existing resolver equation at
all runtime indices. The output is still the actual resolver's nominal key. -/
theorem resolve_of_static {snapshot : Zkc.Source.Structured.Snapshot} {context : Context}
    {expected : Origin} {sites : List String} {candidates : List Template} {template : Template}
    (checked : resolveStatic snapshot context expected sites candidates = some template)
    (frames : Frames) (sameSites : frames.map (·.site) = sites) :
    resolve snapshot context expected frames candidates =
      some (Domain.atCoordinates expected (frames.map (·.index))) := by
  have filtered : candidates.filter (matchesOccurrence snapshot context expected frames) =
      candidates.filter (matchesStatic snapshot context expected sites) := by
    apply List.filter_congr
    intro candidate _
    rw [matchesOccurrence_eq_static, sameSites]
  unfold resolve
  rw [filtered]
  unfold resolveStatic at checked
  split at checked
  · rename_i candidate found
    rw [found]
  · cases checked

/-- The same finite check also proves the target template's dynamic readback.
A certificate cannot use a different template after selecting its source key. -/
theorem template_of_static {snapshot : Zkc.Source.Structured.Snapshot} {context : Context}
    {expected : Origin} {sites : List String} {candidates : List Template} {template : Template}
    (checked : resolveStatic snapshot context expected sites candidates = some template)
    (frames : Frames) (sameSites : frames.map (·.site) = sites) :
    Domain.templateOrigin context template (frames.map (·.index)) =
      some (Domain.atCoordinates expected (frames.map (·.index))) := by
  have selected : matchesStatic snapshot context expected sites template = true := by
    unfold resolveStatic at checked
    split at checked
    · rename_i candidate found
      cases checked
      have member : template ∈ candidates.filter (matchesStatic snapshot context expected sites) := by
        rw [found]
        exact List.mem_singleton_self _
      exact (List.mem_filter.mp member).2
    · cases checked
  have matched : matchesOccurrence snapshot context expected frames template = true := by
    rw [matchesOccurrence_eq_static, sameSites]
    exact selected
  simp only [matchesOccurrence, Bool.and_eq_true, beq_iff_eq] at matched
  exact matched.2

end Zkc.Construction.OccurrenceResolution

namespace Zkc.Construction.Original

/-- Message routes need only the finite source/site check. The reached loop
indices, role endpoints and source history do not become instance lemmas. -/
theorem Routing.message_of_static {routing : Routing} {site : String} {sender receiver : Nat}
    {sites : List String} {template : Template}
    (checked : OccurrenceResolution.resolveStatic routing.snapshot routing.context
      (routing.context.message site sender receiver) sites routing.messages = some template)
    (frames : Frames) (sameSites : frames.map (·.site) = sites) :
    routing.message frames site sender receiver =
      some (Domain.atCoordinates (routing.context.message site sender receiver) (frames.map (·.index))) :=
  OccurrenceResolution.resolve_of_static checked frames sameSites

/-- The selected public service and its finite source route determine every
reached challenge origin; no theorem is needed for each iteration count. -/
theorem Routing.draw_of_static {routing : Routing} {site field : String}
    {sites : List String} {template : Template}
    (publicService : routing.context.service.isSome = true)
    (checked : OccurrenceResolution.resolveStatic routing.snapshot routing.context
      (routing.context.query site (.draw field)) sites routing.draws = some template)
    (frames : Frames) (sameSites : frames.map (·.site) = sites) :
    routing.draw frames site field routing.selectedHandle =
      some (Domain.atCoordinates (routing.context.query site (.draw field)) (frames.map (·.index))) := by
  simp only [Routing.draw, publicService, and_self, ↓reduceIte]
  exact OccurrenceResolution.resolve_of_static checked frames sameSites

end Zkc.Construction.Original
