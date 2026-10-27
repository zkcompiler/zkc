module

public import Zkc.Construction.OriginProjection
public import Zkc.Executable.DomainNativeRelation

@[expose] public section

/-! The existing scalar native oracle uses the six static fields of a message
or query occurrence. Domain retains the dynamic coordinates in its own state;
this named handler map projects them before invoking that oracle. This is not
an identification with a nominal random-oracle game. Template eligibility is
stated as structural header, path-kind and coordinate-depth facts. -/
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source Zkc.Construction.Uniform

theorem template_origin_length (context : Context) (template : Template) (origin : Origin)
    (found : template.origin context = some origin) : origin.event.length = 6 := by
  unfold Template.origin at found
  split at found
  · split at found
    · cases found; rfl
    · cases found
  · cases asked : context.request with
    | none => simp [asked] at found
    | some request =>
        simp [asked] at found
        subst origin
        rfl
  · cases found

/-- These are actual artifact-shape facts. Coordinate values themselves are
arbitrary and are never required to satisfy a numerical relation. -/
theorem templateOrigin_native (context : Context) (template : Template) (coordinates : List Nat)
    (entry : template.entry = context.entry)
    (depth : template.repeats = coordinates.length)
    (kinds : template.steps.all (fun step => step.kind == "apply" || step.kind == "repeat") = true) :
    (Domain.templateOrigin context template coordinates).map Origin.withoutCoordinates = template.origin context := by
  simp only [Domain.templateOrigin, entry, depth, kinds, and_self, ite_true]
  cases found : template.origin context with
  | none => rfl
  | some origin =>
      simp only [Option.map_some]
      exact congrArg some (Origin.withoutCoordinates_atCoordinates origin coordinates
        (template_origin_length context template origin found))

/-- Query admission fixes the suite, request and root service before the
handler sees a reply. Dynamic path depth is a separate checked scope fact. -/
theorem queryOrigin_scoped (context : Context) (suite field : String) (template : Template)
    (coordinates : List Nat) (localEntry site port contract owner : String)
    (entry : template.entry = context.entry)
    (depth : template.repeats = coordinates.length)
    (kinds : template.steps.all (fun step => step.kind == "apply" || step.kind == "repeat") = true)
    (suiteEq : suite = context.suite) (contractEq : context.contract = "random." ++ field ++ "/0")
    (request : context.request = some (.draw field))
    (event : template.event = ["query", localEntry, site, port, contract, "draw", owner]) :
    Domain.queryOrigin context suite field template coordinates =
      some (Domain.atCoordinates (context.query (template.qualify site) (.draw field)) coordinates) := by
  simp only [Domain.queryOrigin, suiteEq, contractEq, request, and_self, ite_true,
    Domain.templateOrigin, entry, depth, kinds, Template.origin, event, Option.map_some]
  have actual : (Domain.atCoordinates (context.query (template.qualify site) (.draw field)) coordinates).request =
      some (.draw field) := by
    simp only [Domain.atCoordinates]
    split <;> rfl
  simp only [actual, ite_true]

/-- Message admission uses the source site as its schema, independently of
its payload. The dynamic suffix remains in the nominal occurrence. -/
theorem messageOrigin_scoped (context : Context) (template : Template) (coordinates : List Nat)
    (localEntry site sender receiver : String) (entry : template.entry = context.entry)
    (depth : template.repeats = coordinates.length)
    (kinds : template.steps.all (fun step => step.kind == "apply" || step.kind == "repeat") = true)
    (event : template.event = ["message", localEntry, site, site, sender, receiver]) :
    Domain.templateOrigin context template coordinates =
      some (Domain.atCoordinates (Origin.message context.entry (template.qualify site) sender receiver)
        coordinates) := by
  simp only [Domain.templateOrigin, entry, depth, kinds, Template.origin, event,
    and_self, ite_true, Option.map_some]

variable {F G : Type} {m : Type → Type} [Monad m]

theorem mapped_message (history : Domain.History (Structured.uniformCarriers F G))
    (suffix : History F G) (origin : Origin) (coordinates : List Nat) (payload : Payload F G)
    (static : origin.event.length = 6)
    (mapped : DomainAdapter.readbackHistory Origin.withoutCoordinates history = some suffix) :
    DomainAdapter.readbackHistory Origin.withoutCoordinates
      (history ++ [.message (Domain.atCoordinates origin coordinates) (DomainAdapter.embedPayload payload)]) =
        some (suffix ++ [.message origin payload]) := by
  rw [DomainAdapter.readbackHistory_append, mapped]
  simp only [DomainAdapter.readbackHistory, List.mapM_cons, List.mapM_nil,
    DomainAdapter.readbackEvent, Origin.withoutCoordinates_atCoordinates origin coordinates static,
    DomainAdapter.readbackPayload_embed]
  rfl

theorem mapped_challenge (history : Domain.History (Structured.uniformCarriers F G))
    (suffix : History F G) (origin : Origin) (coordinates : List Nat) (static : origin.event.length = 6)
    (mapped : DomainAdapter.readbackHistory Origin.withoutCoordinates history = some suffix) :
    DomainAdapter.readbackHistory Origin.withoutCoordinates
      (history ++ [.challenge (Domain.atCoordinates origin coordinates)]) =
        some (suffix ++ [.challenge origin]) := by
  rw [DomainAdapter.readbackHistory_append, mapped]
  simp only [DomainAdapter.readbackHistory, List.mapM_cons, List.mapM_nil,
    DomainAdapter.readbackEvent, Origin.withoutCoordinates_atCoordinates origin coordinates static]
  rfl

/-- The oracle is called at the native key, after the map, with its opaque
initial history and the entire mapped execution suffix. -/
theorem query_native (initial : History F G) (challenge : History F G → m F)
    (history : Domain.History (Structured.uniformCarriers F G)) (origin : Origin)
    (coordinates : List Nat) (field : String) (suffix : History F G)
    (static : origin.event.length = 6) (request : origin.request = some (.draw field))
    (mapped : DomainAdapter.readbackHistory Origin.withoutCoordinates history = some suffix) :
    DomainAdapter.query Origin.withoutCoordinates initial challenge history (Domain.atCoordinates origin coordinates) = (do
      let answer ← challenge (initial ++ suffix ++ [.challenge origin])
      pure (.returned (show Domain.Raw (.challenge (Domain.atCoordinates origin coordinates) :
        Domain.Event (Structured.uniformCarriers F G)) from by
          have actual : (Domain.atCoordinates origin coordinates).request = some (.draw field) := by
            simp only [Domain.atCoordinates]; split <;> exact request
          simpa only [Domain.Raw, actual, Request.draw] using answer))) := by
  have actual : (Domain.atCoordinates origin coordinates).request = some (.draw field) := by
    simp only [Domain.atCoordinates]; split <;> exact request
  rw [DomainAdapter.query_of_draw Origin.withoutCoordinates initial challenge history _ field actual suffix mapped]
  simp only [Origin.withoutCoordinates_atCoordinates origin coordinates static]

end Zkc.Executable.DomainVM
