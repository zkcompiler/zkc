module

public import Zkc.Construction.ConnectionStaticRoutes
public import Zkc.Construction.ConnectionRouting

@[expose] public section

/-! Source action coverage follows from finite source/profile route checks.
These facts do not use simulation: refusing both computations cannot discharge
a missing route. Dynamic coordinates stay arbitrary and ordered. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionActionCoverage
open Zkc.Source Zkc.Source.Structured

variable {carriers : Carriers} {routing : Original.Routing} {frames : Original.Frames}
  {sites : List String} {site field : String} {template : Template}

/-- A plain receive needs its exact source-owned message route. -/
theorem receivePlain (ty : Ty) (sender : Nat)
    (profile : routing.context.profile = .plain) (data : ty.isHandle = false)
    (same : frames.map (·.site) = sites)
    (route : OccurrenceResolution.resolveStatic routing.snapshot routing.context
      (routing.context.message site sender routing.self) sites routing.messages = some template) :
    Original.ActionCovered routing frames
      (.receive ty site sender : (participantInterfaceOn carriers).Op) := by
  have found := OccurrenceResolution.resolve_of_static route frames same
  cases mode : routing.mode <;>
    simpa only [Original.ActionCovered, profile, mode, Original.Routing.message] using
      And.intro data ⟨_, found⟩

/-- The validator's FS receive records the same source-owned message. -/
theorem receiveValidator (ty : Ty) (sender : Nat)
    (mode : routing.mode = .validator) (data : ty.isHandle = false)
    (same : frames.map (·.site) = sites)
    (route : OccurrenceResolution.resolveStatic routing.snapshot routing.context
      (routing.context.message site sender routing.self) sites routing.messages = some template) :
    Original.ActionCovered routing frames
      (.receive ty site sender : (participantInterfaceOn carriers).Op) := by
  have found := OccurrenceResolution.resolve_of_static route frames same
  cases profile : routing.context.profile <;>
    simpa only [Original.ActionCovered, profile, mode, Original.Routing.message] using
      And.intro data ⟨_, found⟩

/-- Sending remains a data action in either execution profile. -/
theorem send (ty : Ty) (receiver : Nat) (value : carriers.Value ty)
    (data : ty.isHandle = false) (same : frames.map (·.site) = sites)
    (route : OccurrenceResolution.resolveStatic routing.snapshot routing.context
      (routing.context.message site routing.self receiver) sites routing.messages = some template) :
    Original.ActionCovered routing frames (.send (ty := ty) site receiver value) :=
  ⟨data, _, OccurrenceResolution.resolve_of_static route frames same⟩

/-- Public challenges retain the selected capability and nominal request. -/
theorem publicQuery (handle : Nat) (selected : handle = routing.selectedHandle)
    (mode : routing.mode = .validator) (service : routing.context.service.isSome = true)
    (same : frames.map (·.site) = sites)
    (route : OccurrenceResolution.resolveStatic routing.snapshot routing.context
      (routing.context.query site (.draw field)) sites routing.draws = some template) :
    Original.ActionCovered routing frames
      (.query site field (.cons handle .nil) : (participantInterfaceOn carriers).Op) := by
  have found : routing.draw frames site field handle = some
      (Domain.atCoordinates (routing.context.query site (.draw field)) (frames.map (·.index))) := by
    simp only [Original.Routing.draw, selected, service, and_self, ↓reduceIte]
    exact OccurrenceResolution.resolve_of_static route frames same
  exact Or.inl ⟨mode, _, found, Original.Routing.draw_request found⟩

/-- Private services cannot acquire public authority through this rule. -/
theorem localQuery (handle : Nat) (port : ServicePort)
    (binding : ConnectionStaticRoutes.Local routing sites site field handle port template)
    (same : frames.map (·.site) = sites) :
    Original.ActionCovered routing frames
      (.query site field (.cons handle .nil) : (participantInterfaceOn carriers).Op) := by
  refine Or.inr ⟨port, _, binding.source frames same, ?_⟩
  rw [OccurrenceResolution.atCoordinates_request]
  rfl

/-- A producer's replacement challenge requires the original def-use delivery. -/
theorem delivery (sender : Nat) (draw message : Template)
    (replacement : Replacement) (profile : routing.context.profile = .fiatShamir replacement)
    (mode : routing.mode = .producer)
    (binding : ConnectionStaticRoutes.Delivery routing sites site field sender draw message)
    (same : frames.map (·.site) = sites) :
    Original.ActionCovered routing frames
      (.receive (.field field) site sender : (participantInterfaceOn carriers).Op) := by
  simp only [Original.ActionCovered, profile, mode]
  refine ⟨_, _, binding.source frames same, ?_⟩
  rw [OccurrenceResolution.atCoordinates_request]
  rfl

/-- Closed helper computations can stop but cannot introduce an uncovered
source action. Every result and every stop remains in the existing meaning. -/
noncomputable def closed {A : Type} (routing : Original.Routing) (frames : Original.Frames)
    (process : PIR.Process closedInterface A) :
    Original.RouteCoverage (carriers := carriers) routing frames frames
      (process.interpret (closedLift (I := Occurrence.signature carriers))) := by
  cases process with
  | done value => exact .done _ _
  | halt reason => exact .halt _ _ _
  | call operation _ => exact nomatch operation

end Zkc.Construction.ConnectionActionCoverage
