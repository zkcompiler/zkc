module

public import Zkc.Construction.OriginalFold
public import Zkc.Source.Finite

@[expose] public section

/-! Coverage of the actual source effects, independent of a proposed route list.

Checking that every supplied template is valid is insufficient: an omitted
route could make the folded source refuse before the mismatched suffix. This
judgment covers every reached action, every typed reply and both sides of each
iteration boundary. It is indexed by the source process, never by the set of
routes a certificate happens to supply.
-/
set_option autoImplicit false
namespace Zkc.Construction.Original
open Zkc.Source
variable {carriers : Structured.Carriers} {A B : Type}

/-- The source participant represented by a construction route. -/
def Routing.self (routing : Routing) : Nat :=
  match routing.mode with
  | .producer => routing.context.producer
  | .validator => routing.context.validator

/-- A reached action has all the associations required by its fixed profile.
No action can become a successful refusal merely because discovery omitted it.
This is a structural precondition, not a randomness or cryptographic law. -/
def ActionCovered (routing : Routing) (frames : Frames) :
    (Structured.participantInterfaceOn carriers).Op → Prop
  | .receive ty site sender =>
      match routing.context.profile, routing.mode with
      | .fiatShamir _, .producer =>
          match ty with
          | .field field => ∃ draw message,
              routing.delivery frames site field sender = some (draw, message) ∧
              draw.request = some (.draw field)
          | _ => False
      | _, _ => ty.isHandle = false ∧
          ∃ origin, routing.message frames site sender routing.self = some origin
  | @Participant.Action.send _ _ _ _ ty site receiver _ =>
      ty.isHandle = false ∧
        ∃ origin, routing.message frames site routing.self receiver = some origin
  | .query site field (.cons handle .nil) =>
      (routing.mode = .validator ∧ ∃ origin,
        routing.draw frames site field handle = some origin ∧ origin.request = some (.draw field)) ∨
      (∃ port origin, routing.local frames site field handle = some (port, origin) ∧
        origin.request = some (.draw field))

/-- Complete reached-source coverage. Stops retain their reason and need no
unreachable suffix. Calls/repeats compose without unrolling runtime counts. -/
inductive RouteCoverage (routing : Routing) : Frames → Frames →
    PIR.Process (Structured.Occurrence.signature carriers) A → Type where
  | done (frames : Frames) (value : A) : RouteCoverage routing frames frames (.done value)
  | halt (frames final : Frames) (reason : PIR.Stop) :
      RouteCoverage routing frames final (.halt reason)
  | enter (frames final : Frames) (frame : Structured.Occurrence.Frame)
      {next : Unit → PIR.Process (Structured.Occurrence.signature carriers) A}
      (tail : RouteCoverage routing (frames ++ [frame]) final (next ())) :
      RouteCoverage routing frames final (.call (.enter frame) next)
  | leave (frames final : Frames) (frame : Structured.Occurrence.Frame)
      {next : Unit → PIR.Process (Structured.Occurrence.signature carriers) A}
      (last : frames.getLast? = some frame)
      (tail : RouteCoverage routing frames.dropLast final (next ())) :
      RouteCoverage routing frames final (.call (.leave frame) next)
  | action (frames final : Frames) (operation : (Structured.participantInterfaceOn carriers).Op)
      {next : (Structured.participantInterfaceOn carriers).Reply operation →
        PIR.Process (Structured.Occurrence.signature carriers) A}
      (covered : ActionCovered routing frames operation)
      (tail : ∀ reply, RouteCoverage routing frames final (next reply)) :
      RouteCoverage routing frames final (.call (.action operation) next)

noncomputable def RouteCoverage.bind {routing : Routing} {frames middle final : Frames}
    {source : PIR.Process (Structured.Occurrence.signature carriers) A}
    {next : A → PIR.Process (Structured.Occurrence.signature carriers) B}
    (head : RouteCoverage routing frames middle source)
    (tail : ∀ value, RouteCoverage routing middle final (next value)) :
    RouteCoverage routing frames final (source.bind next) := by
  induction head with
  | done => exact tail _
  | halt => exact .halt _ _ _
  | enter frames final frame head ih => exact .enter _ _ _ (ih tail)
  | leave frames final frame last head ih => exact .leave _ _ _ last (ih tail)
  | action frames final operation covered head ih =>
      exact .action _ _ _ covered fun reply => ih reply tail

noncomputable def RouteCoverage.finite {routing : Routing} {frames : Frames} {Item : Type}
    (step : A → Item → PIR.Process (Structured.Occurrence.signature carriers) A)
    (law : ∀ value item, RouteCoverage routing frames frames (step value item))
    (items : List Item) (initial : A) :
    RouteCoverage routing frames frames (Finite.fold step items initial) := by
  induction items generalizing initial with
  | nil => exact .done _ _
  | cons item rest ih => exact (law _ _).bind fun next => ih next

/-- One reusable rule wraps an arbitrary callback in its real dynamic source
coordinate. Nesting preserves order, even when indices happen to coincide. -/
noncomputable def RouteCoverage.within {routing : Routing} {frames : Frames}
    (site : String) (index : Nat)
    {source : PIR.Process (Structured.Occurrence.signature carriers) A}
    (body : RouteCoverage routing (frames ++ [⟨site, index⟩])
      (frames ++ [⟨site, index⟩]) source) :
    RouteCoverage routing frames frames (Structured.Occurrence.iterations.within site index source) := by
  simp only [Structured.IterationObservations.within_eq, Structured.Occurrence.iterations,
    Structured.IterationObservations.enter, Structured.IterationObservations.leave, PIR.Process.bind]
  apply RouteCoverage.enter
  apply body.bind
  intro value
  apply RouteCoverage.leave _ _ _ (by simp)
  simpa using RouteCoverage.done (carriers := carriers) (routing := routing) frames value

/-- The coverage judgment cannot certify a reached action without its route,
regardless of whether folding that action happens to refuse. -/
theorem RouteCoverage.action_required {routing : Routing} {frames final : Frames}
    {operation : (Structured.participantInterfaceOn carriers).Op}
    {next : (Structured.participantInterfaceOn carriers).Reply operation →
      PIR.Process (Structured.Occurrence.signature carriers) A}
    (covered : RouteCoverage routing frames final (.call (.action operation) next)) :
    ActionCovered routing frames operation := by
  cases covered with
  | action _ _ _ present _ => exact present

end Zkc.Construction.Original
