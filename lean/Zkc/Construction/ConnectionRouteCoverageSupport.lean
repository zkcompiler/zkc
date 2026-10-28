module

public import Zkc.Construction.ConnectionActionCoverage

@[expose] public section

/-! Coverage with a return invariant. This strengthens the existing source
judgment only at successful leaves, so continuations can use facts established
by the reached prefix. It does not inspect the folded computation. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionRouteCoverage
open Zkc.Source Zkc.Source.Structured
variable {carriers : Carriers} {A B : Type}

inductive Covered (routing : Original.Routing) (post : A → Prop) :
    Original.Frames → Original.Frames → PIR.Process (Occurrence.signature carriers) A → Type where
  | done (frames : Original.Frames) (value : A) (holds : post value) :
      Covered routing post frames frames (.done value)
  | halt (frames final : Original.Frames) (reason : PIR.Stop) :
      Covered routing post frames final (.halt reason)
  | enter (frames final : Original.Frames) (frame : Occurrence.Frame)
      {next : Unit → PIR.Process (Occurrence.signature carriers) A}
      (tail : Covered routing post (frames ++ [frame]) final (next ())) :
      Covered routing post frames final (.call (.enter frame) next)
  | leave (frames final : Original.Frames) (frame : Occurrence.Frame)
      {next : Unit → PIR.Process (Occurrence.signature carriers) A}
      (last : frames.getLast? = some frame)
      (tail : Covered routing post frames.dropLast final (next ())) :
      Covered routing post frames final (.call (.leave frame) next)
  | action (frames final : Original.Frames) (operation : (participantInterfaceOn carriers).Op)
      {next : (participantInterfaceOn carriers).Reply operation → PIR.Process (Occurrence.signature carriers) A}
      (covered : Original.ActionCovered routing frames operation)
      (tail : ∀ reply, Covered routing post frames final (next reply)) :
      Covered routing post frames final (.call (.action operation) next)

noncomputable def Covered.coverage {routing : Original.Routing} {post : A → Prop}
    {frames final : Original.Frames} {source : PIR.Process (Occurrence.signature carriers) A}
    (proof : Covered routing post frames final source) : Original.RouteCoverage routing frames final source := by
  induction proof with
  | done => exact .done _ _
  | halt => exact .halt _ _ _
  | enter _ _ _ _ ih => exact .enter _ _ _ ih
  | leave _ _ _ last _ ih => exact .leave _ _ _ last ih
  | action _ _ _ checked _ ih => exact .action _ _ _ checked ih

noncomputable def Covered.bind {routing : Original.Routing} {pre : A → Prop} {post : B → Prop}
    {frames middle final : Original.Frames} {source : PIR.Process (Occurrence.signature carriers) A}
    {next : A → PIR.Process (Occurrence.signature carriers) B}
    (head : Covered routing pre frames middle source)
    (tail : ∀ value, pre value → Covered routing post middle final (next value)) :
    Covered routing post frames final (source.bind next) := by
  induction head with
  | done _ value holds => exact tail value holds
  | halt => exact .halt _ _ _
  | enter _ _ _ _ ih => exact .enter _ _ _ (ih tail)
  | leave _ _ _ last _ ih => exact .leave _ _ _ last (ih tail)
  | action _ _ _ checked _ ih => exact .action _ _ _ checked fun reply => ih reply tail

noncomputable def Covered.mapPost {routing : Original.Routing} {pre post : A → Prop}
    {frames final : Original.Frames} {source : PIR.Process (Occurrence.signature carriers) A}
    (proof : Covered routing pre frames final source) (law : ∀ value, pre value → post value) :
    Covered routing post frames final source := by
  induction proof with
  | done _ value holds => exact .done _ _ (law value holds)
  | halt => exact .halt _ _ _
  | enter _ _ _ _ ih => exact .enter _ _ _ ih
  | leave _ _ _ last _ ih => exact .leave _ _ _ last ih
  | action _ _ _ checked _ ih => exact .action _ _ _ checked ih

noncomputable def Covered.closedBind {routing : Original.Routing} {post : B → Prop}
    {frames final : Original.Frames} (source : PIR.Process closedInterface A)
    (next : A → PIR.Process (Occurrence.signature carriers) B)
    (tail : ∀ value, Covered routing post frames final (next value)) :
    Covered routing post frames final
      ((source.interpret (closedLift (I := Occurrence.signature carriers))).bind next) := by
  cases source with
  | done value => exact tail value
  | halt reason => exact .halt _ _ _
  | call operation _ => exact nomatch operation

noncomputable def Covered.finite {routing : Original.Routing} {post : A → Prop}
    {frames : Original.Frames} {Item : Type}
    (step : A → Item → PIR.Process (Occurrence.signature carriers) A)
    (law : ∀ value, post value → ∀ item, Covered routing post frames frames (step value item))
    (items : List Item) (initial : A) (holds : post initial) :
    Covered routing post frames frames (Finite.fold step items initial) := by
  induction items generalizing initial with
  | nil => exact .done _ _ holds
  | cons item rest ih => exact (law initial holds item).bind fun value next => ih value next

noncomputable def Covered.within {routing : Original.Routing} {post : A → Prop}
    {frames : Original.Frames} (site : String) (index : Nat)
    {source : PIR.Process (Occurrence.signature carriers) A}
    (body : Covered routing post (frames ++ [⟨site,index⟩]) (frames ++ [⟨site,index⟩]) source) :
    Covered routing post frames frames (Occurrence.iterations.within site index source) := by
  simp only [IterationObservations.within_eq, Occurrence.iterations, IterationObservations.enter,
    IterationObservations.leave, PIR.Process.bind]
  apply Covered.enter
  apply body.bind
  intro value holds
  apply Covered.leave _ _ _ (by simp)
  simpa using Covered.done (carriers := carriers) (routing := routing) frames value holds

end Zkc.Construction.ConnectionRouteCoverage
