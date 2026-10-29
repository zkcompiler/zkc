module

public import ZkcSecurity.Source.PublicProperties
public import Zkc.Obligations.FrameComposition

@[expose] public section

/-! Structural property rules at occurrence boundaries. A stopped erasure
certificate can discharge safety and zero cost only: it cannot establish a
successful pair. Every source enter/leave is retained in the derivation. -/
set_option autoImplicit false
namespace ZkcSecurity.Source.OccurrenceProperties
open Zkc.Source Zkc.Source.Structured Zkc.Obligations Zkc.Transcript
open ZkcSecurity.FiatShamir
variable {carriers : Carriers} {A : Type}
  {escape : EscapeJudgment (PublicProperties.Event carriers) PublicProperties.Raw}
  {post : A → Prop}

def within (site : String) (index : Nat)
    (source : PIR.Process (Occurrence.signature carriers) A)
    (proof : ∀ history, Derivation PublicProperties.interface escape (fun _ => post) history source)
    (history : List (PublicProperties.Event carriers)) :
    Derivation PublicProperties.interface escape (fun _ => post) history
      (Occurrence.iterations.within site index source) := by
  simp only [IterationObservations.within_eq, Occurrence.iterations,
    IterationObservations.enter, IterationObservations.leave, PIR.Process.bind]
  exact .send rfl ((proof _).bind _ (fun reached value holds => .send rfl (.done holds)))

theorem within_cost (price budget : ENNReal) (site : String) (index : Nat)
    (source : PIR.Process (Occurrence.signature carriers) A)
    (bounded : ∀ history, Typed.ChargedCostBound PublicProperties.interface (fun _ _ => price)
      source history budget) (history : List (PublicProperties.Event carriers)) :
    Typed.ChargedCostBound PublicProperties.interface (fun _ _ => price)
      (Occurrence.iterations.within site index source) history budget := by
  simp only [IterationObservations.within_eq, Occurrence.iterations,
    IterationObservations.enter, IterationObservations.leave, PIR.Process.bind]
  change Typed.ChargedCostBound PublicProperties.interface (fun _ _ => price)
    (source.bind fun value => .call (.leave ⟨site,index⟩) (fun _ => .done value)) _ budget
  simpa only [add_zero] using CostComposition.bind source
    (fun value => .call (.leave ⟨site,index⟩) (fun _ => .done value)) budget 0
    (bounded _) (fun _ _ => trivial)

noncomputable def stopped (source : PIR.Process (Occurrence.signature carriers) A) (reason : PIR.Stop)
    (stops : source.interpret Occurrence.erase = .halt reason)
    (history : List (PublicProperties.Event carriers)) :
    Derivation PublicProperties.interface escape (fun _ => post) history source := by
  induction source generalizing history with
  | done value => cases stops
  | halt stop => exact .halt stop
  | call operation next ih =>
    cases operation with
    | enter frame => exact .send rfl (ih () stops _)
    | leave frame => exact .send rfl (ih () stops _)
    | action action => cases stops

theorem stopped_cost (source : PIR.Process (Occurrence.signature carriers) A) (reason : PIR.Stop)
    (stops : source.interpret Occurrence.erase = .halt reason) (price budget : ENNReal)
    (history : List (PublicProperties.Event carriers)) :
    Typed.ChargedCostBound PublicProperties.interface (fun _ _ => price) source history budget := by
  induction source generalizing history with
  | done value => cases stops
  | halt stop => trivial
  | call operation next ih =>
    cases operation with
    | enter frame => exact ih () stops _
    | leave frame => exact ih () stops _
    | action action => cases stops

end ZkcSecurity.Source.OccurrenceProperties
