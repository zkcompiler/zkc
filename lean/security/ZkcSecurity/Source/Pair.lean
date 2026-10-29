module

public import ZkcSecurity.FiatShamir.HonestReadback
public import Zkc.Construction.OriginalEffects
public import Zkc.Construction.ConnectionRouting
public import Zkc.Source.Finite

@[expose] public section

/-! Successful pairing before artifact construction. This judgment relates the
existing occurrence processes; it does not execute a second source language.
The challenge rule fixes both continuations before an arbitrary common reply.
Interpretation laws retain the entire construction state, including history.
-/
set_option autoImplicit false
namespace ZkcSecurity.Source
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.FiatShamir

variable {carriers : Carriers} {A B C D : Type}

/-- The role and def-use associations selected by the source pair. This is
application data; it does not authorize a route or a probability law. -/
structure PairScope where
  producer : Nat
  validator : Nat
  deliveries : List (String × String)

/-- A source pair carries its mathematical residual, rather than requiring a
Boolean complement. There is deliberately no successful stopping constructor. -/
inductive Pair (scope : PairScope) (Post : A → B → Prop) :
    PIR.Process (Occurrence.signature carriers) A →
    PIR.Process (Occurrence.signature carriers) B → Prop where
  | done {left right} : Post left right → Pair scope Post (.done left) (.done right)
  | enter (frame : Occurrence.Frame) {left right} : Pair scope Post left right →
      Pair scope Post (.call (.enter frame) (fun _ => left)) (.call (.enter frame) (fun _ => right))
  | leave (frame : Occurrence.Frame) {left right} : Pair scope Post left right →
      Pair scope Post (.call (.leave frame) (fun _ => left)) (.call (.leave frame) (fun _ => right))
  | message (ty : Ty) (site : String) (producer validator : Nat) (value : carriers.Value ty)
      (data : ty.isService = false)
      {left : PIR.Process (Occurrence.signature carriers) A}
      {right : carriers.Value ty → PIR.Process (Occurrence.signature carriers) B} :
      (roles : producer = scope.producer ∧ validator = scope.validator) →
      Pair scope Post left (right value) →
      Pair scope Post
        (.call (.action (.send (ty := ty) site validator value)) (fun _ => left))
        (.call (.action (.receive ty site producer)) right)
  | challenge (field query delivery : String) (producer validator handle : Nat)
      {left : carriers.Field field → PIR.Process (Occurrence.signature carriers) A}
      {right : carriers.Field field → PIR.Process (Occurrence.signature carriers) B} :
      (roles : producer = scope.producer ∧ validator = scope.validator) →
      (deliveryOwned : (query, delivery) ∈ scope.deliveries) →
      (∀ reply, Pair scope Post (left reply) (right reply)) →
      Pair scope Post
        (.call (.action (.receive (.field field) delivery validator)) left)
        (.call (.action (.query query field (.cons handle .nil))) fun reply =>
          .call (.action (.send (ty := .field field) delivery producer reply)) fun _ => right reply)

namespace Pair
variable {scope : PairScope}

theorem bind {Post : A → B → Prop} {Final : C → D → Prop}
    {left : PIR.Process (Occurrence.signature carriers) A}
    {right : PIR.Process (Occurrence.signature carriers) B}
    (paired : Pair scope Post left right)
    (nextLeft : A → PIR.Process (Occurrence.signature carriers) C)
    (nextRight : B → PIR.Process (Occurrence.signature carriers) D)
    (next : ∀ a b, Post a b → Pair scope Final (nextLeft a) (nextRight b)) :
    Pair scope Final (left.bind nextLeft) (right.bind nextRight) := by
  induction paired with
  | done post => exact next _ _ post
  | enter frame _ ih => exact .enter frame ih
  | leave frame _ ih => exact .leave frame ih
  | message ty site producer validator value data roles _ ih =>
      exact .message ty site producer validator value data roles ih
  | challenge field query delivery producer validator handle roles owned _ ih =>
      exact .challenge field query delivery producer validator handle roles owned ih

theorem mono {Post Final : A → B → Prop}
    {left : PIR.Process (Occurrence.signature carriers) A}
    {right : PIR.Process (Occurrence.signature carriers) B}
    (paired : Pair scope Post left right) (law : ∀ a b, Post a b → Final a b) :
    Pair scope Final left right := by
  simpa only [PIR.Process.bind_done] using paired.bind PIR.Process.done PIR.Process.done
    (fun a b post => .done (law a b post))

/-- Both roles enter the same source occurrence. The dynamic index is ordinary
runtime data, independent of the static address of the body law. -/
theorem within {Post : A → B → Prop} (site : String) (index : Nat)
    {left : PIR.Process (Occurrence.signature carriers) A}
    {right : PIR.Process (Occurrence.signature carriers) B}
    (paired : Pair scope Post left right) :
    Pair scope Post (Occurrence.iterations.within site index left)
      (Occurrence.iterations.within site index right) := by
  simp only [IterationObservations.within_eq, Occurrence.iterations,
    IterationObservations.enter, IterationObservations.leave, PIR.Process.bind]
  exact .enter _ (paired.bind _ _ fun a b post => .leave _ (.done post))

/-- One relational invariant, including non-complement residuals and arbitrary
caller captures, composes over a symbolic source range. Every challenge is
shared before the next invariant is established; no independence is required. -/
theorem range (Invariant : Nat → A → B → Prop)
    (stepLeft : A → Nat → PIR.Process (Occurrence.signature carriers) A)
    (stepRight : B → Nat → PIR.Process (Occurrence.signature carriers) B)
    (step : ∀ n index a b, Invariant (n+1) a b →
      Pair scope (Invariant n) (stepLeft a index) (stepRight b index)) :
    ∀ count start a b, Invariant count a b →
      Pair scope (Invariant 0)
        (Finite.fold stepLeft (List.range' start count) a)
        (Finite.fold stepRight (List.range' start count) b) := by
  intro count
  induction count with
  | zero => intro start a b initial; exact .done initial
  | succ count ih =>
    intro start a b initial
    simp only [List.range'_succ, Finite.fold]
    exact (step count start a b initial).bind _ _ fun c d related => ih (start+1) c d related

/-- Interpret a paired operation with the same state on both sides. A property
installation must discharge these local laws for the reached source operations.
They are not consequences of validator WP success or of marginal distributions. -/
structure FoldLaws (scope : PairScope) (routingP routingV : Original.Routing) where
  message : ∀ (ty : Ty) site producer validator (value : carriers.Value ty) state,
    ty.isService = false →
    producer = scope.producer ∧ validator = scope.validator →
    Original.ActionCovered (carriers := carriers) routingP state.frames (.send (ty := ty) site validator value) →
    Original.ActionCovered (carriers := carriers) routingV state.frames (.receive ty site producer) →
    Readback (fun left right => right = (value, left.2) ∧ left.2.frames = state.frames)
      (Original.operations (carriers := carriers) routingP (.action (.send (ty := ty) site validator value)) state)
      (Original.operations (carriers := carriers) routingV (.action (.receive ty site producer)) state)
  challenge : ∀ field query delivery producer validator handle state,
    producer = scope.producer ∧ validator = scope.validator →
    (query, delivery) ∈ scope.deliveries →
    Original.ActionCovered (carriers := carriers) routingP state.frames (.receive (.field field) delivery validator) →
    Original.ActionCovered (carriers := carriers) routingV state.frames (.query query field (.cons handle .nil)) →
    (∀ value : carriers.Field field,
      Original.ActionCovered (carriers := carriers) routingV state.frames (.send (ty := .field field) delivery producer value)) →
    Readback (fun left right => left = right ∧ left.2.frames = state.frames)
      (Original.operations (carriers := carriers) routingP (.action (.receive (.field field) delivery validator)) state)
      ((Original.operations (carriers := carriers) routingV (.action (.query query field (.cons handle .nil))) state).bind
        fun (value, reached) =>
          (Original.operations (carriers := carriers) routingV (.action (.send (ty := .field field) delivery producer value)) reached).bind
            fun (_, final) => .done (value, final))

/-- Coverage comes from the generated connection, independently of this pair
proof. Missing routes cannot be hidden by a mutually refusing construction. -/
theorem fold {Post : A → B → Prop} {routingP routingV : Original.Routing}
    (laws : FoldLaws (carriers := carriers) scope routingP routingV)
    {left : PIR.Process (Occurrence.signature carriers) A}
    {right : PIR.Process (Occurrence.signature carriers) B}
    (paired : Pair scope Post left right) :
    ∀ (state : Original.State carriers) (finalP finalV : Original.Frames),
      Original.RouteCoverage routingP state.frames finalP left →
      Original.RouteCoverage routingV state.frames finalV right →
      Readback (fun p v => Post p.1 v.1 ∧ p.2 = v.2)
        (Original.fold routingP left state) (Original.fold routingV right state) := by
  induction paired with
  | done post => intros; exact .done ⟨post, rfl⟩
  | enter frame _ ih =>
    intro state finalP finalV coveredP coveredV
    cases coveredP with | enter _ _ _ tailP =>
      cases coveredV with | enter _ _ _ tailV =>
        exact ih ⟨state.frames ++ [frame], state.history⟩ finalP finalV tailP tailV
  | leave frame _ ih =>
    intro state finalP finalV coveredP coveredV
    cases coveredP with | leave _ _ _ lastP tailP =>
      cases coveredV with | leave _ _ _ _ tailV =>
        simp only [Original.fold, PIR.Process.interpretState, Original.operations, lastP, ↓reduceIte,
          PIR.Process.bind]
        exact ih ⟨state.frames.dropLast, state.history⟩ finalP finalV tailP tailV
  | message ty site producer validator value data roles _ ih =>
    intro state finalP finalV coveredP coveredV
    cases coveredP with | action _ _ _ actionP tailP =>
      cases coveredV with | action _ _ _ actionV tailV =>
        exact (laws.message ty site producer validator value state data roles actionP actionV).bind _ _ (by
          intro p v same
          obtain ⟨same, frames⟩ := same
          cases p with | mk ignored reached =>
            cases ignored
            subst v
            rw [← frames] at tailP tailV
            exact ih reached finalP finalV (tailP ()) (tailV value))
  | @challenge field query delivery producer validator handle leftNext rightNext roles owned _ ih =>
    intro state finalP finalV coveredP coveredV
    cases coveredP with | action _ _ _ actionP tailP =>
      cases coveredV with | action _ _ _ actionV tailV =>
        have sends : ∀ value : carriers.Field field, Original.ActionCovered (carriers := carriers) routingV state.frames
            (.send (ty := .field field) delivery producer value) :=
          fun value => (tailV value).action_required
        have pair := laws.challenge field query delivery producer validator handle state roles owned actionP actionV sends
        have installed := pair.bind
          (fun p => Original.fold routingP (leftNext p.1) p.2)
          (fun v => Original.fold routingV (rightNext v.1) v.2) (by
          intro p v same
          obtain ⟨same, frames⟩ := same
          subst v
          rw [← frames] at tailP tailV
          cases p with | mk value reached =>
            have continuation := tailV value
            cases continuation with | action _ _ _ _ tailSend =>
              exact ih value reached finalP finalV (tailP value) (tailSend ()))
        simpa only [Original.fold, PIR.Process.interpretState, PIR.Process.bind_assoc,
          PIR.Process.bind] using installed

end Pair
end ZkcSecurity.Source
