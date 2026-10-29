module

public import Zkc.Source.Structured.DomainParticipant
public import Zkc.Source.Structured.IterationObservations
public import Zkc.Semantics.Yields
public import Zkc.Source.Structured.RepeatLaws

@[expose] public section

/-! Presentation of a symbolic source loop from its callback law and a mask-stable
representation. Every iteration effect and arbitrary reply remains
in the process; no whole-loop equality or source simulation is an input. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.LoopPresentation
open Zkc.Source Zkc.Source.Structured


/-- Lift a callback representation through a bounded, effectful range. The
representation and invariant may depend on the reached index. Preservation
quantifies over every reply and does not assume that a stopped callback returns.
Only callback mathematics is supplied; the full-loop equation is derived here. -/
theorem foldInvariant {I : PIR.Signature} {A B : Type}
    (step : A → Nat → PIR.Process I A)
    (reference : B → Nat → PIR.Process I B)
    (embed : Nat → B → A) (invariant : Nat → B → Prop) (limit : Nat)
    (equation : ∀ index value, index < limit → invariant index value →
      step (embed index value) index =
        (reference value index).bind (fun next => .done (embed (index + 1) next)))
    (preserved : ∀ index value, index < limit → invariant index value →
      PIR.Yields (invariant (index + 1)) (reference value index))
    (index count : Nat) (bounded : index + count ≤ limit) (initial : B)
    (admitted : invariant index initial) :
    Finite.fold step (List.range' index count) (embed index initial) =
      (Finite.fold reference (List.range' index count) initial).bind
        (fun result => .done (embed (index + count) result)) := by
  induction count generalizing index initial with
  | zero => rfl
  | succ count ih =>
    rw [List.range'_succ, Finite.fold, equation index initial (by omega) admitted]
    simp only [PIR.Process.bind_assoc, PIR.Process.bind, Finite.fold]
    apply (preserved index initial (by omega) admitted).bind_congr
    intro next valid
    simpa only [Nat.add_assoc, Nat.add_comm 1 count] using
      ih (index + 1) (by omega) next valid

/-- A counted mathematical presentation is determined by its zero and successor
laws. This is a reusable bridge for references written by structural recursion;
source callbacks and occurrence observations remain in `step`. -/
theorem foldCounted {I : PIR.Signature} {S : Type}
    (step : S → Nat → PIR.Process I S)
    (reference : Nat → Nat → S → PIR.Process I S)
    (zero : ∀ index state, reference index 0 state = .done state)
    (succ : ∀ index count state, reference index (count + 1) state =
      (step state index).bind (reference (index + 1) count))
    (index count : Nat) (initial : S) :
    Finite.fold step (List.range' index count) initial = reference index count initial := by
  induction count generalizing index initial with
  | zero => exact (zero index initial).symm
  | succ count ih =>
    rw [List.range'_succ, Finite.fold, succ]
    apply congrArg (PIR.Process.bind _)
    funext next
    exact ih (index + 1) next

/-- Silent-loop specialization with complete role-local state and arbitrary replies. -/
theorem presentUniform {F G : Type} {I : PIR.Signature} (spec : RepeatSpec) (ctx : ProtocolContext) (self : Nat)
    (inside : (spec.roles.map ctx.roles).contains self = true)
    (captures : Values (Component (assignment F G)) spec.captures)
    (body : RegionFunction (Component (assignment F G)) I
      (.index :: (spec.state ++ spec.captures), spec.state))
    {S : Type} (embed : S → Values (Component (assignment F G)) spec.state)
    (masked : ∀ value, maskValues self (ctx.mapScopes spec.stateScopes) (embed value) = embed value)
    (process : S → Nat → PIR.Process I S)
    (equation : ∀ value index, body (.cons (some index) ((embed value).append captures)) =
      (process value index).bind (fun result => .done (embed result)))
    (count : Nat) (bounded : count ≤ spec.maximum)
    (state : Values (Component (assignment F G)) spec.state) (initial : S)
    (start : maskValues self (ctx.mapScopes spec.stateScopes) state = embed initial) :
    denoteRepeat spec ctx self (some count) state captures body =
      (Finite.fold process (List.range' 0 count) initial).bind (fun result => .done (embed result)) := by
  rw [repeat_admitted spec ctx self state captures body count inside bounded, start]
  apply Repeat.loop_embed
  intro value index
  rw [Repeat.step_equation, masked, equation, PIR.Process.bind_assoc]
  apply congrArg (PIR.Process.bind _)
  funext result
  simp only [PIR.Process.bind, masked]

theorem present {carriers : Carriers} {I : PIR.Signature} (spec : RepeatSpec) (ctx : ProtocolContext) (self : Nat)
    (inside : (spec.roles.map ctx.roles).contains self = true)
    (captures : Values (Component carriers.Value) spec.captures)
    (body : RegionFunction (Component carriers.Value) I
      (.index :: (spec.state ++ spec.captures), spec.state))
    (iterations : IterationObservations I) (site : String)
    {S : Type} (embed : S → Values (Component carriers.Value) spec.state)
    (masked : ∀ value, maskValues self (ctx.mapScopes spec.stateScopes) (embed value) = embed value)
    (process : S → Nat → PIR.Process I S)
    (equation : ∀ value index, body (.cons (some index) ((embed value).append captures)) =
      (process value index).bind (fun result => .done (embed result)))
    (count : Nat) (bounded : count ≤ spec.maximum)
    (state : Values (Component carriers.Value) spec.state) (initial : S)
    (start : maskValues self (ctx.mapScopes spec.stateScopes) state = embed initial) :
    denoteRepeatOn (carriers := carriers) spec ctx self (some count) state captures body iterations site =
      (Finite.fold (fun value index => iterations.within
        (qualifyProtocolSite ctx.applicationPrefix site) index (process value index))
        (List.range' 0 count) initial).bind (fun result => .done (embed result)) := by
  simp only [denoteRepeatOn, inside, bounded, ite_true, Finite.execute, Finite.Domain.admit,
    Finite.admitThen, List.range_eq_range', start]
  have fold (indices : List Nat) (value : S) :
      Finite.fold (fun state index => Repeat.stepOn spec ctx self captures body state index iterations site)
        indices (embed value) =
      (Finite.fold (fun value index => iterations.within
        (qualifyProtocolSite ctx.applicationPrefix site) index (process value index)) indices value).bind
        (fun result => .done (embed result)) := by
    induction indices generalizing value with
    | nil => rfl
    | cons index rest ih =>
      simp only [Finite.fold, Repeat.stepOn, masked, equation, IterationObservations.within_eq,
        PIR.Process.bind_assoc, PIR.Process.bind]
      apply congrArg (PIR.Process.bind _)
      funext _
      apply congrArg (PIR.Process.bind _)
      funext result
      apply congrArg (PIR.Process.bind _)
      funext _
      simpa only [Repeat.stepOn, IterationObservations.within_eq,
        PIR.Process.bind_assoc, PIR.Process.bind] using ih result
  exact fold _ initial

end Zkc.Source.Structured.LoopPresentation
