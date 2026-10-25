module

public import Zkc.Semantics.Interaction
public import Zkc.Semantics.Interpretation
public import Mathlib.Order.Basic

public section

/-! Structural readings of the existing open process. The algebra receives a
reading for every typed reply. Monotonicity is an explicit algebra law; it is
not a claim that every reading combines replies by conjunction.

The `PIR.ProcessSimp` scope is opt-in. It normalizes notation and fold equations,
without globally expanding `Process.bind` into matches.
-/

set_option autoImplicit false
universe u

namespace PIR.Process
variable {I : Signature} {A B : Type} {L : Type u}

@[expose] def foldReplies (leaf : A → L) (stop : Stop → L)
    (node : (operation : I.Op) → (I.Reply operation → L) → L) : Process I A → L
  | .done value => leaf value
  | .halt reason => stop reason
  | .call operation next => node operation fun reply => foldReplies leaf stop node (next reply)

theorem foldReplies_done (leaf : A → L) (stop : Stop → L)
    (node : (operation : I.Op) → (I.Reply operation → L) → L) (value : A) :
    (Process.done value : Process I A).foldReplies leaf stop node = leaf value := rfl

theorem foldReplies_halt (leaf : A → L) (stop : Stop → L)
    (node : (operation : I.Op) → (I.Reply operation → L) → L) (reason : Stop) :
    (Process.halt reason : Process I A).foldReplies leaf stop node = stop reason := rfl

theorem foldReplies_call (leaf : A → L) (stop : Stop → L)
    (node : (operation : I.Op) → (I.Reply operation → L) → L) (operation : I.Op)
    (next : I.Reply operation → Process I A) :
    (Process.call operation next).foldReplies leaf stop node =
      node operation (fun reply => (next reply).foldReplies leaf stop node) := rfl

theorem foldReplies_bind (leaf : B → L) (stop : Stop → L)
    (node : (operation : I.Op) → (I.Reply operation → L) → L) (process : Process I A)
    (next : A → Process I B) :
    (process.bind next).foldReplies leaf stop node =
      process.foldReplies (fun value => (next value).foldReplies leaf stop node) stop node := by
  induction process with
  | done value => rfl
  | halt reason => rfl
  | call operation continuation ih => simp only [Process.bind, foldReplies, ih]

@[expose] def MonotoneNode [Preorder L] (node : (operation : I.Op) → (I.Reply operation → L) → L) : Prop :=
  ∀ operation ⦃lower upper : I.Reply operation → L⦄,
    (∀ reply, lower reply ≤ upper reply) → node operation lower ≤ node operation upper

theorem foldReplies_mono [Preorder L] {node : (operation : I.Op) → (I.Reply operation → L) → L}
    (monotone : MonotoneNode node) {leaf leaf' : A → L} {stop stop' : Stop → L}
    (leafLe : ∀ value, leaf value ≤ leaf' value) (stopLe : ∀ reason, stop reason ≤ stop' reason) :
    ∀ process : Process I A,
      process.foldReplies leaf stop node ≤ process.foldReplies leaf' stop' node
  | .done value => leafLe value
  | .halt reason => stopLe reason
  | .call operation next =>
      monotone operation fun reply => foldReplies_mono monotone leafLe stopLe (next reply)

/-- A set closed under the node algebra lies inside its structural reading. -/
theorem le_foldReplies [Preorder L] {leaf : A → L} {stop : Stop → L}
    {node : (operation : I.Op) → (I.Reply operation → L) → L} (monotone : MonotoneNode node)
    (bound : Process I A → L) (atDone : ∀ value, bound (.done value) ≤ leaf value)
    (atHalt : ∀ reason, bound (.halt reason) ≤ stop reason)
    (atCall : ∀ operation next,
      bound (.call operation next) ≤ node operation (fun reply => bound (next reply))) :
    ∀ process : Process I A, bound process ≤ process.foldReplies leaf stop node
  | .done value => atDone value
  | .halt reason => atHalt reason
  | .call operation next =>
      (atCall operation next).trans (monotone operation fun reply =>
        le_foldReplies monotone bound atDone atHalt atCall (next reply))

theorem foldReplies_interpret {J : Signature} (operations : OperationInterpretation I J)
    (leaf : A → L) (stop : Stop → L) (node : (operation : J.Op) → (J.Reply operation → L) → L)
    (process : Process I A) :
    (process.interpret operations).foldReplies leaf stop node =
      process.foldReplies leaf stop
        (fun operation next => (operations operation).foldReplies next stop node) := by
  induction process with
  | done value => rfl
  | halt reason => rfl
  | call operation next ih =>
      simp only [interpret, foldReplies_call]
      rw [foldReplies_bind]
      simp only [ih]

theorem foldReplies_repeatN_zero (leaf : A → L) (stop : Stop → L)
    (node : (operation : I.Op) → (I.Reply operation → L) → L)
    (step : A → Process I A) (value : A) :
    (PIR.repeatN 0 step value).foldReplies leaf stop node = leaf value := rfl

theorem foldReplies_repeatN_succ (leaf : A → L) (stop : Stop → L)
    (node : (operation : I.Op) → (I.Reply operation → L) → L) (count : Nat)
    (step : A → Process I A) (value : A) :
    (PIR.repeatN (count + 1) step value).foldReplies leaf stop node =
      (step value).foldReplies (fun next => (PIR.repeatN count step next).foldReplies leaf stop node)
        stop node :=
  foldReplies_bind leaf stop node (step value) (PIR.repeatN count step)

/-- Remaining-count invariants include a separately supplied zero leaf. -/
theorem le_foldReplies_repeatN [Preorder L] {stop : Stop → L}
    {node : (operation : I.Op) → (I.Reply operation → L) → L} (monotone : MonotoneNode node)
    (step : A → Process I A) (invariant : Nat → A → L)
    (preserved : ∀ remaining value,
      invariant (remaining + 1) value ≤ (step value).foldReplies (invariant remaining) stop node) :
    ∀ count value,
      invariant count value ≤ (PIR.repeatN count step value).foldReplies (invariant 0) stop node
  | 0, _ => le_rfl
  | count + 1, value => by
      rw [foldReplies_repeatN_succ]
      exact (preserved count value).trans
        (foldReplies_mono monotone
          (fun next => le_foldReplies_repeatN monotone step invariant preserved count next)
          (fun _ => le_rfl) (step value))

theorem bind_notation (process : Process I A) (next : A → Process I B) :
    (process >>= next) = process.bind next := rfl

theorem pure_notation (value : A) :
    (pure value : Process I A) = .done value := rfl

end PIR.Process

namespace PIR.ProcessSimp
attribute [scoped simp] Process.foldReplies_done Process.foldReplies_halt Process.foldReplies_call
  Process.foldReplies_bind Process.foldReplies_repeatN_zero Process.bind_notation Process.pure_notation
  Process.bind_assoc Process.bind_done
end PIR.ProcessSimp
