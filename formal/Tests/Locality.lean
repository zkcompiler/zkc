import Zkc.Semantics.Locality

set_option autoImplicit false

namespace Tests.Locality
open Zkc.Semantics.Locality Zkc.Semantics.AdaptiveClient
theorem private_choice_impossible :
    ¬ ∃ f : Unit → Bool, ∀ b : Bool, f () = b := by
  intro ⟨f, hf⟩
  have bad : false = true := (hf false).symm.trans (hf true)
  cases bad

theorem released_choice : ∃ f : Bool → Bool, ∀ b, f b = b := ⟨id, fun _ => rfl⟩

structure State where
  live : Nat
  dead : Nat
  deriving DecidableEq

def observeStep (_ : Unit) (s : State) : Nat × State := (s.live, s)
def liveRel (s t : State) : Prop := s.live = t.live

theorem observe_law (a : Unit) (s t : State) (h : liveRel s t) :
    (observeStep a s).1 = (observeStep a t).1 ∧
    liveRel (observeStep a s).2 (observeStep a t).2 := ⟨h,h⟩

def before (x : Nat) : State := ⟨x, x+1⟩
def after (x : Nat) : State := ⟨x, 0⟩
theorem deletion_live (x : Nat) : liveRel (before x) (after x) := rfl
theorem deletion_not_full (x : Nat) : before x ≠ after x := by
  intro h
  have hd := congrArg State.dead h
  exact Nat.noConfusion hd

theorem deletion_context (x : Nat) (c : Client Unit Nat) :
    (execClient observeStep c (before x)).1 =
    (execClient observeStep c (after x)).1 :=
  (adaptive_transport observeStep observeStep liveRel observe_law c _ _ (deletion_live x)).1

def hiddenEnabled (b : Bool) (a : Nat) : Bool :=
  if b then a == 1 || a == 2 else a == 0 || a == 1

theorem safe_common_output (b : Bool) : hiddenEnabled b 1 = true := by
  cases b <;> rfl

theorem no_exact_hidden_outputs :
    ¬ ∃ localEnabled : Unit → Nat → Bool,
      OutputExact (fun _ : Bool => ()) hiddenEnabled localEnabled := by
  intro ⟨f, h⟩
  have bad := output_necessary (fun _ : Bool => ()) hiddenEnabled f h false true rfl 0
  cases bad

theorem released_outputs : OutputExact id hiddenEnabled hiddenEnabled := by
  intro g a
  rfl

-- Same current output, different next visible memory: output-only checking
-- cannot justify continued execution. The hidden bit is deliberately released
-- by this transition, so the old view has no deterministic local update.
def memoryView (s : Bool × Bool) := s.1
def revealStep (_ : Unit) (s : Bool × Bool) : Unit × (Bool × Bool) :=
  ((), (s.2, s.2))

theorem current_output_agrees :
    (revealStep () (false,false)).1 = (revealStep () (false,true)).1 := rfl

theorem next_view_fails :
    ¬ FiberConstant memoryView (fun s => projectedResult memoryView (revealStep () s)) := by
  intro h
  have bad := congrArg Prod.snd (h (false,false) (false,true) rfl)
  cases bad

-- Receiving a discriminating message is different: it is an input, not an
-- unknown value that the local program has to choose.
def receiveStep (b : Bool) (_ : Unit) : Bool × Unit := (b, ())
theorem receive_preserves (b : Bool) : (receiveStep b ()).1 = b := rfl

-- Local marginals do not preserve a joint protocol relation.
def correlated (x y : Bool) : Prop := x = y
theorem every_left_locally_possible (x : Bool) : ∃ y, correlated x y := ⟨x,rfl⟩
theorem every_right_locally_possible (y : Bool) : ∃ x, correlated x y := ⟨y,rfl⟩
theorem product_adds_trace : ¬ correlated false true := by intro h; cases h


end Tests.Locality
