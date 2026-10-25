module

public import ZkcSecurity.Tools.ComponentDerivation

@[expose] public section

/-! Opaque components exercise composition independently of Sumcheck.
A false child suffices for conjunction, but not disjunction. A continuation's
contract must hold at every reached history, not just the initial history. -/
set_option autoImplicit false
namespace TestsSecurity.ComponentDerivation
open Zkc.Transcript Zkc.Obligations ZkcSecurity.Obligations
set_option maxRecDepth 5000
set_option maxHeartbeats 400000
noncomputable def composed {I : PIR.Signature} {E P : Type} {Raw : E → Type}
    [∀ event, SampleableType (Raw event)]
    (absorb : Interface I E P Raw) (charge : List E → E → ENNReal)
    (left right : PIR.Process I Bool) (history : List E) (LeftBad RightBad : Prop)
    (leftLaw : ∀ history, LeftBad → Derivation absorb (boundedEscape charge)
      (fun _ value => value = false) history left)
    (rightLaw : ∀ history, RightBad → Derivation absorb (boundedEscape charge)
      (fun _ value => value = false) history right)
    (wrong : LeftBad ∨ RightBad) :
    Derivation absorb (boundedEscape charge) (fun _ value => value = false) history
      (left.bind fun a => right.bind fun b => .done (a && b)) := by
  fail_if_success
    derive_component_rejection [] unfolding [] finishing simp_all
  fail_if_success
    have : Derivation absorb (boundedEscape charge) (fun _ value => value = false) history
        (left.bind fun a => right.bind fun b => .done (a || b)) := by
      derive_component_rejection [leftLaw, rightLaw] unfolding [] finishing simp_all
  fail_if_success
    have : Derivation absorb (boundedEscape charge) (fun _ value => value = false) history
        (left.bind fun a => right.bind fun b => .done (a && b)) := by
      derive_component_rejection [leftLaw, rightLaw history] unfolding [] finishing simp_all
  derive_component_rejection [leftLaw, rightLaw] unfolding [] finishing simp_all
/-- The structural tactic must not discard independent pending caller goals. -/
noncomputable def pending_goal {I : PIR.Signature} {E P : Type} {Raw : E → Type}
    [∀ event, SampleableType (Raw event)]
    (absorb : Interface I E P Raw) (charge : List E → E → ENNReal)
    (history : List E) :
    Derivation absorb (boundedEscape charge) (fun _ (value : Bool) => value = false)
      history (.done false) × Unit := by
  constructor
  derive_component_rejection [] unfolding [] finishing rfl
  exact ()

#print axioms composed
#print axioms pending_goal

end TestsSecurity.ComponentDerivation
