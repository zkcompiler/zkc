module

public meta import ZkcSecurity.Tools.ComponentReadback
public import Zkc.Construction.DomainCalculations

@[expose] public section
set_option autoImplicit false
-- Callback hooks are deliberately unused in the refusal/terminal controls.
-- Negative tactic controls deliberately supply callbacks that must remain unexecuted.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
namespace TestsSecurity.ComponentReadback
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcSecurity.FiatShamir

variable {carriers : Carriers}

/-- Keep the installed component opaque to the structural composer. -/
@[irreducible] def component (x : Nat × Bool) :
    PIR.Process (Domain.effects carriers) (Nat × Bool) :=
  .call (.checkpoint []) (fun _ => .done x)

private theorem step (x : Nat × Bool) (Post : (Nat × Bool) → (Nat × Bool) → Prop)
    (nextLeft nextRight : (Nat × Bool) → PIR.Process (Domain.effects carriers) (Nat × Bool))
    (next : ∀ value, value = x → Readback Post (nextLeft value) (nextRight value)) :
    Readback Post ((component x).bind nextLeft) ((component x).bind nextRight) := by
  unfold component
  exact .checkpointLeft [] (.checkpointRight [] (next x rfl))

example (x : Nat × Bool) :
    Readback (fun left right : Nat × Bool => left = x ∧ right = x)
      ((component x : PIR.Process (Domain.effects carriers) _).bind fun value => .done value)
      ((component x).bind fun value => .done value) := by
  compose_component_readback [step]
    normalizing (try simp_all only [])
    solving assumption
    finishing (constructor <;> first | assumption | rfl)

private theorem requiringPremise (required : Prop) (_proof : required)
    (x : Nat × Bool) (Post : (Nat × Bool) → (Nat × Bool) → Prop)
    (nextLeft nextRight : (Nat × Bool) → PIR.Process (Domain.effects carriers) (Nat × Bool))
    (next : ∀ value, value = x → Readback Post (nextLeft value) (nextRight value)) :
    Readback Post ((component x).bind nextLeft) ((component x).bind nextRight) :=
  step x Post nextLeft nextRight next

-- A component's unproved side premise cannot disappear during composition.
example (x : Nat × Bool) : True := by
  fail_if_success
    have : Readback (fun left right : Nat × Bool => left = right)
        ((component x : PIR.Process (Domain.effects carriers) _).bind fun value => .done value)
        ((component x).bind fun value => .done value) := by
      compose_component_readback [requiringPremise False]
        normalizing skip solving assumption finishing rfl
  trivial

-- Without the installed rule, the opaque component remains an obligation.
example (x : Nat × Bool) : True := by
  fail_if_success
    have : Readback (fun left right : Nat × Bool => left = right)
        ((component x : PIR.Process (Domain.effects carriers) _).bind fun value => .done value)
        ((component x).bind fun value => .done value) := by
      compose_component_readback [] normalizing skip solving assumption finishing rfl
  trivial

example (x : Nat × Bool) :
    Readback (fun left right : Nat × Bool => left = x ∧ right = x)
      (PIR.Process.done x : PIR.Process (Domain.effects carriers) _) (PIR.Process.done x) := by
  compose_component_readback [] normalizing skip solving assumption finishing (exact ⟨rfl, rfl⟩)

-- A false terminal postcondition is not inferred from the proof skeleton.
example (x : Nat) : True := by
  fail_if_success
    have : Readback (fun _ _ : Nat => False)
        (PIR.Process.done x : PIR.Process (Domain.effects carriers) Nat) (.done x) := by
      compose_component_readback [] normalizing skip solving assumption finishing trivial
  trivial

-- Neither refusal nor the absence of a matching component proves completion.
example : True := by
  fail_if_success
    have : Readback (fun _ _ : Nat => True)
        (PIR.Process.halt .refused : PIR.Process (Domain.effects carriers) Nat) (.done 0) := by
      compose_component_readback [] normalizing skip solving assumption finishing trivial
  trivial

-- Other caller goals remain pending after successful local composition.
example (x : Nat) :
    Readback (fun left right : Nat => left = right)
      (PIR.Process.done x : PIR.Process (Domain.effects carriers) Nat) (.done x) ∧ True := by
  constructor
  · compose_component_readback [] normalizing skip solving assumption finishing rfl
  · trivial

end TestsSecurity.ComponentReadback
