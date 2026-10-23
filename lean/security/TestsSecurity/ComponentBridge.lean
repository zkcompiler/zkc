module

public import ZkcSecurity.FiatShamir.DomainReduction
public meta import ZkcSecurity.Tools.ComponentBridge

@[expose] public section

/-! Independent opaque components expose changed continuations, restricted
history laws, lost return data, branch changes and changed stop reasons. -/

open Zkc.Source Zkc.Construction Zkc.Transcript
open ZkcSecurity.FiatShamir.DomainReduction

set_option autoImplicit false
-- Stop and pure-return controls intentionally leave some callbacks unused.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace TestsSecurity.ComponentBridge
variable {carriers : Structured.Carriers} {I : PIR.Signature}
  (absorb : Interface I (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw)
  (leftA rightA : PIR.Process (Domain.effects carriers) Bool)
  (leftP rightP : PIR.Process I Bool)
  (leftLaw : ∀ history, Bridge absorb (fun _ _ => True) history leftA leftP)
  (rightLaw : ∀ history, Bridge absorb (fun _ _ => True) history rightA rightP)
  (history : Domain.History carriers)

include leftLaw rightLaw in
theorem sequence : Bridge absorb (fun _ (_value : Bool × Bool) => True) history
    (leftA.bind fun a => rightA.bind fun b => .done (a,b))
    (leftP.bind fun a => rightP.bind fun b => .done (a,b)) := by
  fail_if_success
    compose_component_bridge [] normalizing skip solving assumption finishing trivial
  fail_if_success
    compose_component_bridge [leftLaw, rightLaw history] normalizing skip solving assumption finishing trivial
  compose_component_bridge [leftLaw, rightLaw] normalizing skip solving assumption finishing trivial

end TestsSecurity.ComponentBridge
#print axioms TestsSecurity.ComponentBridge.sequence

namespace TestsSecurity.ComponentBridgeFurther
open Zkc.Source Zkc.Construction Zkc.Transcript
open ZkcSecurity.FiatShamir.DomainReduction
variable {carriers : Structured.Carriers} {I : PIR.Signature}
  (absorb : Interface I (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw)
  (history : Domain.History carriers)

 theorem stopped : Bridge (A := Bool) absorb (fun _ _ => False) history
    (.halt .exhausted) (.halt .exhausted) := by
  fail_if_success
    have : Bridge (A := Bool) absorb (fun _ _ => False) history
        (.halt .exhausted) (.halt .reject) := by
      compose_component_bridge [] normalizing skip solving assumption finishing contradiction
  compose_component_bridge [] normalizing skip solving assumption finishing contradiction

 theorem pending : Bridge absorb (fun _ (value : Bool) => value = true) history
    (.done true) (.done true) ∧ True := by
  constructor
  compose_component_bridge [] normalizing skip solving assumption finishing rfl
  trivial

 theorem dependent_returns
    (leftA : PIR.Process (Domain.effects carriers) (Nat × Bool))
    (leftP : PIR.Process I (Nat × Bool))
    (rightA : Nat × Bool → PIR.Process (Domain.effects carriers) Nat)
    (rightP : Nat × Bool → PIR.Process I Nat)
    (leftLaw : ∀ reached, Bridge absorb (fun _ _ => True) reached leftA leftP)
    (rightLaw : ∀ reached value, Bridge absorb (fun _ _ => True) reached (rightA value) (rightP value)) :
    Bridge absorb (fun _ _ => True) history
      (leftA.bind fun input => (rightA input).bind fun value => .done (input, value))
      (leftP.bind fun input => (rightP input).bind fun value => .done (input, value)) := by
  fail_if_success
    have : Bridge absorb (fun _ _ => True) history
        (leftA.bind fun input => (rightA input).bind fun value => .done (input, value))
        (leftP.bind fun input => (rightP (input.1, false)).bind fun value => .done (input, value)) := by
      compose_component_bridge [leftLaw, rightLaw] normalizing skip solving assumption finishing trivial
  compose_component_bridge [leftLaw, rightLaw] normalizing skip solving assumption finishing trivial

#print axioms stopped
#print axioms pending
#print axioms dependent_returns
end TestsSecurity.ComponentBridgeFurther

namespace TestsSecurity.ComponentBridgeGuards
open Zkc.Source Zkc.Construction Zkc.Transcript
open ZkcSecurity.FiatShamir.DomainReduction
variable {carriers : Structured.Carriers} {I : PIR.Signature}
  (absorb : Interface I (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw)
  (history : Domain.History carriers)

 theorem guarded (condition : Prop) [Decidable condition] :
    Bridge absorb (fun _ (result : Nat) => result = 7) history
      (if condition then .done 7 else .halt .exhausted)
      (if condition then .done 7 else .halt .exhausted) := by
  fail_if_success
    have : Bridge absorb (fun _ (result : Nat) => result = 7) history
        (if condition then .done 7 else .halt .exhausted)
        (if condition then .done 7 else .halt .reject) := by
      compose_component_bridge [] normalizing skip solving assumption finishing rfl
  compose_component_bridge [] normalizing skip solving assumption finishing rfl

#print axioms guarded
end TestsSecurity.ComponentBridgeGuards
