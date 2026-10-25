module

public import ZkcSecurity.FiatShamir.DomainComposition
public meta import ZkcSecurity.Tools.ComponentView

@[expose] public section
set_option autoImplicit false

/-! Presentation construction preserves full returns, reached histories, guards
and exact stop reasons. Unknown effects and source-dependent candidates fail.
Proof-only input conditions stay on the theorem, not the data API. -/

namespace TestsSecurity.ComponentViewControls
open Zkc.Source Zkc.Construction Zkc.Transcript
open ZkcSecurity.FiatShamir.DomainReduction
-- Negative tactic controls deliberately supply callbacks that must remain unexecuted.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
variable {carriers : Structured.Carriers} {I : PIR.Signature}
  (absorb : Interface I (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw)
  (history : Domain.History carriers)

def pureView (value : Nat × Bool) :
    {presented : PIR.Process I (Nat × Bool) //
      Bridge absorb (fun _ output => output = value) history (.done value) presented} := by
  construct_component_view [] normalizing skip solving assumption finishing rfl
project_checked_view pureView as pureProcess with pureBridge
example (value : Nat × Bool) : pureProcess absorb history value = .done value := rfl

noncomputable def guardedView (condition : Prop) [Decidable condition] :
    {presented : PIR.Process I (Nat × Bool) //
      Bridge absorb (fun _ output => output = (7, false)) history
        (if condition then .done (7, false) else .halt .exhausted) presented} := by
  construct_component_view [] normalizing skip solving assumption finishing rfl
project_checked_view guardedView as guardedProcess with guardedBridge
example (condition : Prop) [Decidable condition] :
    guardedProcess absorb history condition =
      if condition then .done (7, false) else .halt .exhausted := rfl

/-- Construction preserves unrelated pending goals. -/
def pending (value : Nat) :
    {presented : PIR.Process I Nat //
      Bridge absorb (fun _ output => output = value) history (.done value) presented} × Bool := by
  constructor
  construct_component_view [] normalizing skip solving assumption finishing rfl
  exact true

/-- A generated data field cannot discharge an unproved terminal predicate. -/
example : True := by
  fail_if_success
    have : {presented : PIR.Process I Nat //
        Bridge absorb (fun _ _ => False) history (.done 7) presented} := by
      construct_component_view [] normalizing skip solving assumption finishing trivial
  trivial

#print axioms pureBridge
#print axioms guardedBridge
end TestsSecurity.ComponentViewControls

namespace TestsSecurity.EncodedComponentViewControls
open Zkc.Source Zkc.Construction Zkc.Transcript
open ZkcSecurity.FiatShamir.DomainReduction
-- Negative tactic controls deliberately supply callbacks that must remain unexecuted.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
variable {carriers : Structured.Carriers} {I : PIR.Signature}
abbrev State (carriers : Structured.Carriers) := Nat × Bool × Domain.History carriers

def encode (value : State carriers) : State carriers × Nat := (value, 7)
def decode (output : State carriers × Nat) : Option (State carriers) :=
  if output.2 = 7 then some output.1 else none

theorem roundtrip (value : State carriers) : decode (encode value) = some value := by
  simp only [decode, encode, ite_true]

def wholeReturn (output : State carriers × Nat) : Nat × Bool × Nat :=
  (output.1.1, output.1.2.1, output.2)

variable (absorb : Interface I (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw)
  (actual : PIR.Process (Domain.effects carriers) (State carriers × Nat))
  (nominal : PIR.Process I (State carriers))
  (headLaw : ∀ history, Bridge absorb
    (fun reached output => ∃ value : State carriers,
      reached = value.2.2 ∧ True ∧ output = encode value)
    history actual (nominal.bind fun value => .done (encode value)))
  (history : Domain.History carriers)

include headLaw in
noncomputable def assembled :
    {presented : PIR.Process I (Nat × Bool × Nat) //
      Bridge absorb (fun _ _ => True) history
        (actual.bind fun output =>
          if output.1.2.1 = true then .done (wholeReturn output) else .halt .reject) presented} := by
  fail_if_success
    construct_component_view [] normalizing (try dsimp only [encode, wholeReturn]) solving assumption finishing trivial
  construct_component_view
    [Bridge.bindEncoded encode decode roundtrip (fun value : State carriers => value.2.2)
      (fun _ => True) (headLaw history)]
    normalizing (try dsimp only [encode, wholeReturn]) solving assumption finishing trivial

project_checked_view assembled as presented with bridge
example : presented absorb actual nominal history =
    nominal.bind (fun value =>
      if value.2.1 = true then .done (value.1, value.2.1, 7) else .halt .reject) := by
  unfold presented
  congr 1
  funext value
  by_cases enabled : value.2.1 = true <;> simp [enabled]

/-- Forgetting a private Boolean is not a valid result decoder. -/
def lossyDecode (output : State carriers × Nat) : Option (State carriers) :=
  some (output.1.1, false, output.1.2.2)
example : ¬ (∀ value : State carriers, lossyDecode (encode value) = some value) := by
  intro law
  have bad := law (0, true, history)
  simp [lossyDecode, encode] at bad

/-- The source may not be supplied as a function of the candidate presentation. -/
example (_sourceOf : PIR.Process I Nat → PIR.Process (Domain.effects carriers) Nat) : True := by
  fail_if_success
    have : {presented : PIR.Process I Nat //
        Bridge absorb (fun _ _ => True) history (_sourceOf presented) presented} := by
      construct_component_view [] normalizing skip solving assumption finishing trivial
  trivial

#print axioms bridge
end TestsSecurity.EncodedComponentViewControls

namespace TestsSecurity.ProofParameterControl
def assembled (n : Nat) (_bound : n < 10) : {value : Nat // value = n} := ⟨n, rfl⟩
project_checked_view assembled as view with proof
example (n : Nat) : view n = n := rfl
example (n : Nat) : view n + 1 = n + 1 := by simp only [view]
example (n : Nat) (bound : n < 10) : view n = n := proof n bound
#print axioms proof
end TestsSecurity.ProofParameterControl

namespace TestsSecurity.ViewInstanceParameters
def assembled (α : Type) [DecidableEq α] (value : α) : {result : α // result = value} := ⟨value, rfl⟩
project_checked_view assembled as view with proof
example (α : Type) (value : α) : view α value = value := rfl
example (α : Type) [DecidableEq α] (value : α) : view α value = value := proof α value
end TestsSecurity.ViewInstanceParameters
