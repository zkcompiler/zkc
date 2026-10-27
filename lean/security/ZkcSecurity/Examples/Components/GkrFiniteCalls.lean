module

public import ZkcSecurity.Examples.Components.GkrFiniteGate
public import ZkcSecurity.Families.Sumcheck.FiniteCalls

@[expose] public section
noncomputable section

/-! Finite composition of the named two-variable gate component. This checks
conjunctions of circuit gate claims, with a separate child context per call.
It is not a proof of the multilayer caller's line or terminal input checks. -/
set_option autoImplicit false
namespace ZkcSecurity.Examples.Components.GkrFiniteCalls
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm
open ZkcSecurity.Families.Sumcheck
open GkrCallerRealization

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

structure Input (F : Type) where
  context : ProtocolContext
  point : F
  claim : F

def call (service : Nat) (input : Input F) : PIR.Process (participantInterface F G) Bool :=
  GkrFiniteGate.verifier 2 input.context service (raw input.point) input.claim

def view (service : Nat) (input : Input F) : PIR.Process (participantInterface F G) Bool :=
  ((GkrRoundsBinding.program service).remaining (n := 0) 2 input.context
    (GkrRoundsBinding.initial (raw input.point) (reference input.point) input.claim)).bind
    (fun s => .done (decide (s.claim = GkrRoundsReference.total s.reference)))

def verifier (service : Nat) (inputs : List (Input F)) : PIR.Process (participantInterface F G) Bool :=
  FiniteCalls.all (call service) inputs

def Valid (inputs : List (Input F)) : Prop :=
  ∀ input ∈ inputs, RosterDistinct input.context 1 2

def FalseInput (input : Input F) : Prop := input.claim ≠ honestClaim input.point

/-- One composition application, independently of the selected list length. -/
theorem binding (service : Nat) (inputs : List (Input F)) (valid : Valid inputs) :
    verifier (G := G) service inputs = FiniteCalls.all (view service) inputs := by
  exact FiniteCalls.binding (call service) (view service) inputs (fun input member =>
    GkrFiniteGate.binding 2 (by decide) input.context (valid input member) service
      (raw input.point) (reference input.point) input.claim (represented input.point))

variable {E P : Type} {Raw : E → Type} [∀ event, SampleableType (Raw event)]
  {absorb : Zkc.Transcript.Interface (participantInterface F G) E P Raw}
  {charge : List E → E → ENNReal}

/-- Reached-history composition permits a shared all-answer verifier and a
shared oracle. The local law retains its actual conditional sampler. -/
def rejected (service : Nat) (inputs : List (Input F)) (valid : Valid inputs)
    (wrong : ∃ input ∈ inputs, FalseInput input)
    (queries : QueryInterface (GkrRoundsBinding.program (F := F) (G := G) service) absorb)
    (sampling : queries.ConditionalBound (GkrRoundsBinding.representation service) 2 2 charge)
    (history : List E) :
    Zkc.Obligations.Derivation absorb (ZkcSecurity.Obligations.boundedEscape charge)
      (fun _ accepted => accepted = false) history (verifier service inputs) := by
  exact FiniteCalls.rejected (call service) FalseInput inputs
    (fun input member bad reached => GkrFiniteGate.rejected 2 (by decide) input.context
      (valid input member) service (raw input.point) (reference input.point)
      input.claim (represented input.point)
      (by simpa only [FalseInput, honest_control] using bad) queries sampling reached)
    wrong history

/-- All lengths, including 1, 2 and 4, use the same successful execution rule.
Local handler obligations can be discharged by GkrFiniteGate.honest_run. -/
theorem honest_run {H O : Type} (service : Nat) (inputs : List (Input F))
    (handler : PIR.Handler (participantInterface F G) H O)
    (localSuccess : ∀ input ∈ inputs, ∀ h, ∃ final events,
      (call (G := G) service input).run handler h = ⟨.returned true, final, events⟩) (h : H) :
    ∃ final events, (verifier service inputs).run handler h = ⟨.returned true, final, events⟩ :=
  FiniteCalls.honest_run (call service) handler inputs localSuccess h

end ZkcSecurity.Examples.Components.GkrFiniteCalls
