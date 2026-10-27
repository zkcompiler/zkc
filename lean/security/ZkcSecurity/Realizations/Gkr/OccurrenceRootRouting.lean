module

public import ZkcSecurity.Realizations.Gkr.OccurrenceLayerRouting
public import ZkcSecurity.Realizations.Gkr.OccurrenceVerifier

@[expose] public section

/-! Complete routing of the current validator on every typed public input.
The source admission prefix and every helper stop are retained. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.OccurrenceRouting
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured ZkcExamples.Construction.GkrSourceRouting
open Zkc.Construction.Uniform.OccurrenceSourceProcess
open HonestProducerSource
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

macro "route_guard " frames:term " over " scalar:term "," group:term : tactic =>
  `(tactic|
    refine Routed.letOp (middle := $frames) _ _ _ _ _ _
      (by
        simp only [participantMeaningWithOn, protocolOperationWithOn]
        exact (Routed.guard (F := $scalar) (G := $group) _ _ _ _).bind fun _ => .done _ _)
      ?_)

/-- All raw statement values, including source admission refusals. -/
def body_routed (initial outputs add mul : List F) (layers selector width handle : Nat) :
    Routed (routing handle) [] []
      (GkrSourceCallbacks.gkrBody.denote
        (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
          observedHelpers 1 beforeRoot {} Occurrence.iterations)
        (GkrSourceAdmission.inputs (G := G) initial outputs add mul layers selector width handle).get) := by
  unfold GkrSourceCallbacks.gkrBody
  route_mark
  route_calculation handle at [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_helper handle at [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_calculation handle at [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_calculation handle at [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_guard [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_calculation handle at [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_helper handle at [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_calculation handle at [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_calculation handle at [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_guard [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_calculation handle at [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_helper handle at [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_guard [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_calculation handle at [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_helper handle at [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_guard [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_helper handle at [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_helper handle at [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_helper handle at [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_calculation handle at [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_helper handle at [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_guard [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_helper handle at [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_helper handle at [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_helper handle at [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_calculation handle at [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_helper handle at [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_guard [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_helper handle at [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_helper handle at [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_calculation handle at [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_calculation handle at [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_guard [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_helper handle at [] over F, G
  intro values
  cases_type* Values
  route_mark
  route_helper handle at [] over F, G
  intro values
  cases_type* Values
  route_mark
  apply Routed.letOp (middle := [])
  · simp only [participantMeaningWithOn, protocolOperationWithOn, Operands.eval,
      Values.get, Environment.prepend, Environment.push, Regions.denote]
    apply Routed.repeatCaptured
    intro index carried
    have certificate := output_callback_routed (F := F) (G := G) handle index (carried.get .here)
    cases_type* Values
    exact certificate
  · intro values
    cases_type* Values
    route_mark
    route_helper handle at [] over F, G
    intro values
    cases_type* Values
    route_mark
    route_helper handle at [] over F, G
    intro values
    cases_type* Values
    route_mark
    apply Routed.letOp (middle := [])
    · simp only [participantMeaningWithOn, protocolOperationWithOn, Operands.eval,
        Values.get, Environment.prepend, Environment.push, Regions.denote]
      apply Routed.repeatCaptured
      intro index carried
      cases_type* Values
      exact layer_routed (F := F) (G := G) handle index _ _ _ _ _ _ _ _ _
    · intro values
      cases_type* Values
      route_mark
      apply Routed.letOp (middle := [])
      · simp only [participantMeaningWithOn, protocolOperationWithOn]
        have inside : (({} : ProtocolContext).enter "label_696e707574" [1]).contains
            GkrSourceBodies.sourceProtocol80Signature 1 = true := by decide +kernel
        rw [inside]
        exact input_routed (F := F) (G := G) handle [] _ _ _
      · intro values
        exact .done _ _

/-- Routing is proved from the actual current participant, with no input
admission, supplied representation, helper success or transcript premise. -/
def participant_routed (initial outputs add mul : List F) (layers selector width handle : Nat) :
    Routed (routing handle) [] []
      (Occurrence.participant (ringModel F G) GkrSourceViews.program 1
        (GkrSourceAdmission.inputs (G := G) initial outputs add mul layers selector width handle)) := by
  rw [OccurrenceVerifier.body]
  exact body_routed initial outputs add mul layers selector width handle

end ZkcSecurity.Realizations.Gkr.OccurrenceRouting
