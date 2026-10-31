module

public import ZkcSecurity.Bindings.Gkr.RoundsRealization
public import ZkcSecurityExamples.Components.GkrRoundsProcesses
public import ZkcSecurity.Bindings.Gkr.RoundsSourceRealization
public import Zkc.Polynomial.Multilinear.ListRestriction

@[expose] public section

/-! The exact four-vector representation realizes the degree-two gate reference.
The equations concern complete Processes, including their stopping branches.
Every restriction updates all four factors separately. -/

namespace ZkcSecurity.Examples.Components.GkrRoundsRealization
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.Bindings
open ZkcExamples.Structured.GkrSourceViews
open ZkcExamples.Structured.Generated.Bindings.GkrRounds (payload)
open GkrRoundsHelpers GkrRoundsProcesses GkrRoundsReference
open Zkc.Protocols.AlgebraicRounds
open Zkc.Polynomial.Multilinear

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
noncomputable section
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem fix_success {n : Nat} (xs : List F) (s : Table F (n + 1))
    (decoded : ofList? (n + 1) xs = some s) (capacity : 2 ^ n < indexLimit) (r : F) :
    fix (G := G) xs r = .done (.cons (restrictValues xs r) .nil) := by
  exact ZkcSecurity.Bindings.Gkr.RoundsSourceRealization.fix_success payload.linked bodies xs s decoded capacity r

theorem fixGates_success {n : Nat} (raw : RawState F) (s : State F (n + 1))
    (decoded : Decodes raw s) (capacity : 2 ^ n < indexLimit) (r : F) :
    invoke (table (G := G)) gateRestrictionHelper (raw.values.append (.cons r .nil)) =
      .done (raw.restrict r).values := by
  exact ZkcSecurity.Bindings.Gkr.RoundsSourceRealization.fixGates_success payload.linked bodies raw s decoded capacity r

theorem round_success {n : Nat} (raw : RawState F) (s : State F (n + 1))
    (decoded : Decodes raw s) (capacity : 2 ^ n < indexLimit) :
    invoke (table (G := G)) roundMessageHelper raw.values =
      .done (.cons (message s).constant (.cons (message s).linear (.cons (message s).quadratic .nil))) := by
  exact ZkcSecurity.Bindings.Gkr.RoundsSourceRealization.round_success payload.linked bodies raw s decoded capacity

theorem generated_table : (helpers (F := F) (G := G) payload).closed = table :=
  Evaluation.ComponentTables.closed_fold (.silent _) _ _

theorem owned_round (self owner : Nat)
    (args : Values (Component (assignment F G)) roundMessageHelper.inputs) :
    Participant.owned self owner
      (invoke (helpers (F := F) (G := G) payload).toOn.closed roundMessageHelper) args =
    if owner = self then
      match RoleFamily.sequence args with
      | none => .halt .incomplete
      | some values => (round (values.get .here) (values.get (.there .here))
          (values.get (.there (.there .here)))
          (values.get (.there (.there (.there .here))))).bind fun out => .done out.present
    else .done (Values.absent (assignment F G) roundMessageHelper.outputs) := by
  change Participant.owned self owner
    (invoke (helpers (F := F) (G := G) payload).closed roundMessageHelper) args = _
  rw [generated_table]
  exact ZkcSecurity.Bindings.Gkr.RoundsSourceRealization.owned_round payload.linked bodies self owner args

theorem owned_fixGates (self owner : Nat)
    (args : Values (Component (assignment F G)) gateRestrictionHelper.inputs) :
    Participant.owned self owner
      (invoke (helpers (F := F) (G := G) payload).toOn.closed gateRestrictionHelper) args =
    if owner = self then
      match RoleFamily.sequence args with
      | none => .halt .incomplete
      | some values => (fixGates (values.get .here) (values.get (.there .here))
          (values.get (.there (.there .here))) (values.get (.there (.there (.there .here))))
          (values.get (.there (.there (.there (.there .here)))))).bind fun out => .done out.present
    else .done (Values.absent (assignment F G) gateRestrictionHelper.outputs) := by
  change Participant.owned self owner
    (invoke (helpers (F := F) (G := G) payload).closed gateRestrictionHelper) args = _
  rw [generated_table]
  exact ZkcSecurity.Bindings.Gkr.RoundsSourceRealization.owned_fixGates payload.linked bodies self owner args

end
end ZkcSecurity.Examples.Components.GkrRoundsRealization
