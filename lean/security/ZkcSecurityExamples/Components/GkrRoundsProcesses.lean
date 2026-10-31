module

public import ZkcSecurity.Bindings.Gkr.RoundsProcesses
public import ZkcSecurityExamples.Components.GkrRoundsHelpers
public import ZkcSecurity.Bindings.Gkr.RoundsProcessInstallation
public import Zkc.Protocols.Sumcheck.Source.HelperExpansions
public import Zkc.Protocols.Multilinear.Source.CollectLaws
public import Zkc.Polynomial.Multilinear.ListRestriction

@[expose] public section

/-! Full operational equations for `round_message` and `fix_gates`. The raw
views retain ordered split checks, map capacity/shape checks and all stops. -/

namespace ZkcSecurity.Examples.Components.GkrRoundsProcesses
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.Bindings
open ZkcExamples.Structured.GkrSourceViews
open GkrRoundsHelpers
open ZkcExamples.Structured.SumcheckHelperLaws (prepend_empty prepend_one prepend_two prepend_three singleton_eta)
open Zkc.Polynomial.Multilinear

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
noncomputable section
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem round_equation (a m l r : List F) :
    invoke (table (G := G)) roundMessageHelper (.cons a (.cons m (.cons l (.cons r .nil)))) =
      round a m l r :=
  ZkcSecurity.Bindings.Gkr.RoundsProcessInstallation.round_equation
    ZkcExamples.Structured.Generated.Bindings.GkrRounds.payload.linked bodies a m l r

theorem map_interpolate (low high : List F) (r : F)
    (small : low.length < indexLimit) (same : high.length = low.length) :
    invoke (table (G := G)) interpolationsHelper (.cons low (.cons high (.cons r .nil))) =
      .done (.cons (List.zipWith (fun a b => a + (b - a) * r) low high) .nil) :=
  ZkcSecurity.Bindings.Gkr.RoundsProcessInstallation.map_interpolate
    ZkcExamples.Structured.Generated.Bindings.GkrRounds.payload.linked bodies.toRestrictionBodies low high r small same

def fix (xs : List F) (r : F) :
    PIR.Process (participantInterface F G) (Values (assignment F G) [vector]) :=
  (split xs).bind fun halves =>
    invoke table interpolationsHelper (.cons (halves.get .here)
      (.cons (halves.get (.there .here)) (.cons r .nil)))

theorem fix_equation (xs : List F) (r : F) :
    invoke (table (G := G)) factorRestrictionHelper (.cons xs (.cons r .nil)) = fix xs r :=
  ZkcSecurity.Bindings.Gkr.RoundsProcessInstallation.fix_equation
    ZkcExamples.Structured.Generated.Bindings.GkrRounds.payload.linked bodies.toRestrictionBodies xs r

def fixGates (a m l r : List F) (challenge : F) :
    PIR.Process (participantInterface F G) (Values (assignment F G) [vector, vector, vector, vector]) :=
  (fix a challenge).bind fun a => (fix m challenge).bind fun m =>
  (fix l challenge).bind fun l => (fix r challenge).bind fun r =>
  .done (.cons (a.get .here) (.cons (m.get .here) (.cons (l.get .here) (.cons (r.get .here) .nil))))

theorem fixGates_equation (a m l r : List F) (challenge : F) :
    invoke (table (G := G)) gateRestrictionHelper
      (.cons a (.cons m (.cons l (.cons r (.cons challenge .nil))))) =
      fixGates a m l r challenge :=
  ZkcSecurity.Bindings.Gkr.RoundsProcessInstallation.fixGates_equation
    ZkcExamples.Structured.Generated.Bindings.GkrRounds.payload.linked bodies a m l r challenge

theorem map_interpolate_exhausted (low high : List F) (r : F)
    (large : ¬ low.length < indexLimit) :
    invoke (table (G := G)) interpolationsHelper (.cons low (.cons high (.cons r .nil))) =
      .halt .exhausted :=
  ZkcSecurity.Bindings.Gkr.RoundsProcessInstallation.map_interpolate_exhausted
    ZkcExamples.Structured.Generated.Bindings.GkrRounds.payload.linked bodies.toRestrictionBodies low high r large

theorem fix_all (xs : List F) (r : F) :
    fix (G := G) xs r =
      if 0 < xs.length ∧ xs.length % 2 = 0 then
        if xs.length / 2 < indexLimit then .done (.cons (restrictValues xs r) .nil)
        else .halt .exhausted
      else .halt .refused :=
  ZkcSecurity.Bindings.Gkr.RoundsProcessInstallation.fix_all
    ZkcExamples.Structured.Generated.Bindings.GkrRounds.payload.linked bodies.toRestrictionBodies xs r

end
end ZkcSecurity.Examples.Components.GkrRoundsProcesses
