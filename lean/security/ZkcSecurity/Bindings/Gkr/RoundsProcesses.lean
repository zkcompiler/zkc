module

public import ZkcSecurity.Bindings.Gkr.RoundsHelpers
public import Zkc.Protocols.Multilinear.Source.CollectLaws
public import Zkc.Source.Structured.Participant

@[expose] public section

/-! Reusable GKR round process and interpolation template ABI. -/
namespace ZkcSecurity.Examples.Components.GkrRoundsProcesses
open Zkc.Source Zkc.Source.Structured
open ZkcSecurity.Examples.Components.GkrRoundsHelpers
noncomputable section
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

abbrev vector := Ty.vector "bls12-381.fr"
abbrev scalar := Ty.field "bls12-381.fr"

def split (xs : List F) :
    PIR.Process (participantInterface F G) (Values (assignment F G) [vector, vector]) :=
  primitiveOutcome (Primitive.evaluate (.vectorSplit "bls12-381.fr") (.cons xs .nil))

def round (a m l r : List F) :
    PIR.Process (participantInterface F G) (Values (assignment F G) [scalar, scalar, scalar]) :=
  (split a).bind fun a => (split m).bind fun m =>
  (split l).bind fun l => (split r).bind fun r =>
  (mapped (G := G) (Evaluation.mapShape [(a.get .here).length, (m.get .here).length,
      (l.get .here).length, (r.get .here).length])
    (valuesFormula (a.get .here) (m.get .here) (l.get .here) (r.get .here))).bind fun low =>
  (mapped (G := G) (Evaluation.mapShape [(a.get (.there .here)).length, (m.get (.there .here)).length,
      (l.get (.there .here)).length, (r.get (.there .here)).length])
    (valuesFormula (a.get (.there .here)) (m.get (.there .here))
      (l.get (.there .here)) (r.get (.there .here)))).bind fun high =>
  (mapped (G := G) (Evaluation.mapShape [(a.get .here).length, (a.get (.there .here)).length,
      (m.get .here).length, (m.get (.there .here)).length,
      (l.get .here).length, (l.get (.there .here)).length,
      (r.get .here).length, (r.get (.there .here)).length])
    (quadraticsFormula (a.get .here) (a.get (.there .here))
      (m.get .here) (m.get (.there .here)) (l.get .here) (l.get (.there .here))
      (r.get .here) (r.get (.there .here)))).bind fun q =>
  .done (.cons (low.get .here).sum
    (.cons ((high.get .here).sum - (low.get .here).sum - (q.get .here).sum)
      (.cons (q.get .here).sum .nil)))

abbrev interpolationBindings : ZkcExamples.Structured.MultilinearCollectBodies.Bindings where
  collection := interpolationsHelper.name
  domain := interpolationsCollection.domain.name
  callback := interpolationCallbackHelper.name
  computation := interpolationRealizationHelper.name

end
end ZkcSecurity.Examples.Components.GkrRoundsProcesses
