module

import ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Soundness
import ZkcSecurity.Examples.Generated.OriginalSecurity.TwoSums.Soundness

set_option autoImplicit false
namespace TestsSecurity.OriginalSecurityFamily
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.FiatShamir ZkcSecurity.Families.Sumcheck TableComponent
open ZkcSecurity.Realizations.Sumcheck.OriginalRaw
open ZkcSecurity.Examples.Generated.OriginalSecurity

example : SmallSumcheck.Soundness.budget = 2 := rfl
example : TwoSums.Soundness.budget = 8 := rfl

/-- Actual source caller identity, not equality of numeric field results,
separates the two challenge occurrences at the same reached index. -/
example : TwoSums.Sources.schedule0.query 0 ≠ TwoSums.Sources.schedule1.query 0 := by decide +kernel

/-- Zero rounds retain the raw terminal helper and the complete construction state. -/
example {F G : Type} [Field F] [DecidableEq F]
    (schedule : Nominal.Schedule "bls12-381.fr") (entries : List F) (scalar : F)
    (construction : ConstructionState (F := F) (G := G)) :
    root 0 schedule entries scalar 0 construction =
      (terminal entries [] scalar).bind (fun result => .done (result, construction)) := rfl

example {F G : Type} (right : Values (Component (assignment F G)) [.boolean]) :
    both (I := NominalField.signature F "bls12-381.fr") (.cons none .nil) right =
      .done (.cons none .nil) := by
  cases right with
  | cons value rest =>
    cases rest
    rfl

#print axioms ZkcSecurity.Realizations.Sumcheck.OriginalRaw.run_bridge
#print axioms ZkcSecurity.Realizations.Sumcheck.OriginalRaw.root_bridge
#print axioms ZkcSecurity.Realizations.Sumcheck.OriginalRaw.composition_bridge
#print axioms SmallSumcheck.Soundness.rejected
#print axioms SmallSumcheck.Soundness.costs
#print axioms TwoSums.Soundness.rejected
#print axioms TwoSums.Soundness.costs

end TestsSecurity.OriginalSecurityFamily
