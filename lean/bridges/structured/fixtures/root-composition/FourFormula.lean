module

public import ZkcExamples.Structured.Generated.Mathematics.FourSums
public import ZkcSecurity.Examples.Generated.FourSums
public import ZkcSecurity.Examples.Generated.Components.FourSumsABI
public import ZkcSecurity.Families.Sumcheck.TableComponentFold
public import ZkcSecurity.Claims.Completeness
public meta import ZkcSecurity.Tools.TargetEvaluation

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace TestsSecurity.RootComposition.Four.Formula
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured.Generated.Bindings
open ZkcExamples.Structured.Generated.Mathematics.FourSums
open ZkcSecurity.Families.Sumcheck.TableComponent
open ZkcSecurity.Examples.Generated.FourSums
open ZkcSecurity.Examples.Generated.Components.FourSumsABI
open ZkcSecurity.Claims.HonestPair
abbrev Scalar := ZMod blsModulus
abbrev rootImported := ZkcSecurity.Examples.Generated.FourSums.imported

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]
noncomputable abbrev helperMeanings : Meanings F G :=
  closedMeanings FourSumsInputs.imported.program.payload.definitions

def targetFold : FoldSpec := totals.callee.fold

theorem target_step (raw : List F) (a value : F) :
    invoke (helperMeanings (G := G)) targetFold.stepHelper
      (.cons a (.cons value (.cons raw .nil))) = .done (.cons (a + value) .nil) := by
  change invoke (helperMeanings (G := G)) totals.callee.foldStep.helper _ = _
  erw [totals.callee.foldStep.association.invoke FourSumsInputs.unit.linked]
  simp only [totals.callee.foldStep.body, Region.denote, meaning, Evaluation.meaning,
    Evaluation.operation, Operands.eval, Values.get, Regions.denote]
  erw [totals.callee.foldStep.calleeDependency0.association.invoke FourSumsInputs.unit.linked]
  rfl

theorem target_total (raw : List F) (bounded : raw.length < indexLimit) :
    invoke (helperMeanings (G := G)) totals.callee.helper (.cons raw .nil) =
      .done (.cons raw.sum .nil) := by
  erw [totals.callee.association.invoke FourSumsInputs.unit.linked]
  simp only [totals.callee.body, Region.denote, meaning, Evaluation.meaning,
    Evaluation.operation, Operands.eval, Values.get, Regions.denote,
    PIR.Process.bind, Environment.prepend, Environment.push, Nat.cast_zero]
  change (Evaluation.denoteFold _ targetFold
    ((Values.cons raw .nil).append ((Values.cons (0 : F) .nil).append .nil))).bind _ = _
  erw [sumFold_equation _ _ _ _ raw 0 bounded (target_step raw)]
  simp only [zero_add, PIR.Process.bind, Environment.prepend, Environment.push]

theorem target_equation (a b c d : List F) (sa sb sc sd : F)
    (ab : a.length < indexLimit) (bb : b.length < indexLimit)
    (cb : c.length < indexLimit) (db : d.length < indexLimit) :
    invoke (helperMeanings (G := G)) totals.helper
      (.cons a (.cons b (.cons c (.cons d (.cons sa (.cons sb (.cons sc (.cons sd .nil)))))))) =
      .done (.cons (((decide (sa = a.sum) && decide (sb = b.sum)) &&
        decide (sc = c.sum)) && decide (sd = d.sum)) .nil) := by
  erw [totals.association.invoke FourSumsInputs.unit.linked]
  simp only [totals.body, Region.denote, meaning, Evaluation.meaning,
    Evaluation.operation, Operands.eval, Values.get, Regions.denote]
  erw [target_total a ab]
  simp only [PIR.Process.bind, Environment.prepend, Environment.push]
  erw [target_total b bb]
  simp only [PIR.Process.bind, Environment.prepend, Environment.push]
  erw [target_total c cb]
  simp only [PIR.Process.bind, Environment.prepend, Environment.push]
  erw [target_total d db]
  rfl

def formula : FormulaBinding rootImported subject.target.application.relation := by bind_contract

theorem equation (a b c d : List Scalar) (sa sb sc sd : Scalar)
    (ab : a.length < indexLimit) (bb : b.length < indexLimit)
    (cb : c.length < indexLimit) (db : d.length < indexLimit) :
    formula.invokeRelationOn ZkcSecurity.Domains.PrimeField.blsScalarModel
      (.cons a (.cons b (.cons c (.cons d (.cons sa (.cons sb (.cons sc (.cons sd .nil)))))))) =
      .done (.cons (((decide (sa = a.sum) && decide (sb = b.sum)) &&
        decide (sc = c.sum)) && decide (sd = d.sum)) .nil) := by
  change invoke (closedMeaningsOn (ringModel Scalar Scalar) rootImported.program.payload.definitions)
    totals.helper _ = (_ : Closed (Values (assignment Scalar Scalar) [.boolean]))
  rw [← closedMeanings_eq_closedMeaningsOn]
  have same : rootImported.program = FourSumsInputs.imported.program := Zkc.Verification.Imported.unique _ _
  rw [congrArg (fun program : Program => program.payload.definitions) same]
  exact target_equation (G := Scalar) a b c d sa sb sc sd ab bb cb db

theorem nonvacuous : Nonvacuous subject := by
  refine ⟨inputs [0] [0] [0] [0] 0 0 0 0 0 (some 0), ?_, ?_⟩
  · prove_retained_target [Scalar, Scalar]
      reading (application_read [0] [0] [0] [0] 0 0 0 0 0 (some 0))
      evaluating equation solving (decide +kernel)
  · rw [honestInput_iff]
    decide +kernel

end TestsSecurity.RootComposition.Four.Formula
