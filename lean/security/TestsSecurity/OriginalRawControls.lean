import ZkcSecurity.Examples.RootProperties.SmallSumcheck.Soundness
import ZkcSecurity.Examples.RootProperties.TwoSums.Soundness
import TestsSecurity.DomainCharges
import TestsSecurity.SumcheckSourceAdmissionControls

/-! Execution controls for the actual admitted occurrence source. Reference
rewrites below are checked source equations, with no honest-input premise. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace TestsSecurity.OriginalRawControls
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck
open SumcheckSourceSelections

abbrev model := ringModel ℚ ℚ
local instance : Fact (IsField (model.Field field)) := ⟨Field.toIsField ℚ⟩

example : ZkcSecurity.Examples.RootProperties.SmallSumcheck.Soundness.budget = 2 := rfl
example : ZkcSecurity.Examples.RootProperties.TwoSums.Soundness.budget = 8 := rfl
example : TestsSecurity.DomainCharges.leftOrigin ≠ TestsSecurity.DomainCharges.rightOrigin := by decide +kernel

abbrev smallSite := ZkcSecurity.Examples.Generated.SmallSumcheck.validatorSites[0]'(by decide)
example :
    Zkc.Construction.Domain.queryOrigin
      ZkcSecurity.Examples.Generated.SmallSumcheck.validatorCompiled.selection.context
      smallSite.occurrence.suite smallSite.occurrence.field smallSite.occurrence.template [0] ≠
      some TestsSecurity.DomainCharges.leftOrigin := by decide +kernel

/-- Arbitrarily large counts refuse at the actual root, with arbitrary raw inputs. -/
theorem small_unbounded (model : DomainModel) [Fact (IsField (model.Field field))]
    (raw : List (model.Field field)) (scalar : model.Field field)
    (handle count : Nat) (excessive : 2 < count) :
    Occurrence.participant model (source .small) 1
      (SourceRootReference.rootInputs model .small
        (.cons (some raw) (.cons (some scalar) (.cons (some count) (.cons (some handle) .nil))))) =
      .halt .refused := by
  rw [SourceRootReference.actual_reference]
  change (SourceRootReference.one model .small {} _ _ _ _ _).bind _ = _
  rw [SourceRootBounds.one_unbounded model .small _ raw count handle scalar (by simpa [maximum] using Nat.not_le.mpr excessive)]
  rfl

theorem two_unbounded (model : DomainModel) [Fact (IsField (model.Field field))]
    (left right : List (model.Field field)) (a b : model.Field field)
    (handle count : Nat) (excessive : 4 < count) :
    Occurrence.participant model (source .twoSums) 1
      (SourceRootReference.rootInputs model .twoSums
        (.cons (some left) (.cons (some right) (.cons (some a) (.cons (some b)
          (.cons (some count) (.cons (some handle) .nil))))))) = .halt .refused := by
  rw [SourceRootReference.actual_reference]
  change (SourceRootReference.one model .twoSums {} _ _ _ _ _).bind _ = _
  rw [SourceRootBounds.one_unbounded model .twoSums _ left count handle a (by simpa [maximum] using Nat.not_le.mpr excessive)]
  rfl

/-- Actual checker overflow, without an implicit raw-table shape premise. -/
example (model : DomainModel) (selection : Selection)
    (raw point : List (model.Field field)) (scalar : model.Field field)
    (small : point.length < 64) (overflow : ¬ raw.length < indexLimit) :
    invoke (SumcheckReferenceInstallation.tables model (source selection).payload.definitions).closed
      Generated.Bindings.SmallSumcheckInputs.helper33Helper
      (ReferenceLibrary.Multilinear.Admission.checkInputs model field raw point scalar) = .halt .exhausted :=
by
  rw [Evaluation.closed_invoke_componentTablesOn]
  rw [SourceAdmission.check_overflow model field _ (source selection).payload.linked
    (admissionBodies selection) raw point scalar overflow small]
  rfl

/-- The actual output tuple preserves the absent private producer coordinates. -/
example (model : DomainModel) (point : List (model.Field field)) (scalar : model.Field field) :
    SumcheckVerifierBodies.reduceReturnValues (SumcheckReferenceInstallation.state model (some point) (some scalar)) =
      .cons none (.cons none (.cons none (.cons none (.cons (some point) (.cons (some scalar) .nil))))) := rfl

/-- A single actual source round, retaining both iteration observations. -/
def oneRound (selection : Selection) (site : String) (raw : List ℚ) (scalar : ℚ) :
    PIR.Process (Occurrence.signature model.toCarriers) (Option Bool) :=
  let ctx := ProtocolContext.enter {} site [0,1]
  PIR.Process.call (.enter ⟨SourceIteration.repeatSite ctx, 0⟩) fun _ =>
  (SumcheckReferenceInstallation.reference model ctx (some 0) (some []) (some scalar)).bind fun returned =>
  .call (.leave ⟨SourceIteration.repeatSite ctx, 0⟩) fun _ =>
  SourceIteration.terminalCheck model selection raw (SumcheckVerifierBodies.reduceReturnValues returned)

theorem one_round (selection : Selection) (site : String) (raw : List ℚ) (scalar : ℚ) :
    SourceRootReference.one model selection {} site (some raw) (some scalar) (some 1) (some 0) =
      oneRound selection site raw scalar := by
  rw [SourceIteration.one_reduction_with_original model selection site raw [0,0] 1 0 scalar () (by decide)]
  rw [SourceIteration.reduction_equation model _ (source selection).payload.linked
    (roundBodies selection) (Occurrence.table model (source selection).payload)
    (ProtocolContext.enter {} site [0,1]) (SourceRootProperties.context_distinct site) 0
    (SumcheckReductionReference.actual_bodies model selection) (maximum selection) 1
    (by cases selection <;> decide)]
  simp only [PIR.repeatN, PIR.Process.bind_assoc, PIR.Process.bind]
  unfold SourceIteration.step
  simp only [Occurrence.iterations, IterationObservations.within, PIR.Process.bind]
  rw [SourceIteration.round_reference model _ (source selection).payload.linked (roundBodies selection)
    (Occurrence.table model (source selection).payload) (ProtocolContext.enter {} site [0,1])
    (SourceRootProperties.context_distinct site) 0]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind]
  rfl

def zeroReplies : PIR.Handler (Occurrence.signature model.toCarriers) Unit String
  | .enter _, _ => ⟨.returned (), (), []⟩
  | .leave _, _ => ⟨.returned (), (), []⟩
  | .action (.receive (.field _) _ _), _ => ⟨.returned 0, (), ["receive"]⟩
  | .action (.receive _ _ _), _ => ⟨.stopped .refused, (), ["refused"]⟩
  | .action (.query _ _ (.cons _ .nil)), _ => ⟨.returned (by change ℚ; exact 0), (), ["query"]⟩
  | .action (.send ..), _ => ⟨.returned (), (), ["deliver"]⟩

def small (raw : List ℚ) (scalar : ℚ) (count : Nat) :=
  Occurrence.participant model (source .small) 1
    (SourceRootReference.rootInputs model .small
      (.cons (some raw) (.cons (some scalar) (.cons (some count) (.cons (some 0) .nil)))))

def two := Occurrence.participant model (source .twoSums) 1
    (SourceRootReference.rootInputs model .twoSums
      (.cons (some []) (.cons (some []) (.cons (some 0) (.cons (some 0)
        (.cons (some 1) (.cons (some 0) .nil)))))))

/-- Malformed input still pays the actual receive/query/delivery prefix. -/
example : ((small [] 0 1).run zeroReplies ()).events =
    ["receive", "receive", "query", "deliver"] := by
  unfold small
  rw [SourceRootReference.actual_reference]
  simp only [SourceRootReference.reference]
  kernel_rfl

example : ((small [] 0 1).run zeroReplies ()).outcome =
    .returned (.cons (some false) .nil) := by
  unfold small
  rw [SourceRootReference.actual_reference]
  simp only [SourceRootReference.reference]
  kernel_rfl

example : small [] 0 0 = .done (.cons (some false) .nil) := by
  unfold small
  rw [SourceRootReference.actual_reference]
  kernel_rfl

/-- A returned false left Boolean does not short circuit the second call. -/
example : (two.run zeroReplies ()).events =
    ["receive", "receive", "query", "deliver", "receive", "receive", "query", "deliver"] := by
  unfold two
  rw [SourceRootReference.actual_reference]
  simp only [SourceRootReference.reference]
  kernel_rfl

example : (two.run zeroReplies ()).outcome = .returned (.cons (some false) .nil) := by
  unfold two
  rw [SourceRootReference.actual_reference]
  simp only [SourceRootReference.reference]
  kernel_rfl

/-- All nonzero scalar claims stop after the two attacker messages, before a query. -/
example (scalar : ℚ) (nonzero : scalar ≠ 0) :
    ((small [] scalar 1).run zeroReplies ()).outcome = .stopped .reject := by
  unfold small
  rw [SourceRootReference.actual_reference]
  change (((SourceRootReference.one model .small {} _ _ _ _ _).bind _).run zeroReplies ()).outcome = _
  rw [one_round]
  simp [oneRound, SumcheckReferenceInstallation.reference, PIR.Process.bind, PIR.Process.run,
    PIR.Execution.follow, zeroReplies, nonzero]

example (scalar : ℚ) (nonzero : scalar ≠ 0) :
    ((small [] scalar 1).run zeroReplies ()).events = ["receive", "receive"] := by
  unfold small
  rw [SourceRootReference.actual_reference]
  change (((SourceRootReference.one model .small {} _ _ _ _ _).bind _).run zeroReplies ()).events = _
  rw [one_round]
  simp [oneRound, SumcheckReferenceInstallation.reference, PIR.Process.bind, PIR.Process.run,
    PIR.Execution.follow, zeroReplies, nonzero]

#print axioms small_unbounded
#print axioms two_unbounded
#print axioms SourceRootBounds.one_no
#print axioms SourceRootBounds.one_cost
end TestsSecurity.OriginalRawControls
