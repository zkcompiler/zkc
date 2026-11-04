import ZkcExamples.Structured.SumcheckFoldInvariant
import ZkcExamples.Structured.SumcheckHonestExecution
import ZkcExamples.Structured.SumcheckRepackedViews
import Mathlib.Data.ZMod.Basic

/-! Controls through actual imported helpers, callbacks and complete roots.
The mathematical companion is shared; each unit still supplies exact bodies.
No source fixture, theorem statement or challenge law is changed. -/
set_option autoImplicit false
namespace Tests.SumcheckMathematicalAdoption
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured PrimitiveLibrary MapFirstLaws
open SumcheckHelperBodies SumcheckHelperLaws SumcheckProverLaws SumcheckVerifierLaws
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open Zkc.Protocols.Sumcheck.Multilinear
open SumcheckHonestExecution

abbrev F := ZMod 5

private theorem pair_shape (a b : F) : HasShape [a, b] 1 1 :=
  hasShape_of_length [a, b] 1 1 (by decide) (by decide) rfl

private theorem pair_bound (a b : F) : [a, b].length < indexLimit := by
  change 2 < indexLimit
  decide

/-- A scalar view cannot restore arbitrary raw replies: conservation must be proved. -/
theorem unreachable_reply_does_not_roundtrip :
    SumcheckMathematicalHelpers.pack ([] : List F) 1 0 0 ≠
      (⟨0, 1⟩ : SumcheckMathematicalHelpers.Sums.Output (ringModel F F)) := by
  intro same
  have impossible := congrArg SumcheckMathematicalHelpers.Sums.Output.high same
  exact (by decide : (0 : F) ≠ 1) impossible

/-- Exact dependency predicate; the desired sums equation is not a premise. -/
example (table : Meanings F F) (entries : List F) (dimension columns : Nat) :
    (SumcheckMathematicalHelpers.sumsLaw (F := F) (G := F)).Requires table
      (inputs entries dimension columns) ↔ LessAllLaw table ∧ HalvesBodyLaw table := Iff.rfl

/-- Zero dimension rejects before malformed-vector admission in each actual table. -/
example : invoke (SumcheckSourceContracts.helperMeanings (F := F) (G := F)) sumsHelper
      (inputs [] 0 indexLimit) = .halt .reject := by
  rw [SumcheckSourceContracts.sums_all]
  simp only [show 0 < indexLimit by decide, Nat.lt_irrefl, ite_true, ite_false]

example : invoke (SumcheckReduceContracts.helperMeanings (F := F) (G := F)) sumsHelper
      (inputs [1] 1 0) = .halt .refused := by
  rw [SumcheckReduceContracts.sums_all]
  simp

/-- No shape, width or column-representability premise has been added. -/
example : invoke (SumcheckSourceContracts.helperMeanings (F := F) (G := F)) sumsHelper
      (inputs [1, 2] 3 indexLimit) = .done (messageResult 1 2) := by
  rw [SumcheckSourceContracts.sums_all]
  simp [show 3 < indexLimit by decide, messageResult]

example (entries : List F) :
    invoke (SumcheckReduceContracts.helperMeanings (F := F) (G := F)) sumsHelper
      (inputs entries indexLimit 0) = .halt .refused := by
  rw [SumcheckReduceContracts.sums_all]
  simp only [Nat.lt_irrefl, ite_false]

/-- One unchanged finite-table companion is used in all three distinct subjects. -/
theorem decoded_messages {n : Nat} (entries : List F) (table : Table F (n + 1))
    (decoded : ofList? (n + 1) entries = some table) (bound : n + 1 < indexLimit)
    (columns : Nat) :
    (invoke (SumcheckSourceContracts.helperMeanings (G := F)) sumsHelper
      (inputs entries (n + 1) columns) = .done (messageResult (honestMessage table).1 (honestMessage table).2)) ∧
    (invoke (SumcheckReduceContracts.helperMeanings (G := F)) sumsHelper
      (inputs entries (n + 1) columns) = .done (messageResult (honestMessage table).1 (honestMessage table).2)) ∧
    (invoke (closedMeanings (G := F) SumcheckRepackedViews.unit.definitions) sumsHelper
      (inputs entries (n + 1) columns) = .done (messageResult (honestMessage table).1 (honestMessage table).2)) :=
  ⟨SumcheckUnitContracts.sums_honestMessage SumcheckSourceViews.unit.linked
      SumcheckSourceContracts.bodies entries table columns decoded bound,
    SumcheckReduceContracts.sums_honestMessage entries table columns decoded bound,
    SumcheckUnitContracts.sums_honestMessage SumcheckRepackedViews.unit.linked
      SumcheckReduceContracts.bodies entries table columns decoded bound⟩

example (entries point : List F) (count : Nat) (table : Table F count)
    (decoded : ofList? count entries = some table) (bound : entries.length < indexLimit) :
    PIR.Yields (fun result =>
      let fields := SumcheckMathematicalHelpers.FirstOutputs.unpack result
      RestrictionInvariant table point fields.entries fields.dimension fields.columns)
      (invoke (SumcheckSourceContracts.helperMeanings (G := F)) MapPrefixBodies.prefixHelper
        (MapPrefixLaws.prefixInputs entries count 1 point)) :=
  SumcheckSourceContracts.prefix_invariant entries count table decoded bound point

/-- Oversized prefixes exhaust even before a fitting-point proof is available. -/
example (entries point : List F) (count : Nat) (shape : HasShape entries count 1)
    (bound : entries.length < indexLimit) (overflow : ¬ point.length < indexLimit) :
    invoke (SumcheckSourceContracts.helperMeanings (G := F)) MapPrefixBodies.prefixHelper
      (MapPrefixLaws.prefixInputs entries count 1 point) = .halt .exhausted := by
  rw [SumcheckSourceContracts.prefix_equation entries count 1 point shape bound]
  simp only [overflow, ite_false]

example (entries point : List F) (count : Nat) (shape : HasShape entries count 1)
    (bound : entries.length < indexLimit) (pointBound : point.length < indexLimit)
    (tooLong : count < point.length) :
    invoke (SumcheckSourceContracts.helperMeanings (G := F)) MapPrefixBodies.prefixHelper
      (MapPrefixLaws.prefixInputs entries count 1 point) = .halt .reject := by
  rw [SumcheckSourceContracts.prefix_equation entries count 1 point shape bound]
  simp only [pointBound, Nat.not_le_of_lt tooLong, ite_true, ite_false]

/-- Every typed challenge preserves all four atoms on both actual callbacks. -/
theorem both_callbacks_preserve (entries point : List F) (count dimension : Nat)
    (table : Table F count) (shape : HasShape entries dimension 1)
    (bound : entries.length < indexLimit)
    (invariant : RestrictionInvariant table point entries dimension 1)
    (remaining : point.length < count) (index : Nat) :
    PIR.Yields (SumcheckFoldInvariant.Holds count table (index + 1))
      (bodyFn SumcheckSourceViews.unit SumcheckSourceVerifier.childContext 0
        (.cons (some index) ((embedP (G := F) (entries, dimension, 1, point)).append (cap none)))) ∧
    PIR.Yields (SumcheckFoldInvariant.Holds count table (index + 1))
      (bodyFn SumcheckReduceViews.unit reductionChild 0
        (.cons (some index) ((embedP (G := F) (entries, dimension, 1, point)).append (cap none)))) :=
  ⟨SumcheckFoldInvariant.round_preserves_invariant SumcheckSourceViews.unit
      SumcheckSourceContracts.bodies SumcheckSourceVerifier.childContext 0 rfl (by decide)
      count table entries point dimension 1 index none shape bound invariant remaining,
    SumcheckFoldInvariant.round_preserves_invariant SumcheckReduceViews.unit
      SumcheckReduceContracts.bodies reductionChild 0 rfl (by decide)
      count table entries point dimension 1 index none shape bound invariant remaining⟩

/-- Both complete participants, with arbitrary supplied challenges. -/
example (a b : F) (tape : List F) (supply : 1 ≤ tape.length) :
    (SumcheckSourceViews.program.participant F F 1
      (SumcheckSourceVerifier.sourceRootInputs (some [a, b]) (some ([a, b] : List F).sum)
        (some 1) (some 7))).run (network SumcheckSourceVerifier.childContext)
      ⟨SumcheckSourceViews.program.participant F F 0
        (SumcheckSourceVerifier.sourceRootInputs (some [a, b]) (some ([a, b] : List F).sum)
          (some 1) (some 7)), tape⟩ =
      ⟨.returned (.cons (some true) .nil), ⟨.done (.cons none .nil), tape.drop 1⟩, []⟩ :=
  source_complete [a, b] 1 (pair_shape a b) (pair_bound a b) (by decide) 7 tape supply

example (a b : F) (tape : List F) (supply : 1 ≤ tape.length) :
    (SumcheckReduceViews.program.participant F F 1
      (SumcheckReduceVerifier.reduceRootInputs (some [a, b]) (some 1)
        (some ([a, b] : List F).sum) (some 1) (some 7))).run (network reductionChild)
      ⟨SumcheckReduceViews.program.participant F F 0
        (SumcheckReduceVerifier.reduceRootInputs (some [a, b]) (some 1)
          (some ([a, b] : List F).sum) (some 1) (some 7)), tape⟩ =
      ⟨.returned (SumcheckReduceVerifier.reduceRootResults
          (some (tape.take 1), some (restrictPrefixValues [a, b] (tape.take 1)).sum)),
        ⟨.done (SumcheckProverRoots.reductionResults [a, b] (tape.take 1)), tape.drop 1⟩, []⟩ :=
  reduction_complete [a, b] 1 1 (pair_shape a b) (pair_bound a b) (by decide) (by decide) 7 tape supply

/-- A handler stop on the first real send retains its reason and event prefix. -/
example (a b : F) (reason : PIR.Stop) :
    (SumcheckSourceViews.program.participant F F 0
      (SumcheckSourceVerifier.sourceRootInputs (some [a, b]) none (some 1) none)).run
      (fun _ (state : Nat) => ⟨.stopped reason, state + 1, ["blocked"]⟩) 9 =
      ⟨.stopped reason, 10, ["blocked"]⟩ := by
  rw [SumcheckProverRoots.source_prover [a, b] 1 (pair_shape a b) (pair_bound a b) (by decide)]
  rfl

example (a b : F) (reason : PIR.Stop) :
    (SumcheckReduceViews.program.participant F F 0
      (SumcheckReduceVerifier.reduceRootInputs (some [a, b]) (some 1) none (some 1) none)).run
      (fun _ (state : Nat) => ⟨.stopped reason, state + 1, ["blocked"]⟩) 9 =
      ⟨.stopped reason, 10, ["blocked"]⟩ := by
  rw [SumcheckProverRoots.reduction_prover [a, b] 1 1 (pair_shape a b) (pair_bound a b) (by decide) (by decide)]
  rfl

/-- Reduction retains custody and an unchecked residual even with no rounds. -/
example : SumcheckReduceViews.program.participant F F 1
    (SumcheckReduceVerifier.reduceRootInputs none none (some 1) (some 0) none) =
      .done (SumcheckReduceVerifier.reduceRootResults (some [], some 1)) :=
  SumcheckReduceVerifier.verifier_zero none none 1 none

/-- The actual child cannot replace an absent custody token, even at zero rounds. -/
example : SumcheckVerifierPrelude.reduceDenote (G := F)
    SumcheckReductionNormalForms.reduceMaximum SumcheckReduceViews.unit reductionChild 1
    (SumcheckVerifierPrelude.reduceArguments none none none none (some []) (some (1 : F))
      (some 0) none) = .halt .incomplete := by
  rw [SumcheckVerifierPrelude.reduce_optional SumcheckReduceViews.unit
    SumcheckReduceVerifier.helperBodies SumcheckReduceVerifier.claimBodies reductionChild 1
    rfl (by decide)]
  rfl

/-- Public zero-round checking still returns false for a malformed raw table. -/
example : SumcheckSourceViews.program.participant F F 1
    (SumcheckSourceVerifier.sourceRootInputs (some [1, 2]) (some 3) (some 0) none) =
      .done (.cons (some false) .nil) := by
  rw [SumcheckSourceVerifier.verifier_zero]
  apply SumcheckVerifierTerminal.terminal_malformed
  · exact pair_bound 1 2
  · change 0 < indexLimit
    decide
  · change ¬ HasShape ([1, 2] : List F) 0 1
    rw [hasShape_iff_length [1, 2] 0 (pair_bound 1 2)]
    decide

#print axioms SumcheckMathematicalHelpers.sumsLaw
#print axioms SumcheckMathematicalHelpers.firstLaw
#print axioms SumcheckUnitContracts.sums_honestMessage
#print axioms SumcheckFoldInvariant.round_preserves_invariant
#print axioms both_callbacks_preserve
#print axioms decoded_messages
end Tests.SumcheckMathematicalAdoption
