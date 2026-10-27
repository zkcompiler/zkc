module

import ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Soundness
import ZkcSecurity.Examples.Generated.OriginalSecurity.TwoSums.Soundness

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace TestsSecurity.OriginalRawControls
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured
open ZkcSecurity.FiatShamir ZkcSecurity.Families.Sumcheck
open ZkcSecurity.Realizations.Sumcheck.OriginalRaw
open ZkcSecurity.Examples.Generated.OriginalSecurity

example : ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Soundness.budget = 2 := rfl
example : ZkcSecurity.Examples.Generated.OriginalSecurity.TwoSums.Soundness.budget = 8 := rfl
example : SmallSumcheck.Sources.schedule0.query 0 ≠ TwoSums.Sources.schedule0.query 0 := by decide +kernel
example : TwoSums.Sources.schedule0.query 0 ≠ TwoSums.Sources.schedule1.query 0 := by decide +kernel

/-- Source output ABI: all producer-only slots remain absent, in source order. -/
example {F G : Type} [Field F] [DecidableEq F] (point : List F) (scalar : F) :
    output (G := G) ⟨point, scalar⟩ = .cons none (.cons none (.cons none (.cons none
      (.cons (some point) (.cons (some scalar) .nil))))) := rfl

/-- Even arbitrarily large counts have the actual original immediate refusal. -/
example {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (raw : List F) (scalar : F) (handle count : Nat) (excessive : 2 < count) :
    Occurrence.participant (ringModel F G) SmallSumcheck.Sources.program 1
      (.cons (some raw) (.cons (some scalar) (.cons (some count) (.cons (some handle) .nil)))) =
      .halt .refused := by
  rw [SmallSumcheck.Sources.source_root]
  simp [sourceComposition, sourceSequence, SmallSumcheck.Sources.calls, sourceRoot, show ¬ count ≤ 2 by omega, PIR.Process.bind]

example {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (left right : List F) (leftClaim rightClaim : F) (handle count : Nat) (excessive : 4 < count) :
    Occurrence.participant (ringModel F G) TwoSums.Sources.program 1
      (.cons (some left) (.cons (some right) (.cons (some leftClaim) (.cons (some rightClaim)
        (.cons (some count) (.cons (some handle) .nil)))))) = .halt .refused := by
  rw [TwoSums.Sources.source_root]
  simp [sourceComposition, sourceSequence, TwoSums.Sources.calls, sourceRoot, show ¬ count ≤ 4 by omega, PIR.Process.bind]

/-- Checked index overflow is explicit, rather than an implicit shape premise. -/
example {F G : Type} [Field F] [DecidableEq F] (raw point : List F) (scalar : F)
    (overflow : ¬ point.length < indexLimit) :
    terminal (G := G) (I := NominalField.signature F "bls12-381.fr") raw point scalar = .halt .exhausted := by
  simp only [terminal, ite_eq_right overflow]

example {F G : Type} [Field F] [DecidableEq F] (raw point : List F) (scalar : F)
    (small : point.length < 64) (overflow : ¬ raw.length < indexLimit) :
    terminal (G := G) (I := NominalField.signature F "bls12-381.fr") raw point scalar = .halt .exhausted := by
  simp only [terminal, ite_eq_left (small.trans (by decide +kernel : 64 < indexLimit)),
    ite_eq_left small, ite_eq_right overflow]

/-- Large representable dimensions return false before inspecting vector length. -/
example {F G : Type} [Field F] [DecidableEq F] (raw point : List F) (scalar : F)
    (representable : point.length < indexLimit) (large : ¬ point.length < 64) :
    terminal (G := G) (I := NominalField.signature F "bls12-381.fr") raw point scalar =
      .done (.cons (some false) .nil) := by
  simp only [terminal, ite_eq_left representable, ite_eq_right large]

/-- The actual mathematical conjunction preserves absent results. -/
example : both (F := ℚ) (G := ℚ) (I := NominalField.signature ℚ "bls12-381.fr")
    (.cons none .nil) (.cons (some true) .nil) = .done (.cons none .nil) := rfl

def zeroReplies : PIR.Handler (NominalField.signature ℚ "bls12-381.fr") Unit String
  | .receive _, _ => ⟨.returned 0, (), ["receive"]⟩
  | .query .., _ => ⟨.returned 0, (), ["query"]⟩
  | .deliver .., _ => ⟨.returned (), (), ["deliver"]⟩

/-- An empty malformed table still reaches both messages, the query, and its
delivery before the original terminal helper rejects. -/
example : ((SmallSumcheck.Sources.presented (F := ℚ) (G := ℚ) [] 0 1 []).run zeroReplies ()).events =
    ["receive", "receive", "query", "deliver"] := by
  simp [SmallSumcheck.Sources.presented, composition,
    ZkcSecurity.Realizations.Sumcheck.OriginalRaw.sequence, SmallSumcheck.Sources.calls,
    SmallSumcheck.Sources.terminalTree, root, TableComponent.Execution.run, TableComponent.Execution.advance,
    terminal, PIR.Process.bind, PIR.Process.run, PIR.Execution.follow, zeroReplies,
    PrimitiveLibrary.HasShape, indexLimit]

/-- The malformed execution above actually returns false after its query. -/
example : (((SmallSumcheck.Sources.presented (F := ℚ) (G := ℚ) [] 0 1 []).bind
    (fun result => .done (acceptance result))).run zeroReplies ()).outcome =
      .returned (some false) := by
  simp [SmallSumcheck.Sources.presented, composition,
    ZkcSecurity.Realizations.Sumcheck.OriginalRaw.sequence, SmallSumcheck.Sources.calls,
    SmallSumcheck.Sources.terminalTree, root, TableComponent.Execution.run, TableComponent.Execution.advance,
    terminal, acceptance, ZkcSecurity.Realizations.Sumcheck.OriginalSecurity.acceptance,
    PIR.Process.bind, PIR.Process.run, PIR.Execution.follow, zeroReplies,
    PrimitiveLibrary.HasShape, indexLimit]

/-- The original zero-round root inspects the raw shape without interaction. -/
example : Occurrence.participant (ringModel ℚ ℚ) SmallSumcheck.Sources.program 1
    (.cons (some []) (.cons (some 0) (.cons (some 0) (.cons (some 0) .nil)))) =
      .done (.cons (some false) .nil) := by
  rw [SmallSumcheck.Sources.source_root]
  simp [sourceComposition, sourceSequence, SmallSumcheck.Sources.calls, SmallSumcheck.Sources.terminalTree, sourceRoot, run, terminal, PrimitiveLibrary.HasShape, indexLimit, PIR.Process.bind]

/-- A false scalar boundary stops after the two messages, before any query.
The scalar is arbitrary, and no honest producer assumption is involved. -/
example (scalar : ℚ) (nonzero : scalar ≠ 0) :
    ((SmallSumcheck.Sources.presented (F := ℚ) (G := ℚ) [] scalar 1 []).run zeroReplies ()).events =
      ["receive", "receive"] := by
  simp [SmallSumcheck.Sources.presented, composition,
    ZkcSecurity.Realizations.Sumcheck.OriginalRaw.sequence, SmallSumcheck.Sources.calls,
    SmallSumcheck.Sources.terminalTree, root, TableComponent.Execution.run, PIR.Process.bind,
    PIR.Process.run, PIR.Execution.follow, zeroReplies, nonzero]

example (scalar : ℚ) (nonzero : scalar ≠ 0) :
    ((SmallSumcheck.Sources.presented (F := ℚ) (G := ℚ) [] scalar 1 []).run zeroReplies ()).outcome =
      .stopped .reject := by
  simp [SmallSumcheck.Sources.presented, composition,
    ZkcSecurity.Realizations.Sumcheck.OriginalRaw.sequence, SmallSumcheck.Sources.calls,
    SmallSumcheck.Sources.terminalTree, root, TableComponent.Execution.run, PIR.Process.bind,
    PIR.Process.run, PIR.Execution.follow, zeroReplies, nonzero]

/-- TwoSums does not short-circuit on a returned false left Boolean: the
right call still pays for its actual query before conjunction. -/
example : ((TwoSums.Sources.presented (F := ℚ) (G := ℚ) [] [] 0 0 1 []).run zeroReplies ()).events =
    ["receive", "receive", "query", "deliver", "receive", "receive", "query", "deliver"] := by
  simp [TwoSums.Sources.presented, composition,
    ZkcSecurity.Realizations.Sumcheck.OriginalRaw.sequence, TwoSums.Sources.calls,
    TwoSums.Sources.terminalTree, root, TableComponent.Execution.run, TableComponent.Execution.advance,
    terminal, PIR.Process.bind, PIR.Process.run, PIR.Execution.follow, zeroReplies,
    PrimitiveLibrary.HasShape, indexLimit]

example : SmallSumcheck.Sources.presented (F := ℚ) (G := ℚ) [] 0 3 [] = .halt .refused := by
  simp [SmallSumcheck.Sources.presented, composition,
    ZkcSecurity.Realizations.Sumcheck.OriginalRaw.sequence, SmallSumcheck.Sources.calls,
    SmallSumcheck.Sources.terminalTree, root, PIR.Process.bind]

example : TwoSums.Sources.presented (F := ℚ) (G := ℚ) [] [] 0 0 5 [] = .halt .refused := by
  simp [TwoSums.Sources.presented, composition,
    ZkcSecurity.Realizations.Sumcheck.OriginalRaw.sequence, TwoSums.Sources.calls,
    TwoSums.Sources.terminalTree, root, PIR.Process.bind]

#print axioms ZkcSecurity.Realizations.Sumcheck.OriginalRaw.source_step
#print axioms ZkcSecurity.Realizations.Sumcheck.OriginalRaw.source_reduce
#print axioms ZkcSecurity.Realizations.Sumcheck.OriginalRaw.source_terminal
#print axioms ZkcSecurity.Realizations.Sumcheck.OriginalRaw.run_bridge
#print axioms ZkcSecurity.Realizations.Sumcheck.OriginalRaw.root_bridge
#print axioms ZkcSecurity.Realizations.Sumcheck.OriginalRaw.composition_bridge
#print axioms ZkcSecurity.Realizations.Sumcheck.OriginalRaw.root_returns
#print axioms ZkcSecurity.Realizations.Sumcheck.OriginalRaw.sequence_returns
#print axioms ZkcSecurity.Realizations.Sumcheck.OriginalRaw.root_soundness
#print axioms ZkcSecurity.Realizations.Sumcheck.OriginalRaw.root_rejected
#print axioms ZkcSecurity.Realizations.Sumcheck.OriginalRaw.composition_rejected
#print axioms ZkcSecurity.Realizations.Sumcheck.OriginalRaw.root_cost
#print axioms ZkcSecurity.Realizations.Sumcheck.OriginalRaw.composition_cost
#print axioms SmallSumcheck.Sources.source_root
#print axioms TwoSums.Sources.source_root
#print axioms SmallSumcheck.Sources.bridge
#print axioms TwoSums.Sources.bridge
#print axioms ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Soundness.rejected
#print axioms ZkcSecurity.Examples.Generated.OriginalSecurity.TwoSums.Soundness.rejected
#print axioms ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Soundness.costs
#print axioms ZkcSecurity.Examples.Generated.OriginalSecurity.TwoSums.Soundness.costs
#print axioms ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Installation.installation
#print axioms ZkcSecurity.Examples.Generated.OriginalSecurity.TwoSums.Installation.installation

end TestsSecurity.OriginalRawControls
