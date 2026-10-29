module

public import ZkcExamples.Structured.Generated.Presentations.Gkr
public import ZkcExamples.Structured.GkrSourceGuards
public import ZkcExamples.Structured.SumcheckVerifierHelpers

@[expose] public section

/-! The current GKR validator's actual admission prefix. These statements are
about its retained participant, before any circuit representation is selected. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

namespace ZkcExamples.Structured.GkrSourceAdmission
open Zkc.Source Zkc.Source.Structured PrimitiveLibrary SumcheckVerifierHelpers

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

def inputs (initial outputs add mul : List F) (layers selector width handle : Nat) :
    Values (Component (assignment F G)) GkrSourceBodies.gkrSignature.inputs :=
  .cons (some initial) (.cons (some outputs) (.cons (some add) (.cons (some mul)
    (.cons (some layers) (.cons (some selector) (.cons (some width) (.cons (some handle) .nil)))))))

def participant (initial outputs add mul : List F) (layers selector width handle : Nat) :=
  GkrSourceViews.program.participant F G 1 (inputs (G := G) initial outputs add mul layers selector width handle)

/-- Source admission is read from the same complete checked role view as the
canonical and retained compiled properties. No input or transcript premise is
needed for this correspondence. -/
theorem presentation (initial outputs add mul : List F) (layers selector width handle : Nat) :
    participant (G := G) initial outputs add mul layers selector width handle =
      Generated.Presentations.Gkr.Root.verifierProcess {} (some initial) (some outputs)
        (some add) (some mul) (some layers) (some selector) (some width) (some handle) := by
  refine (Generated.Presentations.Gkr.Root.verifier_participant
    (inputs (G := G) initial outputs add mul layers selector width handle)).trans ?_
  change (Generated.Presentations.Gkr.Root.verifierProcess {} (some initial) (some outputs)
    (some add) (some mul) (some layers) (some selector) (some width) (some handle)).bind
      (fun out => .done (.cons (out.get .here) .nil : Values (Component (assignment F G)) [.boolean])) = _
  simp only [SumcheckHelperLaws.singleton_eta, PIR.Process.bind_done]

theorem comparison_plain (a b : Nat) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      PrimitiveShapeViews.lessHelper (.cons a (.cons b .nil)) =
      if a < indexLimit ∧ b < indexLimit then .done (boolResult (decide (a < b)))
      else .halt .refused := by
  rw [closed_invoke_plain]
  change (invoke (GkrSourceGuards.helpers (F := F) (G := G)) _ _).interpret _ = _
  rw [GkrSourceGuards.comparison_all]
  split <;> rfl

theorem shape_plain (xs : List F) (dimension : Nat) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      PrimitiveShapeViews.shapeHelper (PrimitiveLibrary.inputs xs dimension 1) =
      if dimension < indexLimit then
        if dimension < 64 then
          if xs.length < indexLimit then
            .done (boolResult (decide (xs.length = 2 ^ dimension)))
          else .halt .exhausted
        else .done (boolResult false)
      else .halt .refused := by
  rw [closed_invoke_plain]
  change (invoke (GkrSourceGuards.helpers (F := F) (G := G)) _ _).interpret _ = _
  rw [GkrSourceGuards.shape_all]
  by_cases representable : dimension < indexLimit <;>
    by_cases small : dimension < 64 <;> by_cases bounded : xs.length < indexLimit <;>
      simp [representable, small, bounded, PIR.Process.interpret]

theorem shape_plain_values (xs : List F) (dimension : Nat) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      GkrSourceBodies.helper4Helper (.cons xs (.cons dimension (.cons 1 .nil))) =
      if dimension < indexLimit then
        if dimension < 64 then
          if xs.length < indexLimit then
            .done (boolResult (decide (xs.length = 2 ^ dimension)))
          else .halt .exhausted
        else .done (boolResult false)
      else .halt .refused := shape_plain xs dimension

theorem index_add_plain (a b : Nat) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      GkrSourceBodies.sourceHelper4Helper (.cons a (.cons b .nil)) =
      if a < indexLimit ∧ b < indexLimit ∧ a + b < indexLimit then
        .done (.cons (a + b) .nil) else .halt .refused := by
  rw [closed_invoke_plain]
  change (invoke (GkrSourceGuards.helpers (F := F) (G := G)) _ _).interpret _ = _
  rw [GkrSourceGuards.index_add_all]
  split <;> rfl

theorem power_plain (exponent : Nat) (small : exponent < 64) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      GkrSourceBodies.helper18Helper (.cons exponent .nil) =
      .done (.cons (2 ^ exponent) .nil) := by
  rw [closed_invoke_plain]
  change (invoke (GkrSourceGuards.helpers (F := F) (G := G)) _ _).interpret _ = _
  rw [GkrSourceGuards.power_bounded exponent small]
  rfl

/-- Above the declared width, the new explicit guard rejects representable
inputs and preserves the checked-index refusal for unrepresentable inputs. -/
theorem width_refuses (initial outputs add mul : List F) (layers selector width handle : Nat)
    (outside : 4 < width) :
    participant (G := G) initial outputs add mul layers selector width handle =
      .halt (if width < indexLimit then .reject else .refused) := by
  rw [presentation]
  unfold Generated.Presentations.Gkr.Root.verifierProcess
  by_cases representable : width < indexLimit <;>
    simp [Evaluation.ComponentTables.toOn, Generated.Presentations.Gkr.payload,
      Generated.Presentations.Gkr.program, GkrSourceViews.program, Values.get,
    PIR.Process.bind,
    comparison_plain, show 4 < indexLimit by decide, true_and, outside, decide_true,
    representable, ite_true, ite_false, boolResult]


/-- The layer bound is checked before any output challenge. -/
theorem layers_refuses (initial outputs add mul : List F) (layers selector width handle : Nat)
    (widthBound : width ≤ 4) (outside : 4 < layers) :
    participant (G := G) initial outputs add mul layers selector width handle =
      .halt (if layers < indexLimit then .reject else .refused) := by
  rw [presentation]
  unfold Generated.Presentations.Gkr.Root.verifierProcess
  have widthSmall : width < indexLimit := lt_of_le_of_lt widthBound (by decide)
  have widthCheck : ¬ 4 < width := by omega
  by_cases representable : layers < indexLimit <;>
    simp [Evaluation.ComponentTables.toOn, Generated.Presentations.Gkr.payload,
      Generated.Presentations.Gkr.program, GkrSourceViews.program, Values.get,
    PIR.Process.bind,
    comparison_plain, show 4 < indexLimit by decide, true_and, outside, widthSmall, widthCheck, decide_true,
    representable, ite_true, ite_false, boolResult]

/-- Unused wiring still has to have its full shape at zero layers. -/
theorem zero_add_refuses (a b : F) (mul : List F) (handle : Nat) :
    participant (G := G) [a] [b] [] mul 0 0 0 handle = .halt .reject := by
  rw [presentation]
  unfold Generated.Presentations.Gkr.Root.verifierProcess
  simp [Evaluation.ComponentTables.toOn, Generated.Presentations.Gkr.payload,
      Generated.Presentations.Gkr.program, GkrSourceViews.program, Values.get,
    PIR.Process.bind,
    comparison_plain, show 4 < indexLimit by decide, show 0 < indexLimit by decide,
    show 1 < indexLimit by decide, true_and, decide_true,
     ite_true, ite_false, boolResult, shape_plain_values, index_add_plain]

theorem zero_mul_refuses (a b gate : F) (handle : Nat) :
    participant (G := G) [a] [b] [gate] [] 0 0 0 handle = .halt .reject := by
  rw [presentation]
  unfold Generated.Presentations.Gkr.Root.verifierProcess
  simp [Evaluation.ComponentTables.toOn, Generated.Presentations.Gkr.payload,
      Generated.Presentations.Gkr.program, GkrSourceViews.program, Values.get,
    PIR.Process.bind,
    comparison_plain, show 4 < indexLimit by decide, show 0 < indexLimit by decide,
    show 1 < indexLimit by decide, true_and, decide_true,
     ite_true, ite_false, boolResult, shape_plain_values, index_add_plain]

/-- Every malformed input table stops before any challenge, including a list
whose length cannot be represented by a machine index. -/
theorem initial_refuses (initial outputs add mul : List F) (layers selector width handle : Nat)
    (widthBound : width ≤ 4) (layersBound : layers ≤ 4)
    (malformed : initial.length ≠ 2 ^ width) :
    participant (G := G) initial outputs add mul layers selector width handle =
      .halt (if initial.length < indexLimit then .reject else .exhausted) := by
  rw [presentation]
  unfold Generated.Presentations.Gkr.Root.verifierProcess
  have widthSmall : width < indexLimit := lt_of_le_of_lt widthBound (by decide)
  have layerSmall : layers < indexLimit := lt_of_le_of_lt layersBound (by decide)
  have dimensionSmall : width < 64 := by omega
  have widthCheck : ¬ 4 < width := by omega
  have layerCheck : ¬ 4 < layers := by omega
  by_cases tableBound : initial.length < indexLimit <;>
    simp [Evaluation.ComponentTables.toOn, Generated.Presentations.Gkr.payload,
      Generated.Presentations.Gkr.program, GkrSourceViews.program, Values.get,
      PIR.Process.bind,
      comparison_plain, show 4 < indexLimit by decide, show 1 < indexLimit by decide,
      widthSmall, layerSmall, dimensionSmall, widthCheck, layerCheck, tableBound,
      malformed, boolResult, shape_plain_values]

/-- The claimed output has its own shape check; its contents are not an
assumption of the source input policy. -/
theorem outputs_refuse (initial outputs add mul : List F) (layers selector width handle : Nat)
    (widthBound : width ≤ 4) (layersBound : layers ≤ 4)
    (initialShape : initial.length = 2 ^ width) (malformed : outputs.length ≠ 2 ^ width) :
    participant (G := G) initial outputs add mul layers selector width handle =
      .halt (if outputs.length < indexLimit then .reject else .exhausted) := by
  rw [presentation]
  unfold Generated.Presentations.Gkr.Root.verifierProcess
  have widthSmall : width < indexLimit := lt_of_le_of_lt widthBound (by decide)
  have layerSmall : layers < indexLimit := lt_of_le_of_lt layersBound (by decide)
  have dimensionSmall : width < 64 := by omega
  have widthCheck : ¬ 4 < width := by omega
  have layerCheck : ¬ 4 < layers := by omega
  have initialBound : initial.length < indexLimit := by
    rw [initialShape]
    exact power_bound width dimensionSmall
  by_cases tableBound : outputs.length < indexLimit <;>
    simp [Evaluation.ComponentTables.toOn, Generated.Presentations.Gkr.payload,
      Generated.Presentations.Gkr.program, GkrSourceViews.program, Values.get,
      PIR.Process.bind,
      comparison_plain, show 4 < indexLimit by decide, show 1 < indexLimit by decide,
      widthSmall, layerSmall, dimensionSmall, widthCheck, layerCheck, tableBound,
      malformed, boolResult, shape_plain_values,
      initialShape, initialBound, power_bound width dimensionSmall]


/-- The add wiring is checked even when no layer is executed. -/
theorem add_refuses (initial outputs add mul : List F) (layers selector width handle : Nat)
    (widthBound : width ≤ 4) (layersBound : layers ≤ 4)
    (initialShape : initial.length = 2 ^ width) (outputShape : outputs.length = 2 ^ width)
    (dimensions : selector + width + width + width < 64)
    (malformed : add.length ≠ 2 ^ (selector + width + width + width)) :
    participant (G := G) initial outputs add mul layers selector width handle =
      .halt (if add.length < indexLimit then .reject else .exhausted) := by
  rw [presentation]
  unfold Generated.Presentations.Gkr.Root.verifierProcess
  have widthSmall : width < indexLimit := lt_of_le_of_lt widthBound (by decide)
  have layerSmall : layers < indexLimit := lt_of_le_of_lt layersBound (by decide)
  have dimensionSmall : width < 64 := by omega
  have widthCheck : ¬ 4 < width := by omega
  have layerCheck : ¬ 4 < layers := by omega
  have machineDimension : 64 < indexLimit := by decide
  have selectorBound : selector < indexLimit := by omega
  have firstBound : selector + width < indexLimit := by omega
  have secondBound : selector + width + width < indexLimit := by omega
  have thirdBound : selector + width + width + width < indexLimit := by omega
  by_cases tableBound : add.length < indexLimit <;>
    simp [Evaluation.ComponentTables.toOn, Generated.Presentations.Gkr.payload,
      Generated.Presentations.Gkr.program, GkrSourceViews.program, Values.get,
      PIR.Process.bind,
      comparison_plain, show 4 < indexLimit by decide, show 1 < indexLimit by decide,
      widthSmall, layerSmall, dimensionSmall, widthCheck, layerCheck, tableBound,
      malformed, boolResult, shape_plain_values,
      initialShape, outputShape, power_bound width dimensionSmall, index_add_plain,
      selectorBound, firstBound, secondBound, thirdBound, dimensions, ← Nat.add_assoc]


/-- The mul wiring is checked even when no layer is executed. -/
theorem mul_refuses (initial outputs add mul : List F) (layers selector width handle : Nat)
    (widthBound : width ≤ 4) (layersBound : layers ≤ 4)
    (initialShape : initial.length = 2 ^ width) (outputShape : outputs.length = 2 ^ width)
    (dimensions : selector + width + width + width < 64)
    (addShape : add.length = 2 ^ (selector + width + width + width))
    (malformed : mul.length ≠ 2 ^ (selector + width + width + width)) :
    participant (G := G) initial outputs add mul layers selector width handle =
      .halt (if mul.length < indexLimit then .reject else .exhausted) := by
  rw [presentation]
  unfold Generated.Presentations.Gkr.Root.verifierProcess
  have widthSmall : width < indexLimit := lt_of_le_of_lt widthBound (by decide)
  have layerSmall : layers < indexLimit := lt_of_le_of_lt layersBound (by decide)
  have dimensionSmall : width < 64 := by omega
  have widthCheck : ¬ 4 < width := by omega
  have layerCheck : ¬ 4 < layers := by omega
  have machineDimension : 64 < indexLimit := by decide
  have selectorBound : selector < indexLimit := by omega
  have firstBound : selector + width < indexLimit := by omega
  have secondBound : selector + width + width < indexLimit := by omega
  have thirdBound : selector + width + width + width < indexLimit := by omega
  by_cases tableBound : mul.length < indexLimit <;>
    simp [Evaluation.ComponentTables.toOn, Generated.Presentations.Gkr.payload,
      Generated.Presentations.Gkr.program, GkrSourceViews.program, Values.get,
      PIR.Process.bind,
      comparison_plain, show 4 < indexLimit by decide, show 1 < indexLimit by decide,
      widthSmall, layerSmall, dimensionSmall, widthCheck, layerCheck, tableBound,
      malformed, boolResult, shape_plain_values,
      initialShape, outputShape, power_bound width dimensionSmall, index_add_plain,
      selectorBound, firstBound, secondBound, thirdBound, dimensions, ← Nat.add_assoc, addShape, power_bound _ dimensions]


/-- Oversized selector dimensions preserve every checked-index refusal. A
representable dimension of at least 64 fails the actual shape guard. -/
theorem dimensions_refuse (initial outputs add mul : List F) (layers selector width handle : Nat)
    (widthBound : width ≤ 4) (layersBound : layers ≤ 4)
    (initialShape : initial.length = 2 ^ width) (outputShape : outputs.length = 2 ^ width)
    (outside : ¬ selector + width + width + width < 64) :
    participant (G := G) initial outputs add mul layers selector width handle =
      .halt (if selector + width + width + width < indexLimit then .reject else .refused) := by
  rw [presentation]
  unfold Generated.Presentations.Gkr.Root.verifierProcess
  have widthSmall : width < indexLimit := lt_of_le_of_lt widthBound (by decide)
  have layerSmall : layers < indexLimit := lt_of_le_of_lt layersBound (by decide)
  have dimensionSmall : width < 64 := by omega
  have widthCheck : ¬ 4 < width := by omega
  have layerCheck : ¬ 4 < layers := by omega
  by_cases selectorBound : selector < indexLimit <;>
    by_cases firstBound : selector + width < indexLimit <;>
    by_cases secondBound : selector + width + width < indexLimit <;>
    by_cases thirdBound : selector + width + width + width < indexLimit
  all_goals try omega
  all_goals
    simp [Evaluation.ComponentTables.toOn, Generated.Presentations.Gkr.payload,
      Generated.Presentations.Gkr.program, GkrSourceViews.program, Values.get,
      PIR.Process.bind,
      comparison_plain, show 4 < indexLimit by decide, show 1 < indexLimit by decide,
      widthSmall, layerSmall, dimensionSmall, widthCheck, layerCheck,
      boolResult, shape_plain_values,
      initialShape, outputShape, power_bound width dimensionSmall, index_add_plain,
      selectorBound, firstBound, secondBound, thirdBound, outside, ← Nat.add_assoc]


/-- A shape-correct wiring stack must still cover every requested layer. -/
theorem capacity_refuses (initial outputs add mul : List F) (layers selector width handle : Nat)
    (widthBound : width ≤ 4) (layersBound : layers ≤ 4)
    (initialShape : initial.length = 2 ^ width) (outputShape : outputs.length = 2 ^ width)
    (dimensions : selector + width + width + width < 64)
    (addShape : add.length = 2 ^ (selector + width + width + width))
    (mulShape : mul.length = 2 ^ (selector + width + width + width))
    (outside : ¬ layers ≤ 2 ^ selector) :
    participant (G := G) initial outputs add mul layers selector width handle = .halt .reject := by
  rw [presentation]
  unfold Generated.Presentations.Gkr.Root.verifierProcess
  have widthSmall : width < indexLimit := lt_of_le_of_lt widthBound (by decide)
  have layerSmall : layers < indexLimit := lt_of_le_of_lt layersBound (by decide)
  have dimensionSmall : width < 64 := by omega
  have selectorSmall : selector < 64 := by omega
  have widthCheck : ¬ 4 < width := by omega
  have layerCheck : ¬ 4 < layers := by omega
  have machineDimension : 64 < indexLimit := by decide
  have selectorBound : selector < indexLimit := by omega
  have firstBound : selector + width < indexLimit := by omega
  have secondBound : selector + width + width < indexLimit := by omega
  have thirdBound : selector + width + width + width < indexLimit := by omega
  have capacityCheck : 2 ^ selector < layers := by omega
  simp [Evaluation.ComponentTables.toOn, Generated.Presentations.Gkr.payload,
      Generated.Presentations.Gkr.program, GkrSourceViews.program, Values.get,
    PIR.Process.bind,
    comparison_plain, show 4 < indexLimit by decide, show 1 < indexLimit by decide,
    widthSmall, layerSmall, dimensionSmall, widthCheck, layerCheck,
    boolResult, shape_plain_values,
    initialShape, outputShape, power_bound width dimensionSmall, index_add_plain,
    selectorBound, firstBound, secondBound, thirdBound, dimensions, ← Nat.add_assoc,
    addShape, mulShape, power_bound _ dimensions, power_plain _ selectorSmall,
    power_bound selector selectorSmall, capacityCheck]

end ZkcExamples.Structured.GkrSourceAdmission
