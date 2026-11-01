module

public import ZkcSecurityExamples.Gkr.HonestCircuitGoals
public import ZkcExamples.Structured.GkrGateGoals
public import ZkcSecurity.Bindings.Gkr.CircuitEncodingLaws
public import Zkc.Protocols.Multilinear.Source.CollectionEncoding

@[expose] public section

/-! Circuit mathematics over source-generated complete helper statements.
The dependency contracts describe admitted mathematical operations. The actual
linked table supplies their proofs at installation; no helper law is assumed
by the public circuit theorems. Physical rows and callback syntax are generated.
-/
namespace ZkcSecurity.Realizations.Gkr.HonestCircuit.Companion
open Zkc Source Structured
open ZkcExamples.Structured GkrSourceLaws
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open ZkcSecurity.Examples.Components

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
attribute [local implicit_reducible] Op.arguments Op.results Op.regions

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Mathematical dependencies in the same table as the selected layer body.
All premises are discharged from actual linked helper laws by the installer. -/
structure Dependencies (table : Meanings F G) : Prop where
  block : ∀ (source : List F) (position width size : Nat),
    source.length = 2 ^ width * size → 0 < size → position < 2 ^ width →
    source.length < indexLimit →
    invoke table GkrSourceBodies.selectBlockHelper
      (Goals.BlockArguments.pack (Value := assignment F G) ⟨source, position, width⟩) =
      .done (Goals.BlockResult.pack (Value := assignment F G) ⟨block source position size⟩)
  power : ∀ width, width < 64 →
    invoke table GkrSourceBodies.helper18Helper
      (Goals.PowerArguments.pack (Value := assignment F G) ⟨width⟩) =
      .done (Goals.PowerResult.pack (Value := assignment F G) ⟨2 ^ width⟩)
  replicate : ∀ (source : List F) count, source.length < indexLimit → count < indexLimit →
    invoke table GkrSourceBodies.helper25Helper
      (Goals.RepeatArguments.pack (Value := assignment F G) ⟨source, count⟩) =
      .done (Goals.RepeatResult.pack (Value := assignment F G) ⟨source.flatMap (List.replicate count)⟩)
  tile : ∀ (source : List F) count, count < indexLimit → source.length < indexLimit →
    invoke table GkrSourceBodies.helper30Helper
      (Goals.RepeatArguments.pack (Value := assignment F G) ⟨source, count⟩) =
      .done (Goals.RepeatResult.pack (Value := assignment F G) ⟨(List.replicate count source).flatten⟩)
  gates : ∀ {n : Nat} (add mul left right : Table F n), 2 ^ n < indexLimit →
    invoke table GkrSourceBodies.scopedHelper44Helper
      (GkrGateGoals.Map.Inputs.pack (Value := assignment F G)
        { addWeights := GkrRoundsLayout.encode add, mulWeights := GkrRoundsLayout.encode mul,
          lefts := GkrRoundsLayout.encode left, rights := GkrRoundsLayout.encode right }) =
      .done (GkrGateGoals.Map.encode (ringModel F G)
        ⟨GkrRoundsLayout.encode (fun bits =>
          Zkc.Protocols.AlgebraicRounds.Gate.value (add bits) (mul bits) (left bits) (right bits))⟩)

/-- One actual loop iteration computes the independent value of one gate. -/
theorem step_encoded (table : Meanings F G) (dependencies : Dependencies table) {width : Nat}
    (a m : Zkc.Protocols.Gkr.Wiring F width)
    (v : Table F width) (xs : List F) (position : Fin (2 ^ width))
    (small : width + width + width < 64) :
    Goals.Step.body.denote (meaning F G table)
      (Goals.Step.Inputs.pack (Value := assignment F G)
        { position := position.val, values := xs, addWeights := GkrRoundsLayout.encode a,
          mulWeights := GkrRoundsLayout.encode m, width,
          left := GkrRoundsLayout.encode (GkrRoundsLayout.replicate width width v),
          right := GkrRoundsLayout.encode (GkrRoundsLayout.tile width width v) }).get =
      .done (Goals.Step.encode (ringModel F G)
        { values := xs ++ [(Zkc.Protocols.Gkr.layer a m v) (vertex width position)],
          addWeights := GkrRoundsLayout.encode a, mulWeights := GkrRoundsLayout.encode m, width,
          left := GkrRoundsLayout.encode (GkrRoundsLayout.replicate width width v),
          right := GkrRoundsLayout.encode (GkrRoundsLayout.tile width width v) }) := by
  have bound : 2 ^ (width + width + width) < indexLimit :=
    Nat.pow_lt_pow_right (by decide) small
  have pairBound : 2 ^ (width + width) < indexLimit :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  have shape : (GkrRoundsLayout.encode a).length = 2 ^ width * 2 ^ (width + width) := by
    simp [GkrRoundsLayout.encode, Nat.pow_add, Nat.mul_comm]
  have shapeM : (GkrRoundsLayout.encode m).length = 2 ^ width * 2 ^ (width + width) := by
    simp [GkrRoundsLayout.encode, Nat.pow_add, Nat.mul_comm]
  have selectBlock_equation := dependencies.block
  dsimp only [Goals.BlockArguments.pack, Goals.BlockResult.pack] at selectBlock_equation
  dsimp only [Goals.Step.Inputs.pack]
  simp only [meaning]
  rw [Evaluation.denote_meaning_eq_meaningOn, Goals.stepProcess_equation]
  dsimp only [Goals.stepProcess, Goals.stepProcess_certificate, Op.arguments, Op.results, Op.regions]
  simp only [Op.arguments, Op.results, Op.regions, Primitive.evaluateOn, primitiveOutcome, PIR.Process.bind,
    SumcheckHelperLaws.prepend_empty, SumcheckHelperLaws.prepend_one,
    Environment.prepend, Environment.push, Values.get_head, Values.get_tail, Values.get,
    Goals.Step.encode, show 1 < indexLimit by decide +kernel, ite_true]
  rw [selectBlock_equation _ position.val width (2 ^ (width + width)) shape (by positivity)
      position.isLt (by simpa [GkrRoundsLayout.encode] using bound)]
  simp only [PIR.Process.bind, Op.arguments, Op.results, Op.regions,
    SumcheckHelperLaws.prepend_empty, SumcheckHelperLaws.prepend_one,
    Environment.prepend, Environment.push, Values.get_head, Values.get_tail, Values.get]
  rw [selectBlock_equation _ position.val width (2 ^ (width + width)) shapeM (by positivity)
    position.isLt (by simpa [GkrRoundsLayout.encode] using bound)]
  simp only [PIR.Process.bind, Op.arguments, Op.results, Op.regions,
    SumcheckHelperLaws.prepend_empty, SumcheckHelperLaws.prepend_one,
    Environment.prepend, Environment.push, Values.get_head, Values.get_tail, Values.get]
  rw [block_encode width (width + width) a position, block_encode width (width + width) m position]
  have mapped := dependencies.gates
    (fun bits => a (Quadratic.point width (vertex width position) bits))
    (fun bits => m (Quadratic.point width (vertex width position) bits))
    (GkrRoundsLayout.replicate width width v) (GkrRoundsLayout.tile width width v) pairBound
  dsimp only [GkrGateGoals.Map.Inputs.pack] at mapped
  rw [mapped]
  simp only [GkrGateGoals.Map.encode, PIR.Process.bind, Op.arguments, Op.results, Op.regions,
    SumcheckHelperLaws.prepend_empty, SumcheckHelperLaws.prepend_one,
    Environment.prepend, Environment.push, Values.get_head, Values.get_tail, Values.get]
  rw [← List.sum_eq_foldl, sum_encode]
  have formula : (fun bits => Zkc.Protocols.AlgebraicRounds.Gate.value
      (a (Quadratic.point width (vertex width position) bits))
      (m (Quadratic.point width (vertex width position) bits))
      (GkrRoundsLayout.replicate width width v bits)
      (GkrRoundsLayout.tile width width v bits)) =
        Zkc.Protocols.Gkr.gates
          (fun bits => a (Quadratic.point width (vertex width position) bits))
          (fun bits => m (Quadratic.point width (vertex width position) bits)) v := by
    funext bits
    exact gate_formula (width := width)
      (fun pair => a (Quadratic.point width (vertex width position) pair))
      (fun pair => m (Quadratic.point width (vertex width position) pair)) v bits
  rw [formula]
  rfl

/-- The complete actual helper33 loop, at every representable width. -/
theorem layer_encoded_body (table : Meanings F G) (dependencies : Dependencies table) {width : Nat}
    (a m : Zkc.Protocols.Gkr.Wiring F width)
    (v : Table F width) (small : width + width + width < 64) :
    Goals.Layer.body.denote (meaning F G table)
      (Goals.Layer.Inputs.pack (Value := assignment F G)
        { addWeights := GkrRoundsLayout.encode a, mulWeights := GkrRoundsLayout.encode m,
          below := GkrRoundsLayout.encode v, width }).get =
      .done (Goals.Layer.encode (ringModel F G) ⟨GkrRoundsLayout.encode (Zkc.Protocols.Gkr.layer a m v)⟩) := by
  have widthSmall : width < 64 := by omega
  have countBound : 2 ^ width < indexLimit := Nat.pow_lt_pow_right (by decide) widthSmall
  dsimp only [Goals.Layer.Inputs.pack]
  simp only [meaning]
  rw [Evaluation.denote_meaning_eq_meaningOn, Goals.layerProcess_equation]
  dsimp only [Goals.layerProcess, Goals.layerProcess_certificate, Op.arguments, Op.results, Op.regions]
  simp only [Op.arguments, Op.results, Op.regions, Primitive.evaluateOn, primitiveOutcome, PIR.Process.bind,
    SumcheckHelperLaws.prepend_empty, SumcheckHelperLaws.prepend_one,
    Environment.prepend, Environment.push, Values.get_head, Values.get_tail, Values.get,
    show 0 < indexLimit by decide +kernel, ite_true]
  have power := dependencies.power width widthSmall
  dsimp only [Goals.PowerArguments.pack, Goals.PowerResult.pack] at power
  rw [power]
  simp only [PIR.Process.bind, Op.arguments, Op.results, Op.regions,
    SumcheckHelperLaws.prepend_empty, SumcheckHelperLaws.prepend_one,
    Environment.prepend, Environment.push, Values.get_head, Values.get_tail, Values.get]
  have repeated := dependencies.replicate (GkrRoundsLayout.encode v) (2 ^ width)
    (by simpa [GkrRoundsLayout.encode] using countBound) countBound
  dsimp only [Goals.RepeatArguments.pack, Goals.RepeatResult.pack] at repeated
  rw [repeated]
  simp only [PIR.Process.bind, Op.arguments, Op.results, Op.regions,
    SumcheckHelperLaws.prepend_empty, SumcheckHelperLaws.prepend_one,
    Environment.prepend, Environment.push, Values.get_head, Values.get_tail, Values.get]
  have tiled := dependencies.tile (GkrRoundsLayout.encode v) (2 ^ width) countBound
    (by simpa [GkrRoundsLayout.encode] using countBound)
  dsimp only [Goals.RepeatArguments.pack, Goals.RepeatResult.pack] at tiled
  rw [tiled]
  simp only [PIR.Process.bind, Op.arguments, Op.results, Op.regions,
    SumcheckHelperLaws.prepend_empty, SumcheckHelperLaws.prepend_one,
    Environment.prepend, Environment.push, Values.get_head, Values.get_tail, Values.get]
  rw [← GkrRoundsLayout.encode_replicate, ← GkrRoundsLayout.encode_tile]
  rw [← Evaluation.denoteLoop_eq_denoteLoopOn]
  erw [denoteLoop_states (F := F) (G := G)
    Goals.LayerState.types Goals.LayerCaptures.types
    _ (2 ^ width) _
    (Goals.LayerCaptures.pack (Value := assignment F G)
      { addWeights := GkrRoundsLayout.encode a, mulWeights := GkrRoundsLayout.encode m, width,
        left := GkrRoundsLayout.encode (GkrRoundsLayout.replicate width width v),
        right := GkrRoundsLayout.encode (GkrRoundsLayout.tile width width v) })
    (fun i => Goals.LayerState.pack (Value := assignment F G)
      ⟨(GkrRoundsLayout.encode (Zkc.Protocols.Gkr.layer a m v)).take i⟩) ?_ ?_]
  · simp only [PIR.Process.bind, Op.arguments, Op.results, Op.regions,
    SumcheckHelperLaws.prepend_empty, SumcheckHelperLaws.prepend_one,
    Environment.prepend, Environment.push, Values.get_head, Values.get_tail, Values.get]
    rw [show 2 ^ width = (GkrRoundsLayout.encode (Zkc.Protocols.Gkr.layer a m v)).length by
      simp [GkrRoundsLayout.encode], List.take_length]
  · rfl
  · intro i bound
    have iteration := step_encoded table dependencies a m v
      ((GkrRoundsLayout.encode (Zkc.Protocols.Gkr.layer a m v)).take i) ⟨i, bound⟩ small
    simp only [Goals.Step.Inputs.pack, meaning] at iteration
    rw [Evaluation.denote_meaning_eq_meaningOn, Goals.stepProcess_equation] at iteration
    dsimp only [Goals.stepProcess, Goals.stepProcess_certificate] at iteration
    simp only [Evaluation.invokeCallback, Goals.LayerState.pack, Goals.LayerCaptures.pack,
      Values.append, PIR.Process.bind_assoc, Goals.Step.encode,
      Op.arguments, Op.results, Op.regions,
      SumcheckHelperLaws.prepend_empty, SumcheckHelperLaws.prepend_one,
      Environment.prepend, Environment.push, Values.get_head, Values.get_tail, Values.get,
      Primitive.evaluateOn, primitiveOutcome, PIR.Process.bind, Goals.Step.decode,
      show 1 < indexLimit by decide +kernel, ite_true] at iteration ⊢
    rw [iteration]
    rw [List.take_succ_eq_append_getElem (by simpa [GkrRoundsLayout.encode] using bound)]
    simp only [GkrRoundsLayout.encode, List.getElem_ofFn]

/-- The independent layer formula determines the new value; the complete
returned captures are the actual named input captures. -/
def stepReference {width : Nat} (a m : Zkc.Protocols.Gkr.Wiring F width)
    (v : Table F width) (position : Fin (2 ^ width))
    (_position : Nat) (values addWeights mulWeights : List F) (actualWidth : Nat)
    (left right : List F) : PIR.Outcome (Goals.Step.Output (ringModel F G)) :=
  .returned
    { values := values ++ [(Zkc.Protocols.Gkr.layer a m v) (vertex width position)],
      addWeights := addWeights, mulWeights := mulWeights, width := actualWidth,
      left := left, right := right }

def stepCondition {width : Nat} (a m : Zkc.Protocols.Gkr.Wiring F width)
    (v : Table F width) (position : Fin (2 ^ width)) :=
  fun (table : Meanings F G) (actualPosition : Nat) (_values addWeights mulWeights : List F)
      (actualWidth : Nat) (left right : List F) =>
    Dependencies table ∧ actualPosition = position.val ∧ addWeights = GkrRoundsLayout.encode a ∧
      mulWeights = GkrRoundsLayout.encode m ∧ actualWidth = width ∧
      left = GkrRoundsLayout.encode (GkrRoundsLayout.replicate width width v) ∧
      right = GkrRoundsLayout.encode (GkrRoundsLayout.tile width width v)

/-- The expected statement, including every capture, comes from the selected
callback. Only its mathematical reference and representation are chosen here. -/
theorem step {width : Nat} (a m : Zkc.Protocols.Gkr.Wiring F width)
    (v : Table F width) (position : Fin (2 ^ width)) (small : width + width + width < 64) :
    Goals.Step.Goal (ringModel F G) (stepReference a m v position) (stepCondition a m v position) := by
  intro table actualPosition values addWeights mulWeights actualWidth left right condition
  rcases condition with ⟨dependencies, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [← Goals.Step.run_eq, ← Evaluation.denote_meaning_eq_meaningOn]
  erw [step_encoded table dependencies a m v values position small]
  rfl

noncomputable def stepLaw {width : Nat} (a m : Zkc.Protocols.Gkr.Wiring F width)
    (v : Table F width) (position : Fin (2 ^ width)) (small : width + width + width < 64) :=
  Goals.Step.law (ringModel F G) (stepReference a m v position) (stepCondition a m v position)
    (step a m v position small)

def layerReference {width : Nat} (a m : Zkc.Protocols.Gkr.Wiring F width)
    (v : Table F width) (_addWeights _mulWeights _below : List F) (_width : Nat) :
    PIR.Outcome (Goals.Layer.Output (ringModel F G)) :=
  .returned ⟨GkrRoundsLayout.encode (Zkc.Protocols.Gkr.layer a m v)⟩

def layerCondition {width : Nat} (a m : Zkc.Protocols.Gkr.Wiring F width) (v : Table F width) :=
  fun (table : Meanings F G) (addWeights mulWeights below : List F) (actualWidth : Nat) =>
    Dependencies table ∧ addWeights = GkrRoundsLayout.encode a ∧
      mulWeights = GkrRoundsLayout.encode m ∧ below = GkrRoundsLayout.encode v ∧ actualWidth = width

theorem layer {width : Nat} (a m : Zkc.Protocols.Gkr.Wiring F width)
    (v : Table F width) (small : width + width + width < 64) :
    Goals.Layer.Goal (ringModel F G) (layerReference a m v) (layerCondition a m v) := by
  intro table addWeights mulWeights below actualWidth condition
  rcases condition with ⟨dependencies, rfl, rfl, rfl, rfl⟩
  rw [← Goals.Layer.run_eq, ← Evaluation.denote_meaning_eq_meaningOn]
  erw [layer_encoded_body table dependencies a m v small]
  rfl

noncomputable def layerLaw {width : Nat} (a m : Zkc.Protocols.Gkr.Wiring F width)
    (v : Table F width) (small : width + width + width < 64) :=
  Goals.Layer.law (ringModel F G) (layerReference a m v) (layerCondition a m v) (layer a m v small)

end ZkcSecurity.Realizations.Gkr.HonestCircuit.Companion
