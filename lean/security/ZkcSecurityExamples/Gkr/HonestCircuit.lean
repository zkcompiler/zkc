module

public import ZkcSecurity.Bindings.Gkr.CircuitEncodingLaws
public import ZkcExamples.Structured.GkrSourceLaws
public import ZkcSecurityExamples.Gkr.HonestHelpers
public import ZkcSecurityExamples.Components.GkrRoundsHelpers
public import Zkc.Protocols.Sumcheck.Source.VerifierHelpers

@[expose] public section

/-! The actual layer-value helper, with scalar and map equations derived from
its checked source associations. No helper correctness is assumed. -/

namespace ZkcSecurity.Realizations.Gkr.HonestCircuit
open Zkc Source Structured
open ZkcExamples.Structured GkrSourceViews GkrSourceLaws
open ZkcExamples.Structured.PrimitiveLibrary
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open ZkcSecurity.Examples.Components

set_option maxRecDepth 20000 in
structured_associations GkrSourceViews
  [helper31 := GkrSourceBodies.helper31, scopedHelper44 := GkrSourceBodies.scopedHelper44,
    scopedHelper42 := GkrSourceBodies.scopedHelper42, scopedHelper43 := GkrSourceBodies.scopedHelper43,
    helper33 := GkrSourceBodies.helper33, helper34 := GkrSourceBodies.helper34]

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The source gate callback is the independent gate formula. -/
theorem gate_equation (add mul left right : F) :
    invoke (helpers (G := G)) GkrSourceBodies.helper31Helper
      (.cons add (.cons mul (.cons left (.cons right .nil)))) =
        .done (.cons (Zkc.Protocols.AlgebraicRounds.Gate.value add mul left right) .nil) := by
  rw [helper31_association.invoke unit.linked]
  rfl

abbrev gateCollection : CollectSpec :=
  (collection? GkrSourceBodies.scopedHelper44Body).get (by decide +kernel)

/-- The ordered callback retains every input vector in its actual ABI. -/
theorem gate_callback (a m l r : F) (add mul left right : List F) :
    invoke (helpers (G := G)) gateCollection.bodyHelper
      (.cons a (.cons m (.cons l (.cons r
        (.cons add (.cons mul (.cons left (.cons right .nil)))))))) =
      .done (.cons (Zkc.Protocols.AlgebraicRounds.Gate.value (F := F) a m l r) .nil) := by
  change invoke (helpers (G := G)) GkrSourceBodies.scopedHelper43Helper
    (.cons a (.cons m (.cons l (.cons r
      (.cons add (.cons mul (.cons left (.cons right .nil)))))))) = _
  rw [scopedHelper43_association.invoke unit.linked]
  change (invoke (helpers (G := G)) GkrSourceBodies.scopedHelper42Helper
    (.cons a (.cons m (.cons l (.cons r .nil))))).bind _ = _
  rw [scopedHelper42_association.invoke unit.linked]
  change ((invoke (helpers (G := G)) GkrSourceBodies.helper31Helper
    (.cons a (.cons m (.cons l (.cons r .nil))))).bind _).bind _ = _
  rw [gate_equation]
  rfl

/-- Four arbitrary decoded tables, including every operand's shape. -/
theorem gate_map_encodes {n : Nat} (add mul left right : Table F n)
    (small : 2 ^ n < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.scopedHelper44Helper
      (.cons (GkrRoundsLayout.encode add) (.cons (GkrRoundsLayout.encode mul)
        (.cons (GkrRoundsLayout.encode left) (.cons (GkrRoundsLayout.encode right) .nil)))) =
      .done (.cons (GkrRoundsLayout.encode (fun bits =>
        Zkc.Protocols.AlgebraicRounds.Gate.value (add bits) (mul bits) (left bits) (right bits))) .nil) := by
  rw [scopedHelper44_association.invoke unit.linked]
  change (Evaluation.denoteCollect (helpers (G := G)) gateCollection
    (.cons (GkrRoundsLayout.encode add) (.cons (GkrRoundsLayout.encode mul)
      (.cons (GkrRoundsLayout.encode left) (.cons (GkrRoundsLayout.encode right) .nil))))).bind _ = _
  let entry := fun (table : Table F n) (i : Nat) => (GkrRoundsLayout.encode table)[i]?.getD 0
  let pack := fun i => (Values.cons (entry add i) (.cons (entry mul i)
    (.cons (entry left i) (.cons (entry right i) .nil))) :
      Values (assignment F G) gateCollection.domain.items)
  let formula := fun i => Zkc.Protocols.AlgebraicRounds.Gate.value
    (entry add i) (entry mul i) (entry left i) (entry right i)
  have domain := GkrRoundsHelpers.values_domain (G := G)
    (GkrRoundsLayout.encode add) (GkrRoundsLayout.encode mul)
    (GkrRoundsLayout.encode left) (GkrRoundsLayout.encode right)
  have shape : Evaluation.mapShape [2 ^ n, 2 ^ n, 2 ^ n, 2 ^ n] = .returned (2 ^ n) :=
    Evaluation.mapShape_of_equal _ _ small (by simp)
  simp only [GkrRoundsLayout.encode, List.length_ofFn, shape, Finite.continueWith] at domain
  have collected := Evaluation.denoteCollect_reference (helpers (F := F) (G := G)) gateCollection
    (.cons (GkrRoundsLayout.encode add) (.cons (GkrRoundsLayout.encode mul)
      (.cons (GkrRoundsLayout.encode left) (.cons (GkrRoundsLayout.encode right) .nil))))
    .nil (List.range (2 ^ n)) pack domain rfl formula (by
      intro i _; exact gate_callback _ _ _ _ _ _ _ _)
  simp only [Values.append] at collected
  rw [collected]
  have ordered : (List.range (2 ^ n)).map formula = GkrRoundsLayout.encode (fun bits =>
      Zkc.Protocols.AlgebraicRounds.Gate.value (add bits) (mul bits) (left bits) (right bits)) := by
    apply List.ext_getElem
    · simp [GkrRoundsLayout.encode]
    · intro i hi hj
      have bound : i < 2 ^ n := by simpa using hi
      simp [formula, entry, GkrRoundsLayout.encode, bound]
  rw [ordered]
  rfl

/-- The literal callback of helper33; this is checked against its structural
body in the proof of `layer_encodes`. -/
def layerLoopBody : Region dialect
    [.index, .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr",
      .index, .vector "bls12-381.fr", .vector "bls12-381.fr"]
    [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr",
      .index, .vector "bls12-381.fr", .vector "bls12-381.fr"] :=
    .letOp (.mark "s15") .nil .nil <|
    .letOp (.invoke ⟨"zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr"]⟩) (.cons (.there (.there .here)) (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil))) .nil <|
    .letOp (.mark "s17") .nil .nil <|
    .letOp (.invoke ⟨"zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr"]⟩) (.cons (.there (.there (.there (.there .here)))) (.cons (.there .here) (.cons (.there (.there (.there (.there (.there .here))))) .nil))) .nil <|
    .letOp (.mark "s19") .nil .nil <|
    .letOp (.invoke GkrSourceBodies.scopedHelper44Helper) (.cons (.there .here) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil)))) .nil <|
    .letOp (.mark "s20") .nil .nil <|
    .letOp (.exec (.vectorSum "bls12-381.fr")) (.cons .here .nil) .nil <|
    .letOp (.mark "s21") .nil .nil <|
    .letOp (.exec (.vectorAppend "bls12-381.fr")) (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil)) .nil <|
    .ret (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) .nil))))))


/-- The callback expansion is about the literal body, for any helper table. -/
theorem layer_step_body (table : Meanings F G) (position : Nat)
    (xs add mul : List F) (width : Nat) (left right : List F) :
    layerLoopBody.denote (meaning F G table)
      (Values.cons position (.cons xs (.cons add (.cons mul (.cons width
        (.cons left (.cons right .nil))))))).get =
      (invoke table GkrSourceBodies.selectBlockHelper
        (.cons add (.cons position (.cons width .nil)))).bind fun a =>
      (invoke table GkrSourceBodies.selectBlockHelper
        (.cons mul (.cons position (.cons width .nil)))).bind fun m =>
      (invoke table GkrSourceBodies.scopedHelper44Helper
        (.cons (a.get .here) (.cons (m.get .here) (.cons left (.cons right .nil))))).bind fun row =>
      .done (.cons (xs ++ [(row.get .here).foldl (· + ·) 0])
        (.cons add (.cons mul (.cons width (.cons left (.cons right .nil)))))) := by
  derive_process

/-- One actual loop iteration computes the independent value of one gate. -/
theorem layer_step_encodes {width : Nat} (a m : Zkc.Protocols.Gkr.Wiring F width)
    (v : Table F width) (xs : List F) (position : Fin (2 ^ width))
    (small : width + width + width < 64) :
    layerLoopBody.denote (meaning F G (helpers (G := G)))
      (Values.cons position.val (.cons xs (.cons (GkrRoundsLayout.encode a)
        (.cons (GkrRoundsLayout.encode m) (.cons width
          (.cons (GkrRoundsLayout.encode (GkrRoundsLayout.replicate width width v))
            (.cons (GkrRoundsLayout.encode (GkrRoundsLayout.tile width width v)) .nil))))))).get =
      .done (.cons (xs ++ [(Zkc.Protocols.Gkr.layer a m v) (vertex width position)])
        (.cons (GkrRoundsLayout.encode a) (.cons (GkrRoundsLayout.encode m) (.cons width
          (.cons (GkrRoundsLayout.encode (GkrRoundsLayout.replicate width width v))
            (.cons (GkrRoundsLayout.encode (GkrRoundsLayout.tile width width v)) .nil)))))) := by
  have bound : 2 ^ (width + width + width) < indexLimit :=
    Nat.pow_lt_pow_right (by decide) small
  have pairBound : 2 ^ (width + width) < indexLimit :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  have shape : (GkrRoundsLayout.encode a).length = 2 ^ width * 2 ^ (width + width) := by
    simp [GkrRoundsLayout.encode, Nat.pow_add, Nat.mul_comm]
  have shapeM : (GkrRoundsLayout.encode m).length = 2 ^ width * 2 ^ (width + width) := by
    simp [GkrRoundsLayout.encode, Nat.pow_add, Nat.mul_comm]
  rw [layer_step_body,
    selectBlock_equation _ position.val width (2 ^ (width + width)) shape (by positivity)
      position.isLt (by simpa [GkrRoundsLayout.encode] using bound)]
  simp only [PIR.Process.bind, Values.get]
  rw [selectBlock_equation _ position.val width (2 ^ (width + width)) shapeM (by positivity)
    position.isLt (by simpa [GkrRoundsLayout.encode] using bound)]
  simp only [PIR.Process.bind, Values.get]
  rw [block_encode width (width + width) a position, block_encode width (width + width) m position,
    gate_map_encodes _ _ _ _ pairBound]
  simp only [PIR.Process.bind, Values.get]
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

/-- Structural expansion of helper33, retaining the actual counted callback. -/
theorem layer_body (table : Meanings F G) (add mul below : List F) (width : Nat) :
    GkrSourceBodies.helper33Body.denote (meaning F G table)
      (Values.cons add (.cons mul (.cons below (.cons width .nil)))).get =
      (invoke table GkrSourceBodies.helper18Helper (.cons width .nil)).bind fun count =>
      (invoke table GkrSourceBodies.helper25Helper (.cons below (.cons (count.get .here) .nil))).bind fun left =>
      (invoke table GkrSourceBodies.helper30Helper (.cons below (.cons (count.get .here) .nil))).bind fun right =>
      (Evaluation.denoteLoop [.vector "bls12-381.fr"]
        [.vector "bls12-381.fr", .vector "bls12-381.fr", .index,
          .vector "bls12-381.fr", .vector "bls12-381.fr"]
        (fun args => layerLoopBody.denote (meaning F G table) args.get) 0 (count.get .here)
        (.cons [] .nil) (.cons add (.cons mul (.cons width
          (.cons (left.get .here) (.cons (right.get .here) .nil)))))).bind fun result =>
        .done (.cons (result.get .here) .nil) := by
  simp only [GkrSourceBodies.helper33Body, layerLoopBody, Region.denote, meaning, Evaluation.meaning,
    Evaluation.operation, Operands.eval, Regions.denote, Values.get_cons, Values.get,
    SumcheckHelperLaws.prepend_empty, SumcheckHelperLaws.prepend_one,
    Environment.push, SiteObservations.closed, SiteObservations.silent,
    PIR.Process.bind, Primitive.evaluate, primitiveOutcome,
    show 0 < indexLimit by decide +kernel, ite_true, Values.split]
  rfl

/-- The complete actual helper33 loop, at every representable width. -/
theorem layer_encoded {width : Nat} (a m : Zkc.Protocols.Gkr.Wiring F width)
    (v : Table F width) (small : width + width + width < 64) :
    invoke (helpers (G := G)) GkrSourceBodies.helper33Helper
      (.cons (GkrRoundsLayout.encode a) (.cons (GkrRoundsLayout.encode m)
        (.cons (GkrRoundsLayout.encode v) (.cons width .nil)))) =
      .done (.cons (GkrRoundsLayout.encode (Zkc.Protocols.Gkr.layer a m v)) .nil) := by
  have widthSmall : width < 64 := by omega
  have countBound : 2 ^ width < indexLimit := Nat.pow_lt_pow_right (by decide) widthSmall
  rw [helper33_association.invoke unit.linked]
  rw [layer_body]
  rw [powerOfTwo_equation width widthSmall]
  simp only [PIR.Process.bind, Values.get]
  rw [HonestHelpers.replicate_equation _ _ (by simpa [GkrRoundsLayout.encode] using countBound) countBound]
  simp only [PIR.Process.bind, Values.get]
  rw [HonestHelpers.tile_equation _ _ countBound (by simpa [GkrRoundsLayout.encode] using countBound)]
  simp only [PIR.Process.bind, Values.get]
  rw [← GkrRoundsLayout.encode_replicate, ← GkrRoundsLayout.encode_tile]
  rw [denoteLoop_states (F := F) (G := G) [.vector "bls12-381.fr"]
    [.vector "bls12-381.fr", .vector "bls12-381.fr", .index,
      .vector "bls12-381.fr", .vector "bls12-381.fr"] _ (2 ^ width) _
    (.cons (GkrRoundsLayout.encode a) (.cons (GkrRoundsLayout.encode m) (.cons width
      (.cons (GkrRoundsLayout.encode (GkrRoundsLayout.replicate width width v))
        (.cons (GkrRoundsLayout.encode (GkrRoundsLayout.tile width width v)) .nil)))))
    (fun i => .cons ((GkrRoundsLayout.encode (Zkc.Protocols.Gkr.layer a m v)).take i) .nil) ?_ ?_]
  · simp only [PIR.Process.bind, Values.get]
    rw [show 2 ^ width = (GkrRoundsLayout.encode (Zkc.Protocols.Gkr.layer a m v)).length by
      simp [GkrRoundsLayout.encode], List.take_length]
  · rfl
  · intro i bound
    simp only [Evaluation.invokeCallback, Values.append]
    change layerLoopBody.denote (meaning F G (helpers (G := G))) _ = _
    rw [layer_step_encodes a m v _ ⟨i, bound⟩ small]
    simp only [Values.append]
    rw [List.take_succ_eq_append_getElem (by simpa [GkrRoundsLayout.encode] using bound)]
    simp only [GkrRoundsLayout.encode, List.getElem_ofFn]

/-- Arbitrary exact raw encodings compute the independent circuit layer. -/
theorem layer_encodes {width : Nat} (add mul below : List F)
    (a m : Zkc.Protocols.Gkr.Wiring F width) (v : Table F width)
    (da : ofList? (width + width + width) add = some a)
    (dm : ofList? (width + width + width) mul = some m)
    (dv : ofList? width below = some v) (small : width + width + width < 64) :
    invoke (helpers (G := G)) GkrSourceBodies.helper33Helper
      (.cons add (.cons mul (.cons below (.cons width .nil)))) =
        .done (.cons (GkrRoundsLayout.encode (Zkc.Protocols.Gkr.layer a m v)) .nil) := by
  rw [← HonestHelpers.encode_of_decodes add a da, ← HonestHelpers.encode_of_decodes mul m dm,
    ← HonestHelpers.encode_of_decodes below v dv]
  exact layer_encoded a m v small

end ZkcSecurity.Realizations.Gkr.HonestCircuit
