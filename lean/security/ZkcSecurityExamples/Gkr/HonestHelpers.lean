module

public import ZkcSecurityExamples.Gkr.HonestCollectionCompanion
public import ZkcSecurity.Bindings.Gkr.RoundsLayout

@[expose] public section

/-! Install the list collection mathematics in the actual admitted producer.
Public result rows use generated encodings, definitionally preserving the
existing raw ABI. Mathematical shape and capacity assumptions stay explicit. -/
namespace ZkcSecurity.Realizations.Gkr.HonestHelpers
open Zkc Source Structured
open ZkcExamples.Structured GkrSourceViews GkrSourceLaws
open ZkcExamples.Structured.PrimitiveLibrary
open Zkc.Polynomial.Multilinear
open CollectionGoals CollectionCompanion

set_option maxRecDepth 20000 in
structured_associations GkrSourceViews
  [helper20 := GkrSourceBodies.helper20, helper35 := GkrSourceBodies.helper35,
    helper36 := GkrSourceBodies.helper36]

set_option maxRecDepth 20000 in
theorem collection_bodies : CollectionGoals.Bodies unit.definitions := by
  bind_structured_bodies

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
attribute [local implicit_reducible] Op.arguments Op.results Op.regions Primitive.arguments Primitive.results

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem collection_laws : CollectionCompanion.Laws (ringModel F G)
    (closedMeaningsOn (ringModel F G) unit.definitions) :=
  CollectionCompanion.install (ringModel F G) unit.definitions unit.linked collection_bodies

/-- The original arbitrary-table repeat equation, with its original telescope. -/
theorem repeat_body (table : Meanings F G) (xs : List F) (value : F) (count : Nat)
    (_small : count < indexLimit) :
    GkrSourceBodies.helper20Body.denote (meaning F G table)
      (RepeatArguments.pack { initial := xs, value, count }).get =
        .done (Repeat.encode (ringModel F G) ⟨xs ++ List.replicate count value⟩) := by
  rw [Evaluation.denote_meaning_eq_meaningOn]
  exact (repeatLaw (ringModel F G)).valid table
    (RepeatArguments.pack { initial := xs, value, count }) True.intro

theorem replicate_equation (source : List F) (count : Nat)
    (sourceBound : source.length < indexLimit) (small : count < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.helper25Helper
      (ReplicateArguments.pack { source, count }) =
        .done (Replicate.encode (ringModel F G) ⟨source.flatMap (List.replicate count)⟩) := by
  have _countBound := small
  simp only [helpers, closedMeanings_eq_closedMeaningsOn]
  simpa [replicateLaw, Replicate.law, replicateReference, sourceBound,
    ReplicateArguments.pack, Replicate.encodeOutcome, primitiveOutcome] using
    (collection_laws (F := F) (G := G)).replicated (ReplicateArguments.pack { source, count })

theorem tile_equation (source : List F) (count : Nat) (small : count < indexLimit)
    (sourceBound : source.length < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.helper30Helper
      (ReplicateArguments.pack { source, count }) =
        .done (Tile.encode (ringModel F G) ⟨(List.replicate count source).flatten⟩) := by
  have _countBound := small
  simp only [helpers, closedMeanings_eq_closedMeaningsOn]
  simpa [tileLaw, Tile.law, tileReference, sourceBound, Finite.repeatAppend_returned,
    ReplicateArguments.pack, Tile.encodeOutcome, primitiveOutcome] using
    (collection_laws (F := F) (G := G)).tiled (ReplicateArguments.pack { source, count })

/-- Prefix restriction through the producer's wrapper, with all shape checks. -/
theorem prefix_equation (xs point : List F) (dimension : Nat)
    (shape : HasShape xs dimension 1)
    (xsBound : xs.length < indexLimit) (dimensionBound : dimension < indexLimit)
    (pointBound : point.length < indexLimit) (inside : point.length ≤ dimension) :
    invoke (helpers (G := G)) GkrSourceBodies.helper35Helper
      (PrefixArguments.pack { source := xs, dimension, point }) =
        .done (Prefix.encode (ringModel F G) ⟨restrictPrefixValues xs point⟩) := by
  rw [helper35_association.invoke unit.linked, Evaluation.denote_meaning_eq_meaningOn]
  erw [prefixProcess_equation]
  collection_simp [prefixProcess, prefixProcess_certificate]
  erw [prefix_laws.tableLaw xs dimension 1 xsBound dimensionBound (by decide +kernel),
    ite_eq_left shape]
  collection_simp []
  erw [prefix_laws.fixPrefix xs dimension 1 point shape xsBound pointBound, ite_eq_left inside]
  collection_simp []
  erw [prefix_laws.values]
  rfl

/-- All four outputs of the actual `layer_gates` helper, in source order. -/
theorem layout_equation (add mul below point : List F) (width : Nat)
    (widthSmall : width < 64)
    (addShape : HasShape add (point.length + width + width) 1)
    (mulShape : HasShape mul (point.length + width + width) 1)
    (addBound : add.length < indexLimit) (mulBound : mul.length < indexLimit)
    (belowBound : below.length < indexLimit)
    (dimensionBound : point.length + width + width < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.helper36Helper
      (LayoutArguments.pack { add, mul, point, below, width }) =
        .done (Layout.encode (ringModel F G)
          { addValues := restrictPrefixValues add point,
            mulValues := restrictPrefixValues mul point,
            leftValues := below.flatMap (List.replicate (2 ^ width)),
            rightValues := (List.replicate (2 ^ width) below).flatten }) := by
  have pointBound : point.length < indexLimit := by omega
  have sumBound : point.length + width < indexLimit := by omega
  have powerBound : 2 ^ width < indexLimit := Nat.pow_lt_pow_right (by decide) widthSmall
  have widthBound : width < indexLimit := by omega
  rw [helper36_association.invoke unit.linked, Evaluation.denote_meaning_eq_meaningOn]
  erw [layoutProcess_equation]
  collection_simp [layoutProcess, layoutProcess_certificate]
  rw [powerOfTwo_equation width widthSmall]
  collection_simp [checkedIndices, pointBound, sumBound, dimensionBound, widthBound]
  erw [prefix_equation add point _ addShape addBound dimensionBound pointBound (by omega)]
  collection_simp [Prefix.encode]
  erw [prefix_equation mul point _ mulShape mulBound dimensionBound pointBound (by omega)]
  collection_simp [Prefix.encode]
  erw [replicate_equation below _ belowBound powerBound]
  collection_simp [Replicate.encode]
  erw [tile_equation below _ powerBound belowBound]
  rfl

end ZkcSecurity.Realizations.Gkr.HonestHelpers
