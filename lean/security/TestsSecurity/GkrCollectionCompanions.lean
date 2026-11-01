import ZkcSecurityExamples.Gkr.HonestHelpersLayout

/-! Focused collection controls. Actual producer helpers use their admitted
bodies and linked table. Synthetic helper tables and the changed caller below
are explicitly source fixtures, not compiled GKR protocol endpoints. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace TestsSecurity.GkrCollectionCompanions
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open ZkcSecurity.Realizations.Gkr.HonestHelpers
open CollectionGoals CollectionCompanion

private abbrev model := ringModel Int Int

example : invoke (GkrSourceLaws.helpers (F := Int) (G := Int)) GkrSourceBodies.helper25Helper
    (Replicate.Inputs.pack { source := [3, 5], count := 2 }) =
      .done (Replicate.encode model ⟨[3, 3, 5, 5]⟩) :=
  replicate_equation [3, 5] 2 (by decide +kernel) (by decide +kernel)

example : invoke (GkrSourceLaws.helpers (F := Int) (G := Int)) GkrSourceBodies.helper30Helper
    (Replicate.Inputs.pack { source := [3, 5], count := 2 }) =
      .done (Tile.encode model ⟨[3, 5, 3, 5]⟩) :=
  tile_equation [3, 5] 2 (by decide +kernel) (by decide +kernel)

example : invoke (GkrSourceLaws.helpers (F := Int) (G := Int)) GkrSourceBodies.helper29Helper
    (Concatenate.Inputs.pack { initial := [7], source := [3, 5] }) =
      .done (Concatenate.encode model ⟨[7, 3, 5]⟩) := by
  simp only [GkrSourceLaws.helpers, closedMeanings_eq_closedMeaningsOn]
  have law := (collection_laws (F := Int) (G := Int)).concatenate
    (Concatenate.Inputs.pack { initial := [7], source := [3, 5] })
  exact law

example : invoke (GkrSourceLaws.helpers (F := Int) (G := Int)) GkrSourceBodies.helper36Helper
    (Layout.Inputs.pack { add := [2], mul := [3], point := [], below := [7], width := 0 }) =
      .done (Layout.encode model ⟨[2], [3], [7], [7]⟩) :=
  layout_equation [2] [3] [7] [] 0 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

-- Nontrivial width distinguishes every payload, including replication versus tiling.
example : invoke (GkrSourceLaws.helpers (F := Int) (G := Int)) GkrSourceBodies.helper36Helper
    (Layout.Inputs.pack
      { add := [1, 2, 3, 4], mul := [5, 6, 7, 8], point := [], below := [3, 5], width := 1 }) =
      .done (Layout.encode model ⟨[1, 2, 3, 4], [5, 6, 7, 8], [3, 3, 5, 5], [3, 5, 3, 5]⟩) :=
  layout_equation [1, 2, 3, 4] [5, 6, 7, 8] [3, 5] [] 1 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

-- Empty admitted domains do not call a missing callback, preserving initial state.
example : AppendFold.run model [] [] [7] = .done ⟨[7]⟩ := rfl
example : ReplicateFold.run model [] [] [7] indexLimit = .done ⟨[7]⟩ := rfl
example : Tile.run model [] [] 0 = .done ⟨[]⟩ := rfl
example : Repeat.run model [] [7] 3 0 = .done ⟨[7]⟩ := rfl

/-- Actual vector admission precedes the missing fold callback, even at count zero. -/
theorem replicate_exhausted (source : List Int) (exhausted : ¬ source.length < indexLimit) :
    invoke (GkrSourceLaws.helpers (F := Int) (G := Int)) GkrSourceBodies.helper25Helper
      (Replicate.Inputs.pack { source, count := 0 }) = .halt .exhausted := by
  simp only [GkrSourceLaws.helpers, closedMeanings_eq_closedMeaningsOn]
  have law := (collection_laws (F := Int) (G := Int)).replicated
    (Replicate.Inputs.pack { source, count := 0 })
  change _ = primitiveOutcome (Replicate.encodeOutcome model (replicateReference model source 0)) at law
  simpa only [replicateReference, exhausted, ↓reduceIte, Replicate.encodeOutcome, primitiveOutcome] using law

/-- Tile has no up-front vector admission: its zero loop never calls concatenation. -/
theorem tile_zero_unadmitted (source : List Int) :
    invoke (GkrSourceLaws.helpers (F := Int) (G := Int)) GkrSourceBodies.helper30Helper
      (Replicate.Inputs.pack { source, count := 0 }) = .done (Tile.encode model ⟨[]⟩) := by
  simp only [GkrSourceLaws.helpers, closedMeanings_eq_closedMeaningsOn]
  exact (collection_laws (F := Int) (G := Int)).tiled (Replicate.Inputs.pack { source, count := 0 })

theorem tile_exhausted (source : List Int) (exhausted : ¬ source.length < indexLimit) :
    invoke (GkrSourceLaws.helpers (F := Int) (G := Int)) GkrSourceBodies.helper30Helper
      (Replicate.Inputs.pack { source, count := 1 }) = .halt .exhausted := by
  simp only [GkrSourceLaws.helpers, closedMeanings_eq_closedMeaningsOn]
  have law := (collection_laws (F := Int) (G := Int)).tiled
    (Replicate.Inputs.pack { source, count := 1 })
  change _ = primitiveOutcome (Tile.encodeOutcome model (tileReference model source 1)) at law
  simpa only [tileReference, exhausted, ↓reduceIte, Finite.repeatAppend,
    Finite.continueWith, Tile.encodeOutcome, primitiveOutcome] using law

-- The actual finite domain is admitted before looking up any callback.
example (source : List Int) (exhausted : ¬ source.length < indexLimit) :
    ReplicateFold.run model [] source [7] indexLimit = .halt .exhausted := by
  collection_simp [ReplicateFold.run, Evaluation.denoteFoldOn, DomainSpec.admit,
    DomainBody.admit, DomainNode.admit, Collection.values, Finite.continueWith,
    Finite.admitThen, exhausted]

-- A reached missing callback still fails; the empty-domain controls above do not call it.
example : AppendFold.run model [] [3] [7] = .halt .refused := rfl

-- Synthetic stopping dependency, retaining the actual complete layout body.
private def abortPower : Evaluation.MeaningsOn model.toCarriers closedInterface :=
  [⟨GkrSourceBodies.helper18Helper, fun _ => .halt .abort⟩]

/-- The first helper stops before the layout even reads an exhausted point. -/
example (point : List Int) (_exhausted : ¬ point.length < indexLimit) :
    Layout.run model abortPower [] [] point [] 0 = .halt .abort := by
  rfl

-- Synthetic changed source fixture: reordered inputs, a retained Boolean,
-- an extra marked helper boundary, and the actual collection dependency.
private def variantHelper : Helper :=
  ⟨"collection-with-context", .local, [.index, .boolean, .vector scalarDomain], [.vector scalarDomain]⟩

private def variantBody : Region dialect variantHelper.inputs variantHelper.outputs :=
  .letOp (.mark "expanded") .nil .nil <|
  .letOp (.invoke GkrSourceBodies.helper25Helper)
    (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

helper_presentation Variant inputs [copies, retained, batch] outputs [expanded] := variantBody
named_values VariantArguments [copies, retained, batch] := variantHelper.inputs

private def variantLibrary := forward_reference% Variant.body using (replicateLaw model)

private def variantReference (copies : Nat) (_retained : Bool) (batch : List Int) :
    PIR.Outcome (Variant.Output model) :=
  if batch.length < indexLimit then .returned ⟨batch.flatMap (List.replicate copies)⟩
  else .stopped .exhausted

theorem variant_companion : Variant.Goal model variantReference
    (fun table _ _ _ => (replicateLaw model).Realizes (helper := GkrSourceBodies.helper25Helper) table) := by
  apply Variant.of_law model _ _ variantLibrary rfl
  · intro copies retained batch
    by_cases bounded : batch.length < indexLimit <;>
      collection_simp [variantLibrary, replicateLaw, Replicate.law, replicateReference, bounded,
        Replicate.encodeOutcome, Replicate.encode, variantReference, Variant.encodeOutcome, Variant.encode]
  · intro table copies retained batch dependency; exact dependency _

private def definition (helper : Helper) (body : Region dialect helper.inputs helper.outputs) :
    CheckedDefinition :=
  ⟨helper.name, helper.kind, helper.inputs, helper.outputs, body.erase, body, body.elaborate_erase⟩

private def alteredAppend := definition GkrSourceBodies.helper26Helper (.stop .abort)

/-- A matching helper name and ABI cannot replace the actual append body. -/
theorem altered_append_not_associated :
    ¬ BodyIn [alteredAppend] GkrSourceBodies.helper26Helper Append.body := by
  rintro ⟨selected, member, _, same⟩
  simp only [List.mem_singleton] at member
  subst selected
  cases same

private def variantDefinition := definition variantHelper variantBody
private def definitions :=
  [definition GkrSourceBodies.helper20Helper Repeat.body,
    definition GkrSourceBodies.helper21Helper RepeatWrapper.body,
    definition GkrSourceBodies.helper22Helper ReplicateStep.body,
    definition GkrSourceBodies.scopedHelper45Helper ReplicateFold.body,
    definition GkrSourceBodies.helper24Helper ReplicateWrapper.body,
    definition GkrSourceBodies.helper25Helper Replicate.body,
    definition GkrSourceBodies.helper26Helper Append.body,
    definition GkrSourceBodies.helper27Helper AppendStep.body,
    definition GkrSourceBodies.scopedHelper48Helper AppendFold.body,
    definition GkrSourceBodies.helper29Helper Concatenate.body,
    definition GkrSourceBodies.helper30Helper Tile.body,
    variantDefinition]

set_option maxRecDepth 20000 in
private theorem linked : DeclarationsLinked [] definitions := by decide +kernel

private theorem bodies : Bodies definitions := by bind_structured_bodies

private def variantLaw := Variant.law model variantReference
  (fun table _ _ _ => (replicateLaw model).Realizes (helper := GkrSourceBodies.helper25Helper) table)
  variant_companion

/-- Reassembly checks the changed caller's body and all actual dependencies. -/
theorem variant_actual (copies : Nat) (retained : Bool) (batch : List Int) :
    invoke (closedMeaningsOn model definitions) variantHelper
      (VariantArguments.pack { copies, retained, batch }) =
      primitiveOutcome (Variant.encodeOutcome model (variantReference copies retained batch)) := by
  apply variantLaw.invoke (helper := variantHelper) definitions linked
  · bind_structured_bodies
  · exact (install model definitions linked bodies).replicated

example : invoke (closedMeaningsOn model definitions) variantHelper
    (VariantArguments.pack { copies := 2, retained := true, batch := [3, 5] }) =
      .done (Variant.encode model ⟨[3, 3, 5, 5]⟩) := by
  rw [variant_actual]
  rfl

example : invoke (closedMeaningsOn model definitions) variantHelper
    (VariantArguments.pack { copies := indexLimit, retained := false, batch := [] }) =
      .done (Variant.encode model ⟨[]⟩) := by
  rw [variant_actual]
  rfl

-- A complete goal cannot silently swap replication and tiling.
theorem swapped_order_refused :
    ¬ Variant.Goal model
      (fun copies _ batch => .returned ⟨(List.replicate copies batch).flatten⟩)
      (fun _ _ _ _ => True) := by
  intro wrong
  have actual := variant_companion (closedMeaningsOn model definitions) 2 true [3, 5]
    (install model definitions linked bodies).replicated
  have claimed := wrong (closedMeaningsOn model definitions) 2 true [3, 5] True.intro
  have impossible := congrArg Variant.Output.expanded (PIR.Process.done.inj (actual.symm.trans claimed))
  cases impossible

#print axioms CollectionGoals.Repeat.equation
#print axioms CollectionCompanion.install
#print axioms Zkc.Source.Structured.Evaluation.denoteLoopOn_repeatAppend
#print axioms variant_actual

end TestsSecurity.GkrCollectionCompanions
