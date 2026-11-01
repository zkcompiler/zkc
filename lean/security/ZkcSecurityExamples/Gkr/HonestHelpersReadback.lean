module

public import ZkcSecurityExamples.Gkr.HonestHelpers
public import ZkcSecurityExamples.Gkr.HonestHelpersReadbackCompanion
public import Zkc.Source.Structured.DomainContract

@[expose] public section

/-! Install the chosen list readback mathematics into the actual producer's
helper table. Consumers share the checked installation and its complete equations. -/
namespace ZkcSecurity.Realizations.Gkr.HonestHelpers
open Zkc Source Structured
open ZkcExamples.Structured GkrSourceViews GkrSourceLaws
open ReadbackGoals
open ZkcExamples.Structured.PrimitiveLibrary

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

set_option maxRecDepth 20000 in
theorem readback_bodies : Bodies unit.definitions := by
  bind_structured_bodies

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Checked once for all producer consumers, including every dependent helper. -/
theorem readback_laws : ReadbackCompanion.Laws (ringModel F G)
    (closedMeaningsOn (ringModel F G) unit.definitions) :=
  ReadbackCompanion.install (ringModel F G) unit.definitions unit.linked readback_bodies

theorem zero_equation :
    invoke (helpers (F := F) (G := G)) GkrSourceBodies.scopedHelper74Helper (Zero.Inputs.pack {}) =
      .done (ZeroWrapper.encode (ringModel F G) ⟨0⟩) := by
  simp only [helpers, closedMeanings_eq_closedMeaningsOn]
  exact readback_laws.zeroWrapper .nil

theorem read_fold (xs : List F) (position offset : Nat) (current : F)
    (positionBound : position < indexLimit) (bound : offset + xs.length < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.scopedHelper82Helper
      (Scan.Inputs.pack { source := xs, current, index := offset, position }) =
      .done (Scan.encode (ringModel F G)
        { selected := if offset ≤ position then xs[position - offset]?.getD current else current,
          nextIndex := offset + xs.length }) := by
  simp only [helpers, closedMeanings_eq_closedMeaningsOn]
  have law := (readback_laws (F := F) (G := G)).scan
    (Scan.Inputs.pack { source := xs, current, index := offset, position })
  simpa [ReadbackCompanion.scanLaw, Scan.law, ReadbackCompanion.scanReference,
    show xs.length < indexLimit from by omega,
    Zkc.Algorithms.ListReadback.scan_bounded indexLimit position xs current offset positionBound bound,
    Scan.Inputs.pack, Scan.encodeOutcome, Scan.encode, primitiveOutcome] using law

/-- Exact readback through the actual linked table, retaining the scan's index
bound even when the selected position is outside the list. -/
theorem element_equation (xs : List F) (position : Nat)
    (xsBound : xs.length < indexLimit) (positionBound : position < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.helper57Helper (Element.Inputs.pack { source := xs, position }) =
      .done (Element.encode (ringModel F G) ⟨xs[position]?.getD 0⟩) := by
  simp only [helpers, closedMeanings_eq_closedMeaningsOn]
  have law := (readback_laws (F := F) (G := G)).element
    (Element.Inputs.pack { source := xs, position })
  simpa [ReadbackCompanion.elementLaw, Element.law, ReadbackCompanion.elementReference,
    ReadbackCompanion.scanReference, xsBound,
    Zkc.Algorithms.ListReadback.scan_bounded indexLimit position xs (0 : F) 0 positionBound
      (by simpa using xsBound),
    Element.Inputs.pack, Element.encodeOutcome, Element.encode, primitiveOutcome] using law

theorem element_after_equation (xs : List F) (position : Nat)
    (xsBound : xs.length < indexLimit) (positionBound : position + 1 < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.helper70Helper (Element.Inputs.pack { source := xs, position }) =
      .done (After.encode (ringModel F G) ⟨xs[position + 1]?.getD 0⟩) := by
  simp only [helpers, closedMeanings_eq_closedMeaningsOn]
  have law := (readback_laws (F := F) (G := G)).after
    (Element.Inputs.pack { source := xs, position })
  simpa [ReadbackCompanion.afterLaw, After.law, ReadbackCompanion.afterReference,
    ReadbackCompanion.elementReference, ReadbackCompanion.scanReference, xsBound, positionBound,
    Zkc.Algorithms.ListReadback.scan_bounded indexLimit (position + 1) xs (0 : F) 0 positionBound
      (by simpa using xsBound),
    Element.Inputs.pack, After.encodeOutcome, After.encode, primitiveOutcome] using law

/-- The checked successor refuses overflow before any vector admission. -/
theorem element_after_overflow (xs : List F) (position : Nat)
    (overflow : ¬ position + 1 < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.helper70Helper (Element.Inputs.pack { source := xs, position }) =
      .halt .refused := by
  simp only [helpers, closedMeanings_eq_closedMeaningsOn]
  have law := (readback_laws (F := F) (G := G)).after
    (Element.Inputs.pack { source := xs, position })
  simpa [ReadbackCompanion.afterLaw, After.law, ReadbackCompanion.afterReference, overflow,
    Element.Inputs.pack, After.encodeOutcome, primitiveOutcome] using law

end ZkcSecurity.Realizations.Gkr.HonestHelpers
