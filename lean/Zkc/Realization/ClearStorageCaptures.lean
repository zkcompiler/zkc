module

public import Zkc.Realization.ClearStorage
public import Zkc.Realization.CaptureLayout

@[expose] public section

/-! Base publication records supply the handle association in a virtual closure.
This adapter uses the actual storage relation: constructing a capture does not
introduce an independent or author-selected map from handles to words. -/

set_option autoImplicit false
namespace Zkc.Realization.ClearStorage
open Zkc.Source Zkc.Source.Structured
variable {kind : OracleKind} {model : DomainModel}

/-- The reference view of one immutable constructor. Combining several
constructors requires disjoint physical tags in the controller installation. -/
def references (layout : Layout kind) (words : PublishedWords.Table model)
    (records : List (model.Value layout.recordType)) : CaptureLayout.References :=
  fun requested identity anchor physical ↦ requested = kind ∧ identity = layout.referenceIdentity ∧
    ∃ word, word.anchor = anchor ∧ Stored layout words records physical word

theorem references_unambiguous (layout : Layout kind) (words : PublishedWords.Table model)
    (records : List (model.Value layout.recordType)) :
    CaptureLayout.Unambiguous (references layout words records) := by
  rintro _ _ _ _ _ ⟨_, _, first, rfl, left⟩ ⟨_, _, second, rfl, right⟩
  exact left.anchor_unique right

/-- This view remains valid after permitted provider changes and physical
append, so virtual captures need no new preservation premise about their data. -/
theorem references_transport (layout : Layout kind)
    {before after : PublishedWords.Table model}
    {records later : List (model.Value layout.recordType)}
    (provider : PublishedWords.Preserves before after) (physical : records <+: later)
    (requested : OracleKind) (identity : String) (anchor : OracleAnchor) (reference : Nat × Nat)
    (stored : references layout before records requested identity anchor reference) :
    references layout after later requested identity anchor reference := by
  obtain ⟨nominal, name, word, anchorAt, found⟩ := stored
  exact ⟨nominal, name, word, anchorAt, found.transport provider physical⟩

end Zkc.Realization.ClearStorage
