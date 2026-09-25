import Zkc.Semantics.Relation
import Mathlib.Logic.Equiv.Defs

/-! Relation adapters over the existing statement/witness family. An encoding
may introduce auxiliary witnesses and reorder either boundary. Its soundness
law covers every satisfying target assignment at the selected statement map.
No executable importer or protocol security theorem is supplied by this type.
-/

set_option autoImplicit false

namespace Zkc.Relation

open PIR.Relation

/-- Witness correspondence is relational: auxiliary assignments need not be
unique, and recovering a source witness need not be an executable function. -/
structure Encoding (source target : Family) where
  statementMap : source.Statement → target.Statement
  corresponds : source.Statement → source.Witness → target.Witness → Prop
  complete : ∀ s w, source.holds s w →
    ∃ z, target.holds (statementMap s) z ∧ corresponds s w z
  sound : ∀ s z, target.holds (statementMap s) z →
    ∃ w, source.holds s w ∧ corresponds s w z

namespace Encoding

variable {source middle target : Family}

theorem valid_iff (encoding : Encoding source target) (s : source.Statement) :
    Valid source s ↔ Valid target (encoding.statementMap s) := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨z, hz, _⟩ := encoding.complete s w hw
    exact ⟨z, hz⟩
  · rintro ⟨z, hz⟩
    obtain ⟨w, hw, _⟩ := encoding.sound s z hz
    exact ⟨w, hw⟩

/-- Compose the actual statement maps and retain the intermediate witness. -/
def comp (first : Encoding source middle) (next : Encoding middle target) :
    Encoding source target where
  statementMap := next.statementMap ∘ first.statementMap
  corresponds s w z := ∃ v, first.corresponds s w v ∧
    next.corresponds (first.statementMap s) v z
  complete s w hw := by
    obtain ⟨v, hv, hfv⟩ := first.complete s w hw
    obtain ⟨z, hz, hnz⟩ := next.complete (first.statementMap s) v hv
    exact ⟨z, hz, v, hfv, hnz⟩
  sound s z hz := by
    obtain ⟨v, hv, hnz⟩ := next.sound (first.statementMap s) z hz
    obtain ⟨w, hw, hfv⟩ := first.sound s v hv
    exact ⟨w, hw, v, hfv, hnz⟩

/-- A useful constructor for lossless layout/statement changes. The equality
of meanings is an obligation, not inferred from a shared relation name. -/
def ofEquiv (statements : source.Statement ≃ target.Statement)
    (witnesses : source.Witness ≃ target.Witness)
    (law : ∀ s w, source.holds s w ↔ target.holds (statements s) (witnesses w)) :
    Encoding source target where
  statementMap := statements
  corresponds _ w z := witnesses w = z
  complete s w hw := ⟨witnesses w, (law s w).mp hw, rfl⟩
  sound s z hz := by
    refine ⟨witnesses.symm z, ?_, witnesses.apply_symm_apply z⟩
    apply (law s (witnesses.symm z)).mpr
    simpa using hz

theorem reduction (encoding : Encoding source target) (s : source.Statement) :
    ReductionContract (Valid source) (Valid target) s (encoding.statementMap s) False :=
  ⟨fun h => Or.inl ((encoding.valid_iff s).mpr h)⟩

/-- Transport the selected target protocol's reduction and terminal law.
Its bad event is preserved; no sampling or probability premise is invented. -/
theorem terminal_sound {R A : Type} (encoding : Encoding source target)
    (s : source.Statement) {residual : R → Prop} {r : R} {bad : Prop}
    (reduction : ReductionContract (Valid target) residual (encoding.statementMap s) r bad)
    (verify : R → PIR.Continuation.Terminal A) (terminal : TerminalContract residual verify)
    (a : A) (accepted : verify r = .accepted a) : Valid source s ∨ bad := by
  rcases PIR.Relation.terminal_sound reduction verify terminal a accepted with valid | exceptional
  · exact Or.inl ((encoding.valid_iff s).mpr valid)
  · exact Or.inr exceptional

end Encoding
end Zkc.Relation
