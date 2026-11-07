module

public import ZkcSecurity.Bindings.Transcript.QueryTreeSource.Composition.Typed

@[expose] public section

/-! Read the complete primitive and regrouped access logs on the same fixed
table. Every primitive access contributes one entry, including a repeat of
a root exposed by the prover. The table determines the reply at each entry. -/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.QueryTreeSource.Composition
open Zkc.Source Zkc.Construction QueryTree OracleComp OracleSpec

private theorem batchLog {Root Coord Raw Other A : Type} {R : Other → Type}
    (program : OracleComp (ofFn (@primitiveRange Root Coord Raw Other R)) A)
    (table : (key : Root ⊕ Other) → macroRange (Coord := Coord) (Raw := Raw) (R := R) key) :
    (tableQueryLog (translate program) table).map Sigma.fst =
      ((tableQueryLog program (flatten table)).map Sigma.fst).map rootOf := by
  induction program using OracleComp.inductionOn with
  | pure => rfl
  | query_bind key next ih =>
    cases key with
    | inl pair =>
      simp only [translate, simulateQ_bind, simulateQ_spec_query, ask, bind_assoc, pure_bind,
        tableQueryLog_query_bind, List.map_cons, rootOf, flatten]
      exact congrArg (_ :: ·) (ih _)
    | inr other =>
      simp only [translate, simulateQ_bind, simulateQ_spec_query, ask,
        tableQueryLog_query_bind, List.map_cons, rootOf, flatten]
      exact congrArg (_ :: ·) (ih _)

noncomputable section
variable {carriers : Structured.Carriers} {bound height : Nat} [NeZero bound]

/-- Recover the entire typed table, with each grouped scalar read at its
original coordinate and every other dependent reply at its original type. -/
def primitiveAnswers (segment : Segment) (table : (key : Root carriers bound ⊕ OtherKey carriers bound) →
    fullRange carriers bound height key) :=
  (fullRenaming segment).pullback (flatten table)

/-- Evaluation agrees on each fixed table, so successful and stopped runs
take the same adaptive branch even when the adversary queried it first. -/
theorem full_table (segment : Segment) {A : Type}
    (program : OracleComp (ofFn (Typed.ByLast (@Domain.Raw carriers))) A)
    (table : (key : Root carriers bound ⊕ OtherKey carriers bound) → fullRange carriers bound height key) :
    evalWithAnswerFn (QueryImpl.ofFn table) (fullTranslate segment program) =
      evalWithAnswerFn (QueryImpl.ofFn (primitiveAnswers segment table)) program :=
  (translate_table _ table).trans ((fullRenaming segment).evalWithAnswerFn_translate _ _)

local instance accessLogDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def macroKey {height : Nat} (segment : Segment) (history : Domain.History carriers) : Root carriers bound ⊕ OtherKey carriers bound :=
  if member : ScalarCell (bound := bound) history then .inl (locate (height := height) segment member.choose).1
  else .inr ⟨history, member⟩

private theorem routeKey (segment : Segment) (history : Domain.History carriers) :
    ((fullRenaming (bound := bound) (height := height) segment).cell history).map rootOf =
      some (macroKey (bound := bound) (height := height) segment history) := by
  classical
  by_cases member : ScalarCell (bound := bound) history <;> simp [fullRenaming, macroKey, rootOf, member]

/-- Equality of ordered lists preserves multiplicity across the prover and
verifier. An equality of sets, or of distributions alone, would lose this. -/
theorem full_accessLog (segment : Segment) {A : Type}
    (program : OracleComp (ofFn (Typed.ByLast (@Domain.Raw carriers))) A)
    (table : (key : Root carriers bound ⊕ OtherKey carriers bound) → fullRange carriers bound height key) :
    (tableQueryLog (fullTranslate segment program) table).map Sigma.fst =
      ((tableQueryLog program (primitiveAnswers segment table)).map Sigma.fst).map
        (macroKey (height := height) segment) := by
  rw [fullTranslate, batchLog, ZkcSecurity.Oracle.Renaming.tableQueryLog_translate, List.map_filterMap]
  change List.filterMap _ _ = _
  simp only [routeKey, List.filterMap_eq_map', primitiveAnswers]

omit [NeZero bound] in
theorem macroKey_other (segment : Segment) (other : OtherKey carriers bound) :
    macroKey (height := height) segment other.val = Sum.inr other := by
  simp [macroKey, other.property]

theorem macroKey_node (segment : Segment) (request : segment.query.request = some (.sampleIndex bound))
    (root : Domain.History carriers) (node : Node (Fin bound) height) :
    macroKey (height := height) (bound := bound) segment (oracleKey (encode segment (root, node))) = .inl (.inl root) := by
  let key : ScalarKey carriers bound := ⟨encode segment (root, node), (segment.queryAt_request _).trans request⟩
  have found := fullRenaming_scalar (height := height) segment key
  have routed := routeKey (height := height) (bound := bound) segment (oracleKey key.val)
  rw [found] at routed
  rw [show locate (height := height) segment key = (.inl root, .inl node) from locate_encode segment request (root, node)] at routed
  exact Option.some.inj routed.symm

/-- Non-scalar keys retain their exact replies, including keys an adversary
queried outside the source schedule. -/
theorem primitiveAnswers_other (segment : Segment)
    (table : (key : Root carriers bound ⊕ OtherKey carriers bound) → fullRange carriers bound height key)
    (other : OtherKey carriers bound) :
    primitiveAnswers segment table other.val = table (.inr other) := by
  rw [primitiveAnswers, ZkcSecurity.Oracle.Renaming.pullback_some _ _ (fullRenaming_other segment other)]
  simp [fullRenaming, other.property, flatten]

private theorem scalarReadAt (segment : Segment)
    (table : (key : Root carriers bound ⊕ OtherKey carriers bound) → fullRange carriers bound height key)
    (history : Domain.History carriers) (member : ScalarCell (bound := bound) history) :
    typedRenaming.read member.choose history (congrArg some member.choose_spec)
      (primitiveAnswers segment table history) =
        table (.inl (locate (height := height) segment member.choose).1)
          (locate (height := height) segment member.choose).2 := by
  let addressed : (fullRenaming (height := height) segment).cell history =
      some (.inl (locate segment member.choose)) := by simp [fullRenaming, member]
  rw [primitiveAnswers, ZkcSecurity.Oracle.Renaming.pullback_some _ _ addressed]
  simp [fullRenaming, member, flatten]

/-- A primitive scalar request uses the coordinate selected by its original
history, even if another query previously exposed the containing tree. -/
theorem primitiveAnswers_scalar (segment : Segment)
    (table : (key : Root carriers bound ⊕ OtherKey carriers bound) → fullRange carriers bound height key)
    (key : ScalarKey carriers bound) :
    typedRenaming.read key (oracleKey key.val) rfl (primitiveAnswers segment table (oracleKey key.val)) =
      table (.inl (locate (height := height) segment key).1) (locate (height := height) segment key).2 := by
  suffices general : ∀ (history : Domain.History carriers) (k : ScalarKey carriers bound)
      (found : oracleKey k.val = history), typedRenaming.read k history (congrArg some found)
        (primitiveAnswers segment table history) =
          table (.inl (locate (height := height) segment k).1) (locate (height := height) segment k).2 by
    exact general _ key rfl
  intro history k found
  have member : ScalarCell (bound := bound) history := ⟨k, found⟩
  have chosen : member.choose = k := Subtype.ext (oracleKey_injective (member.choose_spec.trans found.symm))
  subst k
  exact scalarReadAt segment table history member

/-- Recover one translated occurrence from its actual primitive log entry. -/
theorem loggedKey (segment : Segment) {A : Type}
    (program : OracleComp (ofFn (Typed.ByLast (@Domain.Raw carriers))) A)
    (table : (key : Root carriers bound ⊕ OtherKey carriers bound) → fullRange carriers bound height key)
    (entry : (history : Domain.History carriers) × Typed.ByLast Domain.Raw history)
    (member : entry ∈ tableQueryLog program (primitiveAnswers segment table)) :
    ∃ query ∈ tableQueryLog (fullTranslate segment program) table,
      query.1 = macroKey (height := height) segment entry.1 := by
  apply List.mem_map.mp
  rw [full_accessLog]
  exact List.mem_map.mpr ⟨entry.1, List.mem_map.mpr ⟨entry, member, rfl⟩, rfl⟩

end
end ZkcSecurity.FiatShamir.QueryTreeSource.Composition
