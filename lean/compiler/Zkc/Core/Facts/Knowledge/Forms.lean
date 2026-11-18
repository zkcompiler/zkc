module

public import Zkc.Core.Facts.Knowledge.Transfer

@[expose] public section

namespace Zkc.Core.BodyAnalysis

private theorem entryIn_spec {Raw : Type} {n : Nat} {e : Entry Raw} : ∀ es : List (Entry Raw),
    entryIn n es = some e → e ∈ es ∧ e.lo ≤ n ∧ n < e.lo + e.count
  | [], found => nomatch found
  | first :: rest, found => by
    simp only [entryIn] at found
    split at found
    · cases found
      exact ⟨List.mem_cons_self, by assumption⟩
    · obtain ⟨mem, inside⟩ := entryIn_spec rest found
      exact ⟨List.mem_cons_of_mem _ mem, inside⟩

theorem Table.formOf_spec {Raw : Type} {table : Table Raw} {id : Ident} {f : Form Raw} {j : Nat}
    (found : table.formOf id = some (f,j)) :
    ∃ e ∈ table, e.form = f ∧ j < e.count ∧ id = .val (e.lo+j) := by
  cases id with
  | leaf => cases found
  | val n =>
    obtain ⟨e, known, eq⟩ := Option.map_eq_some_iff.mp found
    have ⟨mem, lower, upper⟩ : e ∈ table ∧ e.lo ≤ n ∧ n < e.lo + e.count :=
      table.search_spec (probe := entryIn n) (P := fun e => e ∈ table ∧ e.lo ≤ n ∧ n < e.lo + e.count)
        (fun b x m => b.values x (BitTree.mem_of_find _ _ _ _ m))
        (fun es sub hit => let h := entryIn_spec es hit; ⟨sub _ h.1, h.2⟩) known
    cases eq
    exact ⟨e, mem, rfl, by omega,
      congrArg Ident.val (by omega)⟩

namespace Knowledge

variable {Raw Val : Type} {Run : Raw → List Val → List Val → Prop} {R : Reading Val}
    {table : Table Raw} {ρ : Leaves Val}

theorem addedTerm_spec {ops : KnowledgeOperations Raw} {carried ret term : Ident} (h : addedTerm ops table carried ret = some term) :
    ∃ op, ops.form op = some .sum ∧
      (table.formOf ret = some (.app op [carried,term], 0) ∨ table.formOf ret = some (.app op [term,carried], 0)) := by
  unfold addedTerm at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨form, port⟩, found, ok⟩ := h
  split at ok
  · next op a b eq =>
      rw [eq] at found
      split at ok
      · cases ok
      · next named =>
        have sum : ops.form op = some .sum := by simpa using named
        split at ok
        · cases ok
          exact ⟨op, sum, .inl (by simp [*])⟩
        · split at ok
          · cases ok
            exact ⟨op, sum, .inr (by simp [*])⟩
          · cases ok
  · cases ok

/-- A sum-shaped returned result reads the sum of its indicated operands. -/
theorem reads_sum {ops : KnowledgeOperations Raw} (laws : ops.Lawful R Run) (slots : table.WF)
    {op : Raw} {left right ret : Ident} {v : Val} (sum : ops.form op = some .sum)
    (shape : table.formOf ret = some (.app op [left,right], 0)) (read : Reads Run R.bool table ρ ret v) :
    ∃ a b n m, Reads Run R.bool table ρ left a ∧ Reads Run R.bool table ρ right b ∧
      R.nat a = some n ∧ R.nat b = some m ∧ R.nat v = some (n+m) := by
  obtain ⟨entry, mem, form, below, same⟩ := Table.formOf_spec shape
  obtain ⟨xs, ys, inputs, ran, at_⟩ := read.application slots mem form below same
  obtain ⟨x, head, a, b, n, m, rfl, na, nb, nv⟩ := laws.form op xs ys .sum sum ran
  rw [List.head?_eq_getElem?] at head
  rw [at_] at head
  cases head
  cases inputs with
  | cons first more =>
    cases more with
    | cons second _ => exact ⟨_, _, _, _, first, second, na, nb, nv⟩

end Knowledge
end Zkc.Core.BodyAnalysis
