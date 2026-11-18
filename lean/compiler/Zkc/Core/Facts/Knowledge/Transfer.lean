module

public import Zkc.Core.Facts.Knowledge.Join

@[expose] public section

namespace Zkc.Core.BodyAnalysis
variable {Raw Val : Type} {Run : Raw → List Val → List Val → Prop} {R : Reading Val}
    {table : Table Raw} {ρ : Leaves Val}

/-- Recover the run of this entry from a reading of any of its occupied result slots. -/
theorem Reads.application {id : Ident} {v : Val} (read : Reads Run R.bool table ρ id v)
    {e : Entry Raw} {op : Raw} {ids : List Ident} {j : Nat} (slots : table.WF)
    (mem : e ∈ table) (form : e.form = .app op ids) (below : j < e.count)
    (slot : id = .val (e.lo+j)) :
    ∃ xs ys, ReadsAll Run R.bool table ρ ids xs ∧ Run op xs ys ∧ ys[j]? = some v := by
  cases read with
  | leaf found => cases slot
  | @app other written args i xs ys x known shape pos inputs ran result =>
    have same := Ident.val.inj slot
    obtain rfl := slots.apart _ _ known mem _ _ pos below same
    obtain rfl := Nat.add_left_cancel same
    rw [form] at shape
    cases shape
    exact ⟨xs, ys, inputs, ran, result⟩
  | select known shape cond hold selected =>
    have same := Ident.val.inj slot
    obtain rfl := slots.apart _ _ known mem 0 j (slots.select_pos known shape) below
      ((Nat.add_zero _).trans same)
    rw [form] at shape
    cases shape

namespace Knowledge

variable (functional : ∀ op xs ys zs, Run op xs ys → Run op xs zs → ys = zs) (slots : table.WF)

include functional slots in
private theorem addResultRanges_sound :
    ∀ (lo count : Nat) (ranges : List (Option Range)) {k : BufferedFacts}, Means Run R k table ρ →
      (∀ j r, j < count → ranges[j]? = some (some r) →
        ∃ v n, Reads Run R.bool table ρ (.val (lo+j)) v ∧ R.nat v = some n ∧ r.Has n) →
      Means Run R (addResultRanges lo count ranges k) table ρ
  | _, 0, _, _, h, _ => h
  | _, _+1, [], _, h, _ => h
  | lo, count+1, range :: rest, k, h, good => by
    apply addResultRanges_sound (lo+1) count rest
    · cases range with
      | none => exact h
      | some r =>
        obtain ⟨v, n, read, val, fit⟩ := good 0 r (Nat.zero_lt_succ _) rfl
        apply addRange_sound functional slots h read
        intro r' same
        cases same
        exact ⟨n, val, fit⟩
    · intro j r below at_
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using good (j+1) r (Nat.succ_lt_succ below) at_

include slots in
theorem transferRanges_sound {ops : KnowledgeOperations Raw} (laws : ops.Lawful R Run) {asks : Asks} {k : BufferedFacts}
    {e : Entry Raw} (external : asks.Sound Run R table ρ) (h : Means Run R k table ρ)
    (mem : e ∈ table) (read : ∀ j, j < e.count → ∃ v, Reads Run R.bool table ρ (.val (e.lo+j)) v) :
    Means Run R (transferRanges ops asks k e) table ρ := by
  cases form : e.form with
  | select c a b => simpa [transferRanges, form] using h
  | app op ids =>
    simp only [transferRanges, form]
    have ranges : ops.ranges op (if ops.needsOperandRanges op then ids.map (rangeFor asks k) else []) =
        ops.ranges op (ids.map (rangeFor asks k)) := by
      cases used : ops.needsOperandRanges op with
      | false => exact ops.ranges_constant op used _
      | true => rfl
    rw [ranges]
    apply addResultRanges_sound laws.functional slots _ _ _ h
    intro j r below reported
    obtain ⟨v, reading⟩ := read j below
    obtain ⟨xs, ys, inputs, ran, pos⟩ := reading.application slots mem form below rfl
    obtain ⟨x, n, at_, val, fits⟩ := laws.ranges op xs ys (ids.map (rangeFor asks k)) ran (by
      intro i r found
      simp only [List.getElem?_map, Option.map_eq_some_iff] at found
      obtain ⟨id, idAt, known⟩ := found
      obtain ⟨arg, argAt, argRead⟩ := inputs.get idAt
      obtain ⟨n, val, fits⟩ := rangeFor_sound laws.functional slots external h argRead known
      exact ⟨arg, n, argAt, val, fits⟩) j r reported
    rw [pos] at at_
    cases at_
    exact ⟨v, n, reading, val, fits⟩

#print axioms transferRanges_sound
end Knowledge
end Zkc.Core.BodyAnalysis
