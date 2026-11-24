module

public import Zkc.Core.Facts.Knowledge.Learning

@[expose] public section

namespace Zkc.Core.BodyAnalysis.Knowledge

variable {Raw Val : Type} {Run : Raw → List Val → List Val → Prop} {R : Reading Val}
    {table : Table Raw} {ρ : Leaves Val} {ops : KnowledgeOperations Raw}
    (laws : ops.Lawful R Run) (slots : table.WF) {k : BufferedFacts} (h : Means Run R k table ρ)

theorem identOfKey_key (n : Nat) : (identOfKey n).key = n := by
  unfold identOfKey
  split <;> simp [Ident.key] <;> omega

include laws slots h in
private theorem limitFor_sound {accept : Ident → Bool} {base index limit : Ident} {va vi : Val} {x t : Nat}
    (baseRead : Reads Run R.bool table ρ base va) (indexRead : Reads Run R.bool table ρ index vi)
    (baseNum : R.nat va = some x) (indexNum : R.nat vi = some t)
    (found : limitFor ops table k base index accept = some limit) :
    accept limit ∧ ∃ v m, Reads Run R.bool table ρ limit v ∧ R.nat v = some m ∧ x+t < m := by
  obtain ⟨fact, listed, yields⟩ := List.exists_of_findSome?_eq_some found
  split at yields
  · next valid =>
    simp only [Bool.and_eq_true, beq_iff_eq] at valid
    obtain ⟨⟨first, strict⟩, byLoop⟩ := valid
    split at yields
    · next end_ start shape =>
      split at yields
      · next choice =>
        cases yields
        obtain ⟨same, wanted⟩ := Bool.and_eq_true_iff.mp choice
        obtain rfl := beq_iff_eq.mp same
        obtain ⟨assignment, grounded, facts⟩ := h
        obtain ⟨i,d,⟨iv, hi, ni⟩,⟨dv, hd, nd⟩, less⟩ := facts.orders fact (FactCheck.FactBuckets.mem_of_find _ _ _ listed)
        rw [first] at hi
        obtain rfl := Reads.functionalOn laws.functional slots indexRead (grounded index _ hi)
        rw [indexNum] at ni
        cases ni
        have diffRead := grounded (identOfKey fact.second) dv (by simpa [identOfKey_key] using hd)
        obtain ⟨_, reads, _, _, m, n, rfl, nv, ns, _, res⟩ := resultForm_reads laws slots shape diffRead
        cases reads with | cons cap tail => cases tail with | cons start _ =>
          obtain rfl := Reads.functionalOn laws.functional slots baseRead start
          rw [baseNum] at ns
          rw [nd] at res
          rw [strict] at less
          exact ⟨wanted, _, m, cap, nv, by simp_all; omega⟩
      · cases yields
    · cases yields
  · cases yields

include laws slots h in
private theorem sumLimit_sound {accept : Ident → Bool} {base index limit : Ident} {va vi : Val} {x t : Nat}
    (first : Reads Run R.bool table ρ base va) (second : Reads Run R.bool table ρ index vi)
    (na : R.nat va = some x) (nt : R.nat vi = some t)
    (found : sumLimit ops table k base index accept = some limit) :
    accept limit ∧ ∃ cap m, Reads Run R.bool table ρ limit cap ∧ R.nat cap = some m ∧ x+t < m := by
  unfold sumLimit at found
  cases one : limitFor ops table k base index accept with
  | some d =>
    obtain rfl : d = limit := by simpa [one] using found
    obtain ⟨wanted,cap,m,rc,nc,lt⟩ := limitFor_sound laws slots h first second na nt one
    exact ⟨wanted, cap, m, rc, nc, lt⟩
  | none =>
    simp only [one, Option.orElse_none] at found
    obtain ⟨wanted,cap,m,rc,nc,lt⟩ := limitFor_sound laws slots h second first nt na found
    exact ⟨wanted, cap, m, rc, nc, by omega⟩

include laws slots h in
theorem offsetLimit_sound {accept : Ident → Bool} {result limit : Ident} {v : Val}
    (read : Reads Run R.bool table ρ result v) (found : offsetLimit ops table k result accept = some limit) :
    accept limit ∧ ∃ n cap m, R.nat v = some n ∧ Reads Run R.bool table ρ limit cap ∧
      R.nat cap = some m ∧ n < m := by
  unfold offsetLimit at found
  split at found
  · next base index shape =>
    obtain ⟨_, reads, _, _, x, t, rfl, na, nt, res⟩ := resultForm_reads laws slots shape read
    cases reads with | cons first tail => cases tail with | cons second _ =>
      obtain ⟨wanted, cap, m, rc, nc, lt⟩ := sumLimit_sound laws slots h first second na nt found
      exact ⟨wanted, x+t, cap, m, res, rc, nc, lt⟩
  · cases found

include laws slots h in
theorem transfer_sound {asks : Asks} {e : Entry Raw} (external : asks.Sound Run R table ρ)
    (mem : e ∈ table) (reads : ∀ j, j < e.count → ∃ v, Reads Run R.bool table ρ (.val (e.lo+j)) v) :
    Means Run R (transfer ops asks table k e) table ρ := by
  have learned := transferRanges_sound slots laws external h mem reads
  unfold transfer
  split
  · exact learned
  · next nonempty =>
    obtain ⟨v, read⟩ := reads 0 (by omega)
    simp only [Nat.add_zero] at read
    split
    · next op a b shape =>
      split
      · next sum =>
        apply addRange_sound laws.functional slots learned read
        intro r found
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at found
        obtain ⟨limit, picked, range, bound, eq⟩ := found
        cases eq
        obtain ⟨xs, ys, inputs, ran, at_⟩ := read.application slots mem shape (j := 0) (by omega) rfl
        obtain ⟨y, head, x, z, n, t, rfl, na, nt, res⟩ :=
          laws.form _ _ _ _ (beq_iff_eq.mp sum) ran
        rw [List.head?_eq_getElem?, at_] at head
        cases head
        cases inputs with | cons first tail => cases tail with | cons second _ =>
          obtain ⟨_, cap, m, rc, nc, lt⟩ := sumLimit_sound laws slots h first second na nt picked
          obtain ⟨m', val, fits⟩ := rangeFor_sound laws.functional slots external h rc bound
          rw [nc] at val
          cases val
          exact ⟨_, res, fits.below lt⟩
      · exact learned
    · exact learned

end Zkc.Core.BodyAnalysis.Knowledge
