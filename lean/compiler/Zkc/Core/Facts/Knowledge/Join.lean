module

public import Zkc.Core.Facts.Knowledge.Meaning

@[expose] public section

namespace Zkc.Core.BodyAnalysis.Knowledge


variable {Raw Val : Type} {Run : Raw → List Val → List Val → Prop} {R : Reading Val}
    {table : Table Raw} {ρ : Leaves Val}
    (functional : ∀ op xs ys zs, Run op xs ys → Run op xs zs → ys = zs) (slots : table.WF)

include functional slots in
theorem cachedRange {k : BufferedFacts} {id : Ident} {v : Val} {r : Range} (h : Means Run R k table ρ)
    (read : Reads Run R.bool table ρ id v) (known : k.rangeOf id.key = some r) :
    ∃ n, R.nat v = some n ∧ r.Has n := by
  obtain ⟨a, grounded, facts⟩ := h
  obtain ⟨n, ⟨x, found, val⟩, fit⟩ := facts.rangeOf (by simpa only [BufferedFacts.view_rangeOf] using known)
  obtain rfl := Reads.functionalOn functional slots read (grounded _ _ found)
  exact ⟨n, val, fit⟩

private theorem meetReads {value : Option Nat} {a b : Option Range} {r : Range}
    (ha : ∀ {q}, a = some q → ∃ n, value = some n ∧ q.Has n)
    (hb : ∀ {q}, b = some q → ∃ n, value = some n ∧ q.Has n)
    (found : Range.meet a b = some r) : ∃ n, value = some n ∧ r.Has n := by
  cases a with
  | none => exact hb found
  | some ra =>
    obtain ⟨n,read,fits⟩ := ha rfl
    cases b with
    | none => cases found; exact ⟨n,read,fits⟩
    | some rb =>
      obtain ⟨m,read',fits'⟩ := hb rfl
      obtain rfl := Option.some.inj (read.symm.trans read')
      cases found
      exact ⟨n,read,fits.inter fits'⟩

include functional slots in
theorem directRange_sound {asks : Asks} {k : BufferedFacts} {id : Ident} {v : Val} {r : Range}
    (external : asks.Sound Run R table ρ) (h : Means Run R k table ρ)
    (read : Reads Run R.bool table ρ id v) (known : directRange asks k id = some r) :
    ∃ n, R.nat v = some n ∧ r.Has n := by
  let peer : Option Range := match asks.exact id with
    | some n => some (Range.point n)
    | none => (asks.upper id).map fun hi => ⟨0, some hi⟩
  have peerSound : ∀ {r}, peer = some r → ∃ n, R.nat v = some n ∧ r.Has n := by
    intro r report
    cases eq : asks.exact id with
    | some n =>
      obtain ⟨x, other, val⟩ := external.exact _ _ eq
      obtain rfl := Reads.functionalOn functional slots read other
      obtain rfl : Range.point n = r := by simpa [peer, eq] using report
      exact ⟨n, val, Range.has_point.mpr rfl⟩
    | none =>
      cases upper : asks.upper id with
      | none => simp [peer, eq, upper] at report
      | some hi =>
        obtain ⟨x, n, other, val, le⟩ := external.upper _ _ upper
        obtain rfl := Reads.functionalOn functional slots read other
        obtain rfl : (⟨0, some hi⟩ : Range) = r := by simpa [peer, eq, upper] using report
        exact ⟨n, val, Nat.zero_le _, fun bound same => Option.some.inj same ▸ le⟩
  exact meetReads (cachedRange functional slots h read) peerSound known

include functional slots in
theorem rangeFor_sound {asks : Asks} {k : BufferedFacts} {id : Ident} {v : Val} {r : Range}
    (external : asks.Sound Run R table ρ) (h : Means Run R k table ρ)
    (read : Reads Run R.bool table ρ id v) (known : rangeFor asks k id = some r) :
    ∃ n, R.nat v = some n ∧ r.Has n := by
  apply meetReads (directRange_sound functional slots external h read) _ known
  intro q found
  obtain ⟨a,alias,reported⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨x,y,rx,ry,same⟩ := external.numberSource _ _ alias
  cases Reads.functionalOn functional slots read rx
  obtain ⟨n,num,fits⟩ := directRange_sound functional slots external h ry reported
  exact ⟨n,same.trans num,fits⟩


/-- For any selected exit, a successful hull contains the range that exit supplied. -/
theorem hullAt_has {α : Type} (get : α → Option Range) {chosen : α} :
    ∀ {exits : List α} {bound}, chosen ∈ exits → hullAt get exits = some bound →
      ∃ r, get chosen = some r ∧ ∀ n, r.Has n → bound.Has n
  | [], _, member, _ => nomatch member
  | [e], _, member, found => by
    obtain rfl := List.mem_singleton.mp member
    exact ⟨_, found, fun _ h => h⟩
  | e :: next :: rest, _, member, found => by
    simp only [hullAt, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at found
    obtain ⟨left, hl, right, hr, eq⟩ := found
    cases eq
    rcases List.mem_cons.mp member with rfl | tail
    · exact ⟨left, hl, fun _ h => h.hull_left⟩
    · obtain ⟨r, found, incl⟩ := hullAt_has get tail hr
      exact ⟨r, found, fun n h => (incl n h).hull_right⟩

include functional slots in
theorem addRange_sound {k : BufferedFacts} {id : Ident} {v : Val} {r : Option Range}
    (h : Means Run R k table ρ) (read : Reads Run R.bool table ρ id v)
    (good : ∀ r', r = some r' → ∃ n, R.nat v = some n ∧ r'.Has n) :
    Means Run R (k.addRange? id.key r) table ρ := by
  obtain ⟨a, grounded, facts, found⟩ := withRead functional slots h read
  refine ⟨a, grounded, ?_⟩
  rw [BufferedFacts.view_addRange?]
  apply facts.addRange?
  intro r' e
  obtain ⟨n, val, fit⟩ := good r' e
  exact ⟨n, ⟨v, found, val⟩, fit⟩

include functional slots in
theorem learnRanges_sound {rangeAt : Nat → Option Range} {ids : List Ident} {values : List Val}
    (read : ReadsAll Run R.bool table ρ ids values) :
    ∀ i k, Means Run R k table ρ → (∀ j v r, values[j]? = some v → rangeAt (i+j) = some r →
      ∃ n, R.nat v = some n ∧ r.Has n) → Means Run R (learnRanges rangeAt ids i k) table ρ := by
  induction ids generalizing values with
  | nil => exact fun _ _ h _ => h
  | cons id rest ih =>
    cases read with
    | cons one more =>
      intro i k h good
      apply ih more (i+1) _
      · exact addRange_sound functional slots h one (fun r known => good 0 _ r rfl known)
      · intro j v r found known
        exact good (j+1) v r found (by simpa [Nat.add_assoc, Nat.add_comm 1 j] using known)

include functional slots in
theorem after_sound {before exit : BufferedFacts} {exits : List RegionExit} {results returned : List Ident}
    {asks : Asks} {values : List Val} (prior : Means Run R before table ρ)
    (member : (asks, exit, returned) ∈ exits) (last : Means Run R exit table ρ)
    (peer : asks.Sound Run R table ρ) (out : ReadsAll Run R.bool table ρ returned values)
    (made : ReadsAll Run R.bool table ρ results values) : Means Run R (after before exits results) table ρ := by
  have obtainRange {i : Nat} {v : Val} {r : Range} (atValue : values[i]? = some v)
      (found : hullAt (exitRange i) exits = some r) : ∃ n, R.nat v = some n ∧ r.Has n := by
    obtain ⟨selected, known, contains⟩ := hullAt_has _ member found
    change (returned[i]?.bind (rangeFor asks exit)) = some selected at known
    obtain ⟨id, idAt, range⟩ := Option.bind_eq_some_iff.mp known
    obtain ⟨x, same, read⟩ := out.get idAt
    rw [atValue] at same
    cases same
    obtain ⟨n, val, fits⟩ := rangeFor_sound functional slots peer last read range
    exact ⟨n, val, contains n fits⟩
  have nonempty := List.ne_nil_of_mem member
  simp only [after, List.isEmpty_iff, nonempty, ↓reduceIte]
  exact learnRanges_sound functional slots made 0 _ prior (fun j v r at_ found =>
    obtainRange at_ (by simpa using found))

end Zkc.Core.BodyAnalysis.Knowledge
