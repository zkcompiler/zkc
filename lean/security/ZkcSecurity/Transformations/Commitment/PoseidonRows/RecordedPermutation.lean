module

public import ZkcSecurity.Transformations.Commitment.PoseidonRows.ExposureTargets

@[expose] public section

/-! A monitor over the existing shared lazy permutation handler. Primitive replies and
allocation markers are appended by the handler itself. Allocation refusal is explicit; it
neither consumes a primitive call nor silently registers an unprotected checkpoint. -/

set_option autoImplicit false

namespace ZkcSecurity.Commitment.PoseidonRows.Monitored

open OracleComp OracleSpec
open ZkcSecurity.Probability

variable {Key F : Type} {rate b : ℕ} [Zero F] [DecidableEq F]

local notation "D" => Digest F rate

/-- Primitive calls and actual allocation attempts have different result types. -/
inductive Command (Key F : Type) (rate : ℕ) where
  | call (query : PermQuery (Digest F rate))
  | allocate (key : Key) (roots : List (Digest F rate))

abbrev Reply : Command Key F rate → Type
  | .call _ => State F rate
  | .allocate _ _ => Bool

abbrev Oracle (Key F : Type) (rate : ℕ) :=
  OracleSpec.ofFn (Reply (Key := Key) (F := F) (rate := rate))

structure Monitor (Key F : Type) (rate b : ℕ) [DecidableEq F] where
  permutation : PermState (Digest F rate)
  history : History Key F rate
  roots : Roots (Digest F rate) b

def empty : Monitor Key F rate b :=
  ⟨PermutationExposure.State.empty, [], ⟨[], by simp⟩⟩

/-- Every primitive call is logged, including cache hits, inverse calls and failed-operation
prefixes. No protocol acceptance filter is applied. -/
def record (s : Monitor Key F rate b) (q : PermQuery D)
    (result : State F rate × PermState D) : Monitor Key F rate b :=
  { s with permutation := result.2, history := s.history ++ [primitive (exposure q result.1)] }

/-- An over-budget attempt returns false. Successful attempts retain all root occurrences
forever, even duplicates and registrations under an already used key. -/
def register (s : Monitor Key F rate b) (key : Key) (roots : List D) :
    Bool × Monitor Key F rate b :=
  if bounded : s.roots.entries.length + roots.length ≤ b then
    (true, { s with
      history := s.history ++ [allocation key roots]
      roots := ⟨s.roots.entries ++ roots, by simpa using bounded⟩ })
  else (false, s)

noncomputable def handler [Fintype F] :
    QueryImpl (Oracle Key F rate) (StateT (Monitor Key F rate b) ProbComp) :=
  fun command ↦ StateT.mk fun s ↦ match command with
  | .call q => (fun result ↦ (result.1, record s q result)) <$>
      PermutationExposure.step (targets s.roots) q s.permutation
  | .allocate key roots => pure (register s key roots)

/-- Flatten only actual accepted allocation markers. -/
def registered (history : History Key F rate) : List D :=
  history.flatMap fun entry ↦ match entry.2 with | .inl _ => [] | .inr roots => roots

omit [Zero F] [DecidableEq F] in
@[simp] theorem registered_append (a c : History Key F rate) :
    registered (a ++ c) = registered a ++ registered c := by simp [registered]

omit [Zero F] [DecidableEq F] in
@[simp] theorem calls_primitive (h : History Key F rate) (e : Exposure F rate) :
    calls (h ++ [primitive e]) = calls h ++ [e] := by simp [calls, primitive]

omit [Zero F] [DecidableEq F] in
@[simp] theorem calls_allocation (h : History Key F rate) (key : Key) (roots : List D) :
    calls (h ++ [allocation key roots]) = calls h := by simp [calls, allocation]

/-- A list split at an occurrence either precedes the last entry or is that last entry. -/
theorem split_snoc {A : Type} (h p : List A) (a z : A) (t : List A)
    (equal : h ++ [z] = p ++ a :: t) :
    (∃ u, h = p ++ a :: u ∧ t = u ++ [z]) ∨ (h = p ∧ a = z ∧ t = []) := by
  induction p generalizing h with
  | nil =>
    cases h with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, List.nil_eq] at equal
      exact Or.inr ⟨rfl, equal.1.symm, equal.2⟩
    | cons x xs =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at equal
      exact Or.inl ⟨xs, by simp [equal.1], equal.2.symm⟩
  | cons x xs ih =>
    cases h with
    | nil => simp at equal
    | cons y ys =>
      simp only [List.cons_append, List.cons.injEq] at equal
      rcases ih ys equal.2 with ⟨u, hu, ht⟩ | ⟨hp, ha, ht⟩
      · exact Or.inl ⟨u, by simp [equal.1, hu], ht⟩
      · exact Or.inr ⟨by simp [equal.1, hp], ha, ht⟩

/-- Generic history extension, including failed decodings and allocations before first use.
The extra premise consists only of misses on roots in earlier actual markers. -/
theorem goodHistory_snoc (h : History Key F rate)
    (z : (_key : Option Key) × HistoryData F rate) (born : List (Exposure F rate))
    (oldGood : GoodHistory h)
    (extension : normalize (calls (h ++ [z])) = normalize (calls h) ++ born)
    (newGood : Good (normalize (calls (h ++ [z]))))
    (protectedRoots : ∀ p key roots t, h = p ++ allocation key roots :: t →
      ∀ e ∈ born, e.forward = true → ∀ root ∈ roots, e.output.1 ≠ root) :
    GoodHistory (h ++ [z]) := by
  refine ⟨newGood, ?_⟩
  intro p key roots t marker fresh freshEq e em ef root rm
  rcases split_snoc h p (allocation key roots) z t marker with ⟨u, hu, _⟩ | ⟨hp, hz, _⟩
  · have isPrefix : normalize (calls p) <+: normalize (calls h) := by
      rw [hu, calls_append]
      exact normalize_prefix _ _
    obtain ⟨middle, hm⟩ := isPrefix
    have combined : fresh = middle ++ born := by
      have : normalize (calls p) ++ fresh = normalize (calls p) ++ (middle ++ born) := by
        rw [← freshEq, extension, ← hm, List.append_assoc]
      exact List.append_cancel_left this
    rw [combined] at em
    rcases List.mem_append.mp em with earlier | new
    · exact oldGood.2 p key roots u hu middle hm.symm e earlier ef root rm
    · exact protectedRoots p key roots u hu e new ef root rm
  · subst h
    rw [← hz] at freshEq
    have : fresh = [] := by
      have equal : normalize (calls p) ++ [] = normalize (calls p) ++ fresh := by
        simpa using freshEq
      exact (List.append_cancel_left equal).symm
    simp [this] at em

/-- Raw/normalized pair association and the exact aggregate registration list. -/
def Invariant (s : Monitor Key F rate b) : Prop :=
  Associated s.permutation (normalize (calls s.history)) ∧
    s.roots.entries = registered s.history ∧
    (s.permutation.bad = false → GoodHistory s.history)

theorem empty_invariant : Invariant (empty : Monitor Key F rate b) := by
  simp [Invariant, empty, Associated, PermutationExposure.State.empty,
    registered, GoodHistory, Good, calls, normalize]


omit [Zero F] [DecidableEq F] in
theorem root_registered {h p t : History Key F rate} {key : Key} {roots : List D}
    (marker : h = p ++ allocation key roots :: t) {root : D} (member : root ∈ roots) :
    root ∈ registered h := by
  rw [marker, registered_append]
  exact List.mem_append_right _ (by simp [registered, allocation, member])

omit [Zero F] in
/-- The exact set insertion and its fresh input in either orientation. -/
theorem fresh_input [Fintype F] (s : PermState D) (q : PermQuery D)
    (fresh : ¬ s.cached q) (answer : State F rate)
    (available : answer ∈ s.available q.direction) (hit : Bool) :
    (exposure q answer).input ∉ s.used ∧
      (s.insert q answer hit).used = Insert.insert (exposure q answer).input s.used ∧
      (s.insert q answer hit).completion (exposure q answer).input =
        (exposure q answer).output := by
  cases q with
  | mk direction point =>
    cases direction with
    | forward => simpa [exposure, PermutationExposure.State.cached,
        PermutationExposure.State.insert] using fresh
    | inverse =>
      have unused := (Finset.mem_sdiff.mp available).2
      simpa [exposure, PermutationExposure.State.excluded,
        PermutationExposure.State.insert] using unused

omit [Zero F] in
/-- Association is preserved by a supported fresh insertion, independently of badness. -/
theorem associate_fresh [Fintype F] (s : PermState D)
    (q : PermQuery D) (fresh : ¬ s.cached q) (answer : State F rate)
    (available : answer ∈ s.available q.direction) (hit : Bool)
    (log : List (Exposure F rate)) (assoc : Associated s log) :
    Associated (s.insert q answer hit) (log ++ [exposure q answer]) := by
  have shape := fresh_input s q fresh answer available hit
  refine ⟨?_, ?_⟩
  · intro e em
    rcases List.mem_append.mp em with old | new
    · obtain ⟨known, image⟩ := assoc.1 e old
      exact ⟨by rw [shape.2.1]; exact Finset.mem_insert_of_mem known,
        (PermutationExposure.fresh_preserves s q fresh answer available hit e.input known).trans
          image⟩
    · have equal : e = exposure q answer := by simpa using new
      subst e
      exact ⟨by rw [shape.2.1]; exact Finset.mem_insert_self _ _, shape.2.2⟩
  · intro x known
    rw [shape.2.1, Finset.mem_insert] at known
    rcases known with rfl | known
    · exact ⟨exposure q answer, by simp, rfl⟩
    · obtain ⟨e, em, eq⟩ := assoc.2 x known
      exact ⟨e, List.mem_append_left _ em, eq⟩

/-- One actual primitive handler step constructs its record and preserves the invariant.
A forward cache hit on an inverse birth leaves the first normalized direction unchanged. -/
theorem record_invariant [Fintype F] (s : Monitor Key F rate b) (inv : Invariant s)
    (q : PermQuery D) (result : State F rate × PermState D)
    (member : result ∈ support (PermutationExposure.step (targets s.roots) q s.permutation)) :
    Invariant (record s q result) := by
  classical
  by_cases cached : s.permutation.cached q
  · rw [PermutationExposure.step_cached _ _ _ cached, support_pure,
      Set.mem_singleton_iff] at member
    subst result
    have known : (exposure q (s.permutation.answer q)).input ∈ s.permutation.used := by
      cases direction : q.direction <;>
        simpa [exposure, PermutationExposure.State.answer,
          PermutationExposure.State.cached, direction] using cached
    obtain ⟨old, om, input⟩ := inv.1.2 _ known
    have output := (inv.1.1 old om).2
    have same : SamePair old (exposure q (s.permutation.answer q)) := by
      refine ⟨input, ?_⟩
      rw [← output, input]
      cases direction : q.direction <;>
        simp [exposure, PermutationExposure.State.answer, direction]
    have norm : normalize (calls
        (record s q (s.permutation.answer q, s.permutation.tick)).history) =
        normalize (calls s.history) := by
      simp only [record, calls_primitive]
      exact normalize_repeat om same
    have normRaw : normalize (calls (s.history ++
        [primitive (exposure q (s.permutation.answer q))])) = normalize (calls s.history) := norm
    refine ⟨?_, ?_, ?_⟩
    · change Associated s.permutation.tick _
      rw [norm]
      exact inv.1
    · simpa [record, registered, primitive] using inv.2.1
    · intro quiet
      have oldGood := inv.2.2 quiet
      apply goodHistory_snoc s.history (primitive (exposure q (s.permutation.answer q))) []
        oldGood (by simpa using normRaw) (by rw [normRaw]; exact oldGood.1)
      simp
  · rw [PermutationExposure.step_fresh _ _ _ cached, support_map] at member
    obtain ⟨answer, am, rfl⟩ := member
    have available := PermutationExposure.draw_mem _ _ answer am
    let e := exposure q answer
    let hit := decide (PermutationExposure.FiberHit (targets s.roots s.permutation q).1
      (targets s.roots s.permutation q).2 answer)
    have shape := fresh_input s.permutation q cached answer available hit
    have absent : (normalize (calls s.history)).any (fun old ↦ decide (SamePair old e)) =
        false := by
      apply List.any_eq_false.mpr
      intro old om
      have unused : ¬ SamePair old e := fun same ↦
        shape.1 (same.1 ▸ (inv.1.1 old om).1)
      simpa using unused
    have norm : normalize (calls (s.history ++ [primitive e])) =
        normalize (calls s.history) ++ [e] := by
      rw [calls_primitive, normalize_snoc]
      simp [PoseidonRows.insert, absent]
    refine ⟨?_, ?_, ?_⟩
    · change Associated (s.permutation.insert q answer hit)
        (normalize (calls (s.history ++ [primitive e])))
      rw [norm]
      exact associate_fresh s.permutation q cached answer available hit _ inv.1
    · simpa [record, registered, primitive] using inv.2.1
    · intro quiet
      change (s.permutation.insert q answer hit).bad = false at quiet
      rw [PermutationExposure.insert_bad, Bool.or_eq_false_iff] at quiet
      have oldGood := inv.2.2 quiet.1
      have miss : ¬ PermutationExposure.FiberHit (targets s.roots s.permutation q).1
          (targets s.roots s.permutation q).2 answer := by simpa [hit] using quiet.2
      have flags := miss_good s.roots s.permutation q answer _ inv.1 miss
      have newGood : Good (normalize (calls (s.history ++ [primitive e]))) := by
        rw [norm]
        refine ⟨List.pairwise_append.mpr ⟨oldGood.1.1, by simp, ?_⟩, ?_⟩
        · intro old om new nm
          have equal : new = e := by simpa using nm
          subst new
          exact flags.2.1 old om
        · intro new nm
          rcases List.mem_append.mp nm with old | last
          · exact oldGood.1.2 new old
          · have equal : new = e := by simpa using last
            subst new
            exact flags.1
      apply goodHistory_snoc s.history (primitive e) [e] oldGood norm newGood
      intro p key roots t marker new nm nf root rm
      have equal : new = e := by simpa using nm
      subst new
      apply flags.2.2 root _ nf
      rw [inv.2.1]
      exact root_registered marker rm

/-- Accepted allocations retain the marker and every root; refused attempts leave the state
unchanged and return false, so no successful marker is discarded. -/
theorem register_invariant (s : Monitor Key F rate b) (inv : Invariant s)
    (key : Key) (roots : List D) : Invariant (register s key roots).2 := by
  unfold register
  split
  · refine ⟨?_, ?_, ?_⟩
    · simpa using inv.1
    · simpa [registered, allocation] using congrArg (fun xs ↦ xs ++ roots) inv.2.1
    · intro quiet
      have oldGood := inv.2.2 quiet
      apply goodHistory_snoc s.history (allocation key roots) [] oldGood
        (by simp) (by simpa using oldGood.1)
      simp
  · exact inv

/-- Support induction uses VCVio's existing simulation invariant theorem. -/
theorem run_invariant [Fintype F] {α : Type} (program : OracleComp (Oracle Key F rate) α)
    (result : α × Monitor Key F rate b)
    (member : result ∈ support ((simulateQ handler program).run empty)) :
    Invariant result.2 := by
  apply simulateQ_run_preservesInv handler Invariant (fun command s inv result member ↦ ?_)
    program empty empty_invariant result member
  cases command with
  | call q =>
    change result ∈ support ((fun r ↦ (r.1, record s q r)) <$>
      PermutationExposure.step (targets s.roots) q s.permutation) at member
    rw [support_map] at member
    obtain ⟨r, rm, rfl⟩ := member
    exact record_invariant s inv q r rm
  | allocate key roots =>
    change result ∈ support (pure (register s key roots)) at member
    simp only [support_pure] at member
    change result = register s key roots at member
    subst result
    exact register_invariant s inv key roots

/-- The sampler's cumulative flag absence implies the existing, unmodified GoodHistory. -/
theorem run_goodHistory [Fintype F] {α : Type} (program : OracleComp (Oracle Key F rate) α)
    (result : α × Monitor Key F rate b)
    (member : result ∈ support ((simulateQ handler program).run empty))
    (quiet : result.2.permutation.bad = false) : GoodHistory result.2.history :=
  (run_invariant program result member).2.2 quiet


omit [Zero F] in
/-- Allocation attempts never consume a primitive call, including refused attempts. -/
theorem register_permutation (s : Monitor Key F rate b) (key : Key) (roots : List D) :
    (register s key roots).2.permutation = s.permutation := by
  unfold register
  split <;> rfl

/-- All raw calls are equations of the same final partial bijection, also on bad runs. -/
theorem run_association [Fintype F] {α : Type} (program : OracleComp (Oracle Key F rate) α)
    (result : α × Monitor Key F rate b)
    (member : result ∈ support ((simulateQ handler program).run empty)) :
    (∀ e ∈ calls result.2.history, e.input ∈ result.2.permutation.used ∧
      result.2.permutation.completion e.input = e.output) ∧
    result.2.roots.entries = registered result.2.history ∧
    (registered result.2.history).length ≤ b := by
  have inv := run_invariant program result member
  refine ⟨?_, inv.2.1, inv.2.1 ▸ result.2.roots.bounded⟩
  intro e em
  obtain ⟨born, bm, same⟩ := pair_covered em
  simpa [same.1, same.2] using inv.1.1 born bm

end ZkcSecurity.Commitment.PoseidonRows.Monitored
