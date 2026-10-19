module

public import ZkcSecurity.Commitment.Verifier

@[expose] public section

/-! # The joint record: targets, good records, stable extraction

A run of the joint experiment against a complete answer table records a list of joint keys,
transcript keys and hash calls, each answered by the table. This module states what a hash call
must avoid for the extracted tables to be stable and the openings consistent, deterministically,
for any key list and table.

* The **targets** of a record (`targets`) are the labels a fresh hash answer must not hit: every
  earlier hash answer (a collision), every input label of an earlier hash call, and the first
  `bound` roots committed in every earlier transcript key (a root or a pending child label of a
  checkpoint extraction).
* A record is **good** (`GoodFrom`) when every hash call that is new to the record is answered
  outside the targets of the record before it.

In a good record, distinct hash calls have distinct answers (`responseInjective_of_good`), and the
table extracted for a root of a transcript key at the checkpoint before the key's first query is
the table extracted from the whole record (`extract_checkpoint_eq`). These are the two facts the
joint security argument needs to replace the checkpoint tables and the authenticated openings by
one extraction. `good_of_forall_not_bad` turns the absence of a bad hash call, judged at its first
query, into a good record.
-/

set_option autoImplicit false

namespace ZkcSecurity.Commitment

open OracleComp OracleSpec

variable {E Shape Value Query Y : Type} {Raw : E → Type}

/-- A complete answer table of the joint oracle. -/
abbrev JointTable (Raw : E → Type) (Shape Y Query : Type) :=
  (key : JointKey E Shape Y Query) → JointRange Raw Shape Y Query key

/-- The keys before the first occurrence of `key`; all of them when `key` does not occur. -/
def beforeFirstKey [DecidableEq E] [DecidableEq Shape] [DecidableEq Y] [DecidableEq Query]
    (key : JointKey E Shape Y Query) (keys : List (JointKey E Shape Y Query)) :
    List (JointKey E Shape Y Query) :=
  keys.takeWhile fun other => decide (other ≠ key)

/-- The hash calls of a key list with their answers in the table. -/
def hashLog (table : JointTable Raw Shape Y Query) (keys : List (JointKey E Shape Y Query)) :
    HashLog Query Y :=
  keys.filterMap fun key =>
    match key with
    | .inr query => some (⟨query, table (.inr query)⟩ : (_ : Query) × Y)
    | .inl _ => none

/-- The first `bound` roots committed in a transcript key's history. -/
def keyRoots (bound : ℕ) (key : TranscriptKey E Shape Y) : List Y :=
  ((key.1.filterMap Absorbed.committed).map Prod.snd).take bound

/-- The labels a key adds to the targets. -/
def keyTargets (scheme : Extractable Shape Value Query Y) (bound : ℕ)
    (table : JointTable Raw Shape Y Query) : JointKey E Shape Y Query → List Y
  | .inl transcript => keyRoots bound transcript
  | .inr query => table (.inr query) :: scheme.inputs query

/-- The targets of a record. -/
def targets (scheme : Extractable Shape Value Query Y) (bound : ℕ)
    (table : JointTable Raw Shape Y Query) (keys : List (JointKey E Shape Y Query)) : List Y :=
  keys.flatMap (keyTargets scheme bound table)

/-- Every hash call new to the record is answered outside the targets of the record before it. -/
def GoodFrom (scheme : Extractable Shape Value Query Y) (bound : ℕ)
    (table : JointTable Raw Shape Y Query) :
    List (JointKey E Shape Y Query) → List (JointKey E Shape Y Query) → Prop
  | _, [] => True
  | earlier, key :: rest =>
      (∀ query, key = .inr query → key ∉ earlier →
        table (.inr query) ∉ targets scheme bound table earlier) ∧
      GoodFrom scheme bound table (earlier ++ [key]) rest

section Lemmas
variable (scheme : Extractable Shape Value Query Y) (bound : ℕ)
  (table : JointTable Raw Shape Y Query)

@[simp] theorem hashLog_nil : hashLog table ([] : List (JointKey E Shape Y Query)) = [] := rfl

theorem hashLog_append (first second : List (JointKey E Shape Y Query)) :
    hashLog table (first ++ second) = hashLog table first ++ hashLog table second := by
  simp [hashLog, List.filterMap_append]

theorem hashLog_singleton_inl (transcript : TranscriptKey E Shape Y) :
    hashLog (Query := Query) table [.inl transcript] = [] := rfl

theorem hashLog_singleton_inr (query : Query) :
    hashLog table [(.inr query : JointKey E Shape Y Query)] = [⟨query, table (.inr query)⟩] := rfl

theorem mem_hashLog {keys : List (JointKey E Shape Y Query)} {query : Query}
    (member : (.inr query : JointKey E Shape Y Query) ∈ keys) :
    (⟨query, table (.inr query)⟩ : (_ : Query) × Y) ∈ hashLog table keys := by
  unfold hashLog
  rw [List.mem_filterMap]
  exact ⟨.inr query, member, rfl⟩

theorem mem_of_mem_hashLog {keys : List (JointKey E Shape Y Query)} {entry : (_ : Query) × Y}
    (member : entry ∈ hashLog table keys) :
    (.inr entry.1 : JointKey E Shape Y Query) ∈ keys ∧ entry = ⟨entry.1, table (.inr entry.1)⟩ := by
  unfold hashLog at member
  rw [List.mem_filterMap] at member
  obtain ⟨key, keyMember, found⟩ := member
  cases key with
  | inl _ => simp at found
  | inr query =>
      simp only [Option.some.injEq] at found
      subst found
      exact ⟨keyMember, rfl⟩

theorem targets_append (first second : List (JointKey E Shape Y Query)) :
    targets scheme bound table (first ++ second) =
      targets scheme bound table first ++ targets scheme bound table second := by
  simp [targets, List.flatMap_append]

theorem answer_mem_targets {keys : List (JointKey E Shape Y Query)} {entry : (_ : Query) × Y}
    (member : entry ∈ hashLog table keys) : entry.2 ∈ targets scheme bound table keys := by
  obtain ⟨keyMember, shape⟩ := mem_of_mem_hashLog table member
  rw [targets, List.mem_flatMap]
  refine ⟨.inr entry.1, keyMember, ?_⟩
  rw [shape]
  exact List.mem_cons_self

theorem input_mem_targets {keys : List (JointKey E Shape Y Query)} {entry : (_ : Query) × Y}
    (member : entry ∈ hashLog table keys) {label : Y} (input : label ∈ scheme.inputs entry.1) :
    label ∈ targets scheme bound table keys := by
  obtain ⟨keyMember, _⟩ := mem_of_mem_hashLog table member
  rw [targets, List.mem_flatMap]
  exact ⟨.inr entry.1, keyMember, List.mem_cons_of_mem _ input⟩

theorem root_mem_targets {keys : List (JointKey E Shape Y Query)} {transcript : TranscriptKey E Shape Y}
    (member : (.inl transcript : JointKey E Shape Y Query) ∈ keys) {root : Y}
    (rooted : root ∈ keyRoots bound transcript) : root ∈ targets scheme bound table keys := by
  rw [targets, List.mem_flatMap]
  exact ⟨.inl transcript, member, rooted⟩

theorem goodFrom_append (earlier first second : List (JointKey E Shape Y Query)) :
    GoodFrom scheme bound table earlier (first ++ second) ↔
      GoodFrom scheme bound table earlier first ∧
        GoodFrom scheme bound table (earlier ++ first) second := by
  induction first generalizing earlier with
  | nil => simp [GoodFrom]
  | cons key rest ih =>
      simp only [List.cons_append, GoodFrom, ih, List.append_assoc]
      tauto

/-- In a good record, distinct hash calls have distinct answers. -/
theorem responseInjective_of_good :
    ∀ (earlier rest : List (JointKey E Shape Y Query)),
      MerkleTreeExtractor.ResponseInjectiveOn (hashLog table earlier) →
      GoodFrom scheme bound table earlier rest →
      MerkleTreeExtractor.ResponseInjectiveOn (hashLog table (earlier ++ rest)) := by
  intro earlier rest
  induction rest generalizing earlier with
  | nil => intro injective _; simpa using injective
  | cons key rest ih =>
      intro injective good
      obtain ⟨fresh, later⟩ := good
      rw [← List.singleton_append, ← List.append_assoc]
      refine ih (earlier ++ [key]) ?_ later
      cases key with
      | inl transcript =>
          rwa [hashLog_append, hashLog_singleton_inl, List.append_nil]
      | inr query =>
          rw [hashLog_append, hashLog_singleton_inr]
          by_cases seen : (.inr query : JointKey E Shape Y Query) ∈ earlier
          · have old : (⟨query, table (.inr query)⟩ : (_ : Query) × Y) ∈ hashLog table earlier :=
              mem_hashLog table seen
            intro first firstMember second secondMember same
            rw [List.mem_append, List.mem_singleton] at firstMember secondMember
            rcases firstMember with firstOld | rfl <;> rcases secondMember with secondOld | rfl
            · exact injective _ firstOld _ secondOld same
            · exact injective _ firstOld _ old same
            · exact injective _ old _ secondOld same
            · rfl
          · have outside := fresh query rfl seen
            intro first firstMember second secondMember same
            rw [List.mem_append, List.mem_singleton] at firstMember secondMember
            rcases firstMember with firstOld | rfl <;> rcases secondMember with secondOld | rfl
            · exact injective _ firstOld _ secondOld same
            · have hit := answer_mem_targets scheme bound table firstOld
              rw [same] at hit
              exact absurd hit outside
            · have hit := answer_mem_targets scheme bound table secondOld
              rw [← same] at hit
              exact absurd hit outside
            · rfl

/-- A good record whose start already makes `root` a target keeps every extraction of `root`. -/
theorem extract_stable (shape : Shape) (root : Y) :
    ∀ (earlier rest : List (JointKey E Shape Y Query)),
      root ∈ targets scheme bound table earlier →
      GoodFrom scheme bound table earlier rest →
      scheme.extract (hashLog table (earlier ++ rest)) shape root =
        scheme.extract (hashLog table earlier) shape root := by
  intro earlier rest
  induction rest generalizing earlier with
  | nil => intro _ _; simp
  | cons key rest ih =>
      intro rooted good
      obtain ⟨fresh, later⟩ := good
      rw [← List.singleton_append, ← List.append_assoc]
      have targeted : root ∈ targets scheme bound table (earlier ++ [key]) := by
        rw [targets_append]
        exact List.mem_append_left _ rooted
      rw [ih (earlier ++ [key]) targeted later]
      cases key with
      | inl transcript => rw [hashLog_append, hashLog_singleton_inl, List.append_nil]
      | inr query =>
          rw [hashLog_append, hashLog_singleton_inr]
          by_contra changed
          obtain ⟨absent, hit⟩ := scheme.extract_append _ _ shape root changed
          have unseen : (.inr query : JointKey E Shape Y Query) ∉ earlier :=
            fun seen => absent (mem_hashLog table seen)
          have outside := fresh query rfl unseen
          rcases hit with isRoot | ⟨recorded, member, input⟩
          · rw [← isRoot] at rooted
            exact outside rooted
          · exact outside (input_mem_targets scheme bound table member input)

/-- A key list containing `key` is the keys before its first occurrence, that occurrence and the
rest. -/
theorem eq_beforeFirstKey_append [DecidableEq E] [DecidableEq Shape] [DecidableEq Y]
    [DecidableEq Query] (key : JointKey E Shape Y Query) :
    ∀ keys : List (JointKey E Shape Y Query), key ∈ keys →
      ∃ rest, keys = beforeFirstKey key keys ++ key :: rest
  | [], member => absurd member List.not_mem_nil
  | head :: tail, member => by
      by_cases same : head = key
      · subst same
        exact ⟨tail, by simp [beforeFirstKey]⟩
      · have later : key ∈ tail := by
          rcases List.mem_cons.mp member with first | inTail
          · exact absurd first.symm same
          · exact inTail
        obtain ⟨rest, split⟩ := eq_beforeFirstKey_append key tail later
        refine ⟨rest, ?_⟩
        simp only [beforeFirstKey, List.takeWhile_cons, ne_eq, same, not_false_eq_true,
          decide_true, ↓reduceIte, List.cons_append] at split ⊢
        exact congrArg (List.cons head) split

/-- In a good record, the table extracted for a root of a transcript key at the checkpoint before
the key's first query is the table extracted from the whole record. -/
theorem extract_checkpoint_eq [DecidableEq E] [DecidableEq Shape] [DecidableEq Y]
    [DecidableEq Query] (keys : List (JointKey E Shape Y Query))
    (good : GoodFrom scheme bound table [] keys) (transcript : TranscriptKey E Shape Y)
    (member : (.inl transcript : JointKey E Shape Y Query) ∈ keys) (shape : Shape) {root : Y}
    (rooted : root ∈ keyRoots bound transcript) :
    scheme.extract (hashLog table (beforeFirstKey (.inl transcript) keys)) shape root =
      scheme.extract (hashLog table keys) shape root := by
  obtain ⟨rest, split⟩ := eq_beforeFirstKey_append (.inl transcript) keys member
  set before := beforeFirstKey (.inl transcript) keys
  rw [split] at good
  rw [split, ← List.singleton_append, ← List.append_assoc] at *
  have halves := (goodFrom_append scheme bound table [] (before ++ [.inl transcript]) rest).mp good
  rw [List.nil_append] at halves
  rw [extract_stable scheme bound table shape root _ _ (by
      rw [targets_append]
      exact List.mem_append_right _ (root_mem_targets scheme bound table
        (List.mem_singleton_self _) rooted)) halves.2,
    hashLog_append, hashLog_singleton_inl, List.append_nil]

/-- A record whose every hash call, judged against the targets before its first query, misses
them is good. -/
theorem good_of_forall_not_bad [DecidableEq E] [DecidableEq Shape] [DecidableEq Y]
    [DecidableEq Query] :
    ∀ (earlier keys : List (JointKey E Shape Y Query)),
      (∀ query, (.inr query : JointKey E Shape Y Query) ∈ keys →
        (.inr query : JointKey E Shape Y Query) ∉ earlier →
        table (.inr query) ∉ targets scheme bound table
          (earlier ++ beforeFirstKey (.inr query) keys)) →
      GoodFrom scheme bound table earlier keys := by
  intro earlier keys
  induction keys generalizing earlier with
  | nil => intro _; trivial
  | cons key rest ih =>
      intro notBad
      refine ⟨?_, ih (earlier ++ [key]) ?_⟩
      · rintro query rfl unseen
        have := notBad query List.mem_cons_self unseen
        simpa [beforeFirstKey] using this
      · intro query member unseen
        have notEarlier : (.inr query : JointKey E Shape Y Query) ∉ earlier :=
          fun seen => unseen (List.mem_append_left _ seen)
        have notKey : key ≠ .inr query :=
          fun same => unseen (List.mem_append_right _ (same ▸ List.mem_singleton_self _))
        have := notBad query (List.mem_cons_of_mem _ member) notEarlier
        simpa [beforeFirstKey, notKey, List.append_assoc] using this

end Lemmas

end ZkcSecurity.Commitment
