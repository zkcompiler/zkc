module

public import ZkcSecurity.Examples.CommittedOpening
public import ZkcSecurity.Commitment.HashedLeaves
public import ZkcSecurity.Commitment.Experiment
public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

@[expose] public section

/-! # The bound of the committed-opening experiment

`intendedBound` proves `CommittedOpening.IntendedBound` for the straight-line extractor
`extractor`: in the joint experiment of the smallest protocol with a committed table, one
challenge and an authenticated opening, every adversary within the budgets of `q_T` transcript
calls and `q_M` hash calls makes the validator accept while the table extracted at its checkpoint
key is far with probability at most

`(q_T + 1) · 1 · (1 - δ) + (q_M + k + 1) · 4 (q_T + q_M + k + 2) / |Digest| + 0`,

for both readings of the terminal opening (absorbed or omitted). The history-oracle term has
factor `1` because the index is decoded exactly; the extraction term charges each of the at most
`q_M + k + 1` hash calls of the experiment (the adversary's and the validator's `k + 1`) the number
of labels it must avoid over the number of digests; the namespace term is `0` because the
transcript keys and the hash calls are separate families of the joint oracle.

**The extractor.** `extractor` reads the table committed by the root of a checkpoint key from the
hash calls of the record before the key's first query: from the root it follows the first
recorded node call answered by each label (most significant bit of the index first) and reads the
row of the first recorded leaf call answered by the leaf label
(`ZkcSecurity.Commitment.LeafHashing`). It always returns a table, with the empty row where nothing
is extracted. An extractor that returned no table whenever some row is missing would make the
intended bound false: an adversary that computes the left half of the tree honestly and a random
right child, then opens honestly when the index falls left, makes the validator accept with
probability one half while `Far none` holds.

**The proof.** One application of VCVio's weighted bad-query bound to the logged experiment
(`loggedRun` is the random-oracle run of `withQueryLog`, `loggedRun_eq`). A transcript key is bad
when it is the validator's key for a root, its frozen table is far, and its answer selects an
accepted row (`Bad`): the frozen table is fixed before the answer (`frozen_update`), so the
probability is at most `1 - δ`. A hash call is bad when its answer hits a target of the record
before its first query, read through the joint record of `ZkcSecurity.Commitment.Record`. Without
a bad hash call the record is good, the authenticated row is the row extracted from the whole
record (`LeafHashing.extractLabel_of_climbs`) and the frozen table agrees with it
(`extract_checkpoint_eq`), so an accepting run with a far frozen table queries a bad key.
-/

set_option autoImplicit false

namespace ZkcSecurity.Examples.CommittedOpening

open OracleComp OracleSpec ZkcSecurity.Commitment

variable {Context Scheme Coordinate Digest : Type}

/-! ### The extractor -/

/-- The leaf and node calls of the joint namespace's hash family. -/
def leafHashing : LeafHashing (List Coordinate) (HashCall (List Coordinate) Digest) Digest where
  leaf := .leaf
  node := .node
  leafRow
    | .leaf row => some row
    | .node _ _ => none
  children
    | .node left right => some (left, right)
    | .leaf _ => none
  leafRow_leaf _ := rfl
  children_node _ _ := rfl

/-- The hash calls of a record. -/
def hashRecord (record : Record Context Scheme (List Coordinate) Digest) :
    HashLog (HashCall (List Coordinate) Digest) Digest :=
  record.filterMap fun entry =>
    match entry with
    | ⟨.hash call, answer⟩ => some ⟨call, answer⟩
    | ⟨.transcript _, _⟩ => none

/-- The root a transcript key carries, if any. -/
def rootOfKey (key : List (Event Context Scheme (List Coordinate) Digest)) : Option Digest :=
  key.findSome? fun
    | .root value => some value
    | _ => none

/-- The straight-line extractor: the rows of the tree committed by the key's root, read from the
hash calls of the record, with the empty row where nothing is extracted. -/
def extractor [DecidableEq Digest] : Extractor Context Scheme Coordinate Digest :=
  fun configuration key record => some fun index =>
    match rootOfKey key with
    | some rootValue =>
        ((leafHashing.extract (hashRecord record) configuration.depth rootValue) index.val).getD []
    | none => []

theorem rootOfKey_verifierKey (context : Context) (configuration : Configuration Scheme)
    (rootValue : Digest) :
    rootOfKey (Coordinate := Coordinate) (verifierKey context configuration rootValue) =
      some rootValue := rfl

/-! ### The joint record -/

/-- Absorbed events as joint-record events: roots are commitments. -/
def absorbedOf : Event Context Scheme (List Coordinate) Digest →
    Absorbed (Event Context Scheme (List Coordinate) Digest) ℕ Digest
  | .root value => .root 0 value
  | event => .event event

theorem absorbedOf_injective :
    Function.Injective (absorbedOf (Context := Context) (Scheme := Scheme)
      (Coordinate := Coordinate) (Digest := Digest)) := by
  intro first second same
  cases first <;> cases second <;> simp_all [absorbedOf]

/-- Queries of the joint namespace as joint-record keys. -/
def jointKey : Query Context Scheme (List Coordinate) Digest →
    JointKey (Event Context Scheme (List Coordinate) Digest) ℕ Digest
      (HashCall (List Coordinate) Digest)
  | .transcript key => .inl (key.map absorbedOf, .position 0)
  | .hash call => .inr call

theorem jointKey_injective :
    Function.Injective (jointKey (Context := Context) (Scheme := Scheme)
      (Coordinate := Coordinate) (Digest := Digest)) := by
  intro first second same
  cases first <;> cases second <;> simp only [jointKey, Sum.inl.injEq, Sum.inr.injEq,
    Prod.mk.injEq, reduceCtorEq] at same
  · exact congrArg _ ((List.map_injective_iff.mpr absorbedOf_injective) same.1)
  · exact congrArg _ same

/-- The answers of the joint namespace as a joint-record table: only the hash answers matter. -/
def jointAnswers (answers : (query : Query Context Scheme (List Coordinate) Digest) → Range query) :
    JointTable (fun _ : Event Context Scheme (List Coordinate) Digest => Unit) ℕ Digest
      (HashCall (List Coordinate) Digest)
  | .inl _ => ()
  | .inr call => answers (.hash call)

/-- The keys of a record as joint-record keys. -/
def jointKeys (record : Record Context Scheme (List Coordinate) Digest) :
    List (JointKey (Event Context Scheme (List Coordinate) Digest) ℕ Digest
      (HashCall (List Coordinate) Digest)) :=
  record.map fun entry => jointKey entry.1

section Record
variable [DecidableEq Context] [DecidableEq Scheme] [DecidableEq Coordinate] [DecidableEq Digest]

instance jointKeyDecidableEq : DecidableEq (JointKey (Event Context Scheme (List Coordinate) Digest)
    ℕ Digest (HashCall (List Coordinate) Digest)) := by
  haveI : DecidableEq (Event Context Scheme (List Coordinate) Digest) := inferInstance
  haveI : DecidableEq (HashCall (List Coordinate) Digest) := inferInstance
  haveI : DecidableEq (Absorbed (Event Context Scheme (List Coordinate) Digest) ℕ Digest) :=
    inferInstance
  exact inferInstance

omit [DecidableEq Context] [DecidableEq Scheme] [DecidableEq Coordinate] [DecidableEq Digest] in
/-- The hash calls of a table record are the joint record's hash log. -/
theorem hashLog_jointKeys (answers : (query : Query Context Scheme (List Coordinate) Digest) →
    Range query) :
    ∀ record : Record Context Scheme (List Coordinate) Digest,
      (∀ entry ∈ record, entry = ⟨entry.1, answers entry.1⟩) →
      hashLog (jointAnswers answers) (jointKeys record) = hashRecord record
  | [] => fun _ => rfl
  | ⟨query, answer⟩ :: rest => fun consistent => by
      have head := consistent _ List.mem_cons_self
      have tail := hashLog_jointKeys answers rest
        fun entry member => consistent entry (List.mem_cons_of_mem _ member)
      simp only at head
      cases query with
      | transcript key =>
          change hashLog (jointAnswers answers) ([jointKey (.transcript key)] ++ jointKeys rest) =
            hashRecord rest
          rw [hashLog_append, jointKey, hashLog_singleton_inl, List.nil_append, tail]
      | hash call =>
          simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at head
          subst head
          change hashLog (jointAnswers answers) ([jointKey (.hash call)] ++ jointKeys rest) =
            ⟨call, answers (.hash call)⟩ :: hashRecord rest
          rw [hashLog_append, jointKey, hashLog_singleton_inr, tail]
          rfl

/-- The record before a transcript key's first query, as joint-record keys. -/
theorem jointKeys_beforeFirst (key : List (Event Context Scheme (List Coordinate) Digest)) :
    ∀ record : Record Context Scheme (List Coordinate) Digest,
      jointKeys (CommittedOpening.beforeFirst key record) =
        beforeFirstKey (jointKey (.transcript key)) (jointKeys record)
  | [] => rfl
  | entry :: rest => by
      unfold CommittedOpening.beforeFirst at *
      have later := jointKeys_beforeFirst key rest
      unfold CommittedOpening.beforeFirst at later
      by_cases same : entry.1 = .transcript key
      · simp [jointKeys, beforeFirstKey, same]
      · have different : jointKey entry.1 ≠ jointKey (.transcript key) :=
          fun equal => same (jointKey_injective equal)
        simp only [jointKeys, beforeFirstKey, List.takeWhile_cons, ne_eq, same,
          not_false_eq_true, decide_true, ↓reduceIte, List.map_cons, different] at later ⊢
        exact congrArg _ later

/-- The record before a hash call's first query, as joint-record keys. -/
theorem jointKeys_beforeFirst_hash (call : HashCall (List Coordinate) Digest) :
    ∀ record : Record Context Scheme (List Coordinate) Digest,
      jointKeys (ZkcSecurity.Commitment.beforeFirst (.hash call) record) =
        beforeFirstKey (jointKey (.hash call)) (jointKeys record)
  | [] => rfl
  | entry :: rest => by
      have later := jointKeys_beforeFirst_hash call rest
      rw [ZkcSecurity.Commitment.beforeFirst_cons]
      by_cases same : entry.1 = .hash call
      · simp [jointKeys, beforeFirstKey, same]
      · have different : jointKey entry.1 ≠ jointKey (.hash call) :=
          fun equal => same (jointKey_injective equal)
        simp only [same, ↓reduceIte, jointKeys, List.map_cons, beforeFirstKey,
          List.takeWhile_cons, ne_eq, different, not_false_eq_true, decide_true] at later ⊢
        exact congrArg _ later

theorem jointAnswers_update (answers : (query : Query Context Scheme (List Coordinate) Digest) →
    Range query) (call : HashCall (List Coordinate) Digest) (answer : Digest) :
    jointAnswers (Function.update answers (.hash call) answer) =
      Function.update (jointAnswers answers) (.inr call) answer := by
  funext key
  cases key with
  | inl _ => rfl
  | inr other =>
      by_cases same : other = call
      · subst same
        simp only [jointAnswers, Function.update_self]
        exact (Function.update_self (f := jointAnswers answers) (Sum.inr other) answer).symm
      · have different : (Query.hash other : Query Context Scheme (List Coordinate) Digest) ≠
            .hash call := by simpa using same
        simp only [jointAnswers]
        rw [Function.update_of_ne different]
        have ne : (Sum.inr other : JointKey (Event Context Scheme (List Coordinate) Digest) ℕ Digest
            (HashCall (List Coordinate) Digest)) ≠ .inr call := by simpa using same
        exact (Function.update_of_ne ne answer (jointAnswers answers)).symm

end Record

/-! ### Runs of the validator against a complete answer table -/

section Runs

/-- The hash calls of a climb against complete answers, in call order. -/
def climbEntries (answers : (query : Query Context Scheme (List Coordinate) Digest) → Range query) :
    ℕ → List Digest → Digest → Record Context Scheme (List Coordinate) Digest
  | _, [], _ => []
  | index, sibling :: rest, current =>
      ⟨.hash (parent index current sibling), answers (.hash (parent index current sibling))⟩ ::
        climbEntries answers (index / 2) rest (answers (.hash (parent index current sibling)))

theorem tableQueryLog_climb {A : Type}
    (answers : (query : Query Context Scheme (List Coordinate) Digest) → Range query)
    (absorbOpening : Bool) (next : Digest → PIR.Proc (signature (List Coordinate) Digest) A)
    (history : List (Event Context Scheme (List Coordinate) Digest))
    (proof : List (Message (List Coordinate) Digest)) :
    ∀ (index : ℕ) (siblings : List Digest) (current : Digest),
      tableQueryLog (oracleReading absorbOpening ((climbProcess index siblings current).bind next)
          history proof) answers =
        climbEntries answers index siblings current ++
          tableQueryLog (oracleReading absorbOpening
            (next (climb (hashOf answers) index siblings current)) history proof) answers
  | _, [], _ => rfl
  | index, sibling :: rest, current => by
      simp only [climbProcess, PIR.Proc.bind, oracleReading, interpret]
      rw [tableQueryLog_query_bind]
      exact congrArg (List.cons _) (tableQueryLog_climb answers absorbOpening next history proof
        (index / 2) rest _)

theorem climbs_climbEntries
    (answers : (query : Query Context Scheme (List Coordinate) Digest) → Range query) :
    ∀ (index : ℕ) (siblings : List Digest) (current : Digest),
      LeafHashing.Climbs leafHashing (hashRecord (climbEntries answers index siblings current))
        index siblings current (climb (hashOf answers) index siblings current)
  | _, [], _ => rfl
  | index, _ :: rest, _ =>
      ⟨_, List.mem_cons_self, LeafHashing.climbs_mono leafHashing
        (fun _ member => List.mem_cons_of_mem _ member) _ _ _ _
        (climbs_climbEntries answers (index / 2) rest _)⟩

variable [DecidableEq Digest]

/-- The validator's record on a proof that starts with a root and an opening: its transcript
query, then, when the opening has the configured shape, the leaf hash and the climb. -/
theorem tableQueryLog_verifier (accepts : Scheme → List Coordinate → Bool) (absorbOpening : Bool)
    (context : Context) (configuration : Configuration Scheme)
    (answers : (query : Query Context Scheme (List Coordinate) Digest) → Range query)
    (rootValue : Digest) (row : List Coordinate) (siblings : List Digest)
    (rest : List (Message (List Coordinate) Digest)) :
    tableQueryLog (oracleReading absorbOpening (verifier accepts configuration)
        (initial context configuration) (.root rootValue :: .opening row siblings :: rest)) answers =
      ⟨.transcript (verifierKey context configuration rootValue),
        answers (.transcript (verifierKey context configuration rootValue))⟩ ::
        (if row.length = configuration.width ∧ siblings.length = configuration.depth then
          ⟨.hash (.leaf row), answers (.hash (.leaf row))⟩ ::
            climbEntries answers (decodeIndex configuration.depth
              (answers (.transcript (verifierKey context configuration rootValue)))).val siblings
              (answers (.hash (.leaf row)))
        else []) := by
  simp only [verifier, oracleReading, interpret, verifierKey, initial, List.cons_append,
    List.nil_append]
  rw [tableQueryLog_query_bind]
  refine congrArg (List.cons _) ?_
  simp only [authenticate]
  split
  · simp only [PIR.Proc.bind, interpret]
    rw [tableQueryLog_query_bind]
    refine congrArg (List.cons _) ?_
    rw [CommittedOpening.bind_assoc]
    refine (tableQueryLog_climb answers absorbOpening _ _ _ _ _ _).trans ?_
    simp only [PIR.Proc.bind]
    split <;> simp [oracleReading, interpret]
  · simp [PIR.Proc.bind, interpret]

/-- The joint experiment against complete answers: the adversary's proof and the validator's
outcome. -/
theorem evalWithAnswerFn_experiment (accepts : Scheme → List Coordinate → Bool)
    (absorbOpening : Bool) (context : Context) (configuration : Configuration Scheme)
    (adversary : OracleComp (spec Context Scheme (List Coordinate) Digest)
      (List (Message (List Coordinate) Digest)))
    (answers : (query : Query Context Scheme (List Coordinate) Digest) → Range query) :
    evalWithAnswerFn (QueryImpl.ofFn answers)
        (experiment accepts absorbOpening context configuration adversary) =
      (evalWithAnswerFn (QueryImpl.ofFn answers) adversary,
        interpret (m := Id) (fun query => answers query) absorbOpening (verifier accepts configuration)
          (initial context configuration) (evalWithAnswerFn (QueryImpl.ofFn answers) adversary)) := by
  simp only [experiment, evalWithAnswerFn_bind, evalWithAnswerFn_map, evalWithAnswerFn_interpret,
    QueryImpl.ofFn_apply]

theorem tableQueryLog_experiment (accepts : Scheme → List Coordinate → Bool)
    (absorbOpening : Bool) (context : Context) (configuration : Configuration Scheme)
    (adversary : OracleComp (spec Context Scheme (List Coordinate) Digest)
      (List (Message (List Coordinate) Digest)))
    (answers : (query : Query Context Scheme (List Coordinate) Digest) → Range query) :
    tableQueryLog (experiment accepts absorbOpening context configuration adversary) answers =
      tableQueryLog adversary answers ++ tableQueryLog (oracleReading absorbOpening
        (verifier accepts configuration) (initial context configuration)
        (evalWithAnswerFn (QueryImpl.ofFn answers) adversary)) answers := by
  simp only [experiment, tableQueryLog_bind, ZkcSecurity.Commitment.tableQueryLog_map]

/-- An accepting run reads a root and an opening of the configured shape whose climb reaches the
root, at the index the transcript answers at the validator's key, and the row is accepted. -/
theorem accepted_shape (accepts : Scheme → List Coordinate → Bool) (absorbOpening : Bool)
    (context : Context) (configuration : Configuration Scheme)
    (answers : (query : Query Context Scheme (List Coordinate) Digest) → Range query)
    (proof : List (Message (List Coordinate) Digest))
    (accepted : (interpret (m := Id) (fun query => answers query) absorbOpening
      (verifier accepts configuration) (initial context configuration) proof).1 = .returned true) :
    ∃ rootValue row siblings rest, proof = .root rootValue :: .opening row siblings :: rest ∧
      row.length = configuration.width ∧ siblings.length = configuration.depth ∧
      climb (hashOf answers) (decodeIndex configuration.depth
          (answers (.transcript (verifierKey context configuration rootValue)))).val siblings
          (hashOf answers (.leaf row)) = rootValue ∧
      accepts configuration.scheme row = true := by
  match proof with
  | [] => simp [verifier, interpret] at accepted
  | .opening _ _ :: _ => simp [verifier, interpret] at accepted
  | [.root _] => simp [verifier, interpret, id_bind_eq] at accepted
  | .root _ :: .root _ :: _ => simp [verifier, interpret, id_bind_eq] at accepted
  | .root rootValue :: .opening row siblings :: rest =>
      have outcome := congrArg Prod.fst (interpret_verifier (fun query => answers query) absorbOpening
        accepts configuration context rootValue row siblings rest)
      rw [show initial context configuration = [Event.binding context configuration] from rfl]
        at accepted
      rw [accepted] at outcome
      split at outcome
      · rename_i held
        simp only [PIR.Outcome.returned.injEq] at outcome
        exact ⟨rootValue, row, siblings, rest, rfl, held.1, held.2.1, held.2.2, outcome.symm⟩
      · simp at outcome

end Runs

/-! ### Budgets and charges -/

section Budgets
open ZkcSecurity.FiatShamir

/-- Family budgets bound the pathwise charge with a weight per family. -/
theorem familyQueryBound_costBound {α : Type} (weight : Family → ENNReal) :
    ∀ (computation : OracleComp (spec Context Scheme (List Coordinate) Digest) α)
      (budget : Provider.Budget Family),
      Provider.FamilyQueryBound familyOf computation budget →
        WorstCaseCostBound computation ⟨fun query => weight (familyOf query)⟩
          (budget .transcript * weight .transcript + budget .merkle * weight .merkle) := by
  intro computation
  induction computation using OracleComp.inductionOn with
  | pure value => intro _ _; exact (worstCaseCostBound_pure _ _ _).mpr zero_le
  | query_bind query next ih =>
      intro budget bounded
      obtain ⟨positive, rest⟩ := (Provider.familyQueryBound_query_bind_iff familyOf).mp bounded
      rw [worstCaseCostBound_query_bind_iff]
      intro reply cost member
      have tail := (worstCaseCostBound_iff_support_bound _ _ _).mp (ih reply _ (rest reply)) cost
        member
      refine (add_le_add le_rfl tail).trans (le_of_eq ?_)
      cases family : familyOf query with
      | transcript =>
          rw [family] at positive
          obtain ⟨count, hcount⟩ : ∃ count, budget .transcript = count + 1 :=
            ⟨budget .transcript - 1, by omega⟩
          simp only [family, Function.update_self, Function.update_of_ne (show
            (Family.merkle) ≠ .transcript from by decide), hcount, Nat.add_sub_cancel]
          push_cast
          ring
      | merkle =>
          rw [family] at positive
          obtain ⟨count, hcount⟩ : ∃ count, budget .merkle = count + 1 :=
            ⟨budget .merkle - 1, by omega⟩
          simp only [family, Function.update_self, Function.update_of_ne (show
            (Family.transcript) ≠ .merkle from by decide), hcount, Nat.add_sub_cancel]
          push_cast
          ring

/-- Family budgets bound the total number of calls. -/
theorem familyQueryBound_total {α : Type} :
    ∀ (computation : OracleComp (spec Context Scheme (List Coordinate) Digest) α)
      (budget : Provider.Budget Family),
      Provider.FamilyQueryBound familyOf computation budget →
        IsTotalQueryBound computation (budget .transcript + budget .merkle) := by
  intro computation
  induction computation using OracleComp.inductionOn with
  | pure value => intro _ _; trivial
  | query_bind query next ih =>
      intro budget bounded
      obtain ⟨positive, rest⟩ := (Provider.familyQueryBound_query_bind_iff familyOf).mp bounded
      rw [isTotalQueryBound_query_bind_iff]
      cases family : familyOf query with
      | transcript =>
          rw [family] at positive
          refine ⟨by omega, fun reply => ?_⟩
          have tail := rest reply
          rw [family] at tail
          have counted := ih reply _ tail
          simp only [Function.update_self, Function.update_of_ne (show
            (Family.merkle) ≠ .transcript from by decide)] at counted
          exact counted.mono (by omega)
      | merkle =>
          rw [family] at positive
          refine ⟨by omega, fun reply => ?_⟩
          have tail := rest reply
          rw [family] at tail
          have counted := ih reply _ tail
          simp only [Function.update_self, Function.update_of_ne (show
            (Family.transcript) ≠ .merkle from by decide)] at counted
          exact counted.mono (by omega)

/-- A climb of `n` levels makes `n` hash calls. -/
theorem climb_familyQueryBound {A : Type} (absorbOpening : Bool)
    (next : Digest → PIR.Proc (signature (List Coordinate) Digest) A)
    (history : List (Event Context Scheme (List Coordinate) Digest))
    (proof : List (Message (List Coordinate) Digest))
    (final : ∀ top budget, Provider.FamilyQueryBound familyOf
      (oracleReading absorbOpening (next top) history proof) budget) :
    ∀ (index : ℕ) (siblings : List Digest) (current : Digest) (budget : Provider.Budget Family),
      siblings.length ≤ budget .merkle →
      Provider.FamilyQueryBound familyOf (oracleReading absorbOpening
        ((climbProcess index siblings current).bind next) history proof) budget
  | _, [], _, budget, _ => final _ budget
  | index, sibling :: rest, current, budget, enough => by
      simp only [climbProcess, PIR.Proc.bind, oracleReading, interpret]
      rw [Provider.familyQueryBound_query_bind_iff]
      simp only [List.length_cons] at enough
      refine ⟨by simp only [familyOf]; omega, fun reply => ?_⟩
      exact climb_familyQueryBound absorbOpening next history proof final (index / 2) rest reply _
        (by simp only [familyOf, Function.update_self]; omega)

variable [DecidableEq Digest]

/-- The validator makes one transcript call and at most `k + 1` hash calls. -/
theorem verifier_familyQueryBound (accepts : Scheme → List Coordinate → Bool) (absorbOpening : Bool)
    (context : Context) (configuration : Configuration Scheme)
    (proof : List (Message (List Coordinate) Digest)) :
    Provider.FamilyQueryBound familyOf (oracleReading absorbOpening (verifier accepts configuration)
      (initial context configuration) proof)
      (fun | .transcript => 1 | .merkle => configuration.depth + 1) := by
  match proof with
  | [] => trivial
  | .opening _ _ :: _ => trivial
  | .root rootValue :: tail =>
      simp only [verifier, oracleReading, interpret]
      rw [Provider.familyQueryBound_query_bind_iff]
      refine ⟨by simp [familyOf], fun raw => ?_⟩
      match tail with
      | [] => trivial
      | .root _ :: _ => trivial
      | .opening row siblings :: rest =>
          simp only [interpret, authenticate]
          split
          · rename_i shape
            simp only [PIR.Proc.bind, interpret]
            rw [Provider.familyQueryBound_query_bind_iff]
            refine ⟨by simp [familyOf], fun leafDigest => ?_⟩
            rw [CommittedOpening.bind_assoc]
            refine climb_familyQueryBound absorbOpening _ _ _ (fun top budget => ?_) _ _ _ _ ?_
            · simp only [PIR.Proc.bind]
              split <;> trivial
            · simp [familyOf, shape.2]
          · simp only [PIR.Proc.bind]
            trivial

end Budgets

/-! ### Bad keys -/

section Bad
variable [DecidableEq Context] [DecidableEq Scheme] [DecidableEq Coordinate] [DecidableEq Digest]

/-- Bad keys of the joint table run of `game`. The validator's transcript key for a root is bad
when its frozen table is far and the answer at the key selects an accepted row; a hash call is
bad when its answer hits a target of the record before its first query. -/
def Bad (accepts : Scheme → List Coordinate → Bool) (context : Context)
    (configuration : Configuration Scheme) (fraction : ENNReal) {α : Type}
    (game : OracleComp (spec Context Scheme (List Coordinate) Digest) α) :
    (query : Query Context Scheme (List Coordinate) Digest) →
      ((query : Query Context Scheme (List Coordinate) Digest) → Range query) → Prop
  | .transcript key, answers =>
      (∃ rootValue, key = verifierKey context configuration rootValue) ∧
        ∃ table, frozen extractor configuration key (tableQueryLog game answers) = some table ∧
          Far accepts configuration fraction (some table) ∧
          accepts configuration.scheme
            (table (decodeIndex configuration.depth (answers (.transcript key)))) = true
  | .hash call, answers =>
      answers (.hash call) ∈ targets leafHashing.scheme 1 (jointAnswers answers)
        (beforeFirstKey (.inr call) (jointKeys (tableQueryLog game answers)))

omit [DecidableEq Context] [DecidableEq Scheme] [DecidableEq Coordinate] [DecidableEq Digest] in
/-- A far table accepts at most a `1 - δ` fraction of its rows. -/
theorem accepted_fraction_le (accepts : Scheme → List Coordinate → Bool)
    (configuration : Configuration Scheme) (fraction : ENNReal)
    (table : Fin (2 ^ configuration.depth) → List Coordinate)
    (far : Far accepts configuration fraction (some table)) :
    ((Finset.univ.filter fun index => accepts configuration.scheme (table index) = true).card :
        ENNReal) / (2 ^ configuration.depth : ℕ) ≤ 1 - fraction := by
  have total := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun index : Fin (2 ^ configuration.depth) => accepts configuration.scheme (table index) = true)
  simp only [Finset.card_univ, Fintype.card_fin, Bool.not_eq_true] at total
  have castTotal : ((Finset.univ.filter fun index : Fin (2 ^ configuration.depth) =>
      accepts configuration.scheme (table index) = true).card : ENNReal) +
      ((Finset.univ.filter fun index : Fin (2 ^ configuration.depth) =>
        accepts configuration.scheme (table index) = false).card : ENNReal) =
      ((2 ^ configuration.depth : ℕ) : ENNReal) := by exact_mod_cast total
  apply ENNReal.div_le_of_le_mul
  rw [ENNReal.eq_sub_of_add_eq (by simp) castTotal, ENNReal.sub_mul (fun _ _ => by simp), one_mul]
  refine tsub_le_tsub_left ?_ _
  simpa [Far] using far

/-- Resampling the validator's transcript key makes it bad with probability at most `1 - δ`: its
frozen table is fixed before the answer, and the decoded index is uniform. -/
theorem bad_transcript_resample [SampleableType Digest] (accepts : Scheme → List Coordinate → Bool)
    (context : Context) (configuration : Configuration Scheme) (fraction : ENNReal) {α : Type}
    (game : OracleComp (spec Context Scheme (List Coordinate) Digest) α)
    (key : List (Event Context Scheme (List Coordinate) Digest))
    (answers : (query : Query Context Scheme (List Coordinate) Digest) → Range query) :
    Pr{let answer ← $ᵗ (Range (Query.transcript (Row := List Coordinate) (Digest := Digest)
        (Context := Context) (Scheme := Scheme) key))}[
      Bad accepts context configuration fraction game (.transcript key)
        (Function.update answers (.transcript key) answer)] ≤ 1 - fraction := by
  have fixed : ∀ answer : Range (Query.transcript (Row := List Coordinate) (Digest := Digest)
      (Context := Context) (Scheme := Scheme) key),
      frozen extractor configuration key
          (tableQueryLog game (Function.update answers (.transcript key) answer)) =
        frozen extractor configuration key (tableQueryLog game answers) :=
    fun answer => frozen_update extractor configuration key game answers answer
  by_cases found : (∃ rootValue, key = verifierKey context configuration rootValue) ∧
      ∃ table, frozen extractor configuration key (tableQueryLog game answers) = some table ∧
        Far accepts configuration fraction (some table)
  · obtain ⟨⟨rootValue, rfl⟩, table, frozenTable, far⟩ := found
    have depth : depthOf (verifierKey (Row := List Coordinate) context configuration rootValue) =
        configuration.depth := by
      rw [verifierKey, show initial context configuration ++
          [Event.root rootValue, .position configuration.depth] =
          (initial context configuration ++ [Event.root rootValue]) ++
            [.position configuration.depth] by simp]
      exact depthOf_request _ _
    let index : Fin (2 ^ depthOf (verifierKey (Row := List Coordinate) context configuration
        rootValue)) ≃ Fin (2 ^ configuration.depth) := finCongr (by rw [depth])
    have decoded : ∀ answer, decodeIndex configuration.depth answer = index answer := by
      intro answer
      ext
      have below : answer.val < 2 ^ configuration.depth :=
        calc answer.val < 2 ^ depthOf (verifierKey (Row := List Coordinate) context configuration
              rootValue) := answer.isLt
          _ = 2 ^ configuration.depth := by rw [depth]
      simp [decodeIndex, index, Nat.mod_eq_of_lt below]
    calc _ ≤ Pr{let answer ← $ᵗ (Fin (2 ^ depthOf (verifierKey (Row := List Coordinate)
            context configuration rootValue)))}[
            accepts configuration.scheme (table (index answer)) = true] := by
          refine prEvent_mono _ _ _ fun answer bad => ?_
          obtain ⟨_, table', frozen', _, selected⟩ := bad
          rw [fixed, frozenTable] at frozen'
          cases Option.some.inj frozen'
          simpa only [Function.update_self, decoded] using selected
      _ = Pr{let row ← $ᵗ (Fin (2 ^ configuration.depth))}[
            accepts configuration.scheme (table row) = true] :=
          SampleableType.prEvent_uniformSample_equiv index
            (fun row => accepts configuration.scheme (table row) = true)
      _ ≤ 1 - fraction := by
          rw [SampleableType.prEvent_uniformSample, Fintype.card_fin]
          exact_mod_cast accepted_fraction_le accepts configuration fraction table far
  · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_not _ _ fun answer bad => ?_) zero_le
    obtain ⟨rooted, table, frozen', far, _⟩ := bad
    rw [fixed] at frozen'
    exact found ⟨rooted, table, frozen', far⟩

/-- Resampling a hash call makes it bad with probability at most the number of targets over the
number of digests. -/
theorem bad_hash_resample [SampleableType Digest] [Fintype Digest]
    (accepts : Scheme → List Coordinate → Bool) (context : Context)
    (configuration : Configuration Scheme) (fraction : ENNReal) {α : Type}
    (game : OracleComp (spec Context Scheme (List Coordinate) Digest) α) (targetBound : ℕ)
    (bounded : ∀ answers : (query : Query Context Scheme (List Coordinate) Digest) → Range query,
      (targets leafHashing.scheme 1 (jointAnswers answers)
        (jointKeys (tableQueryLog game answers))).length ≤ targetBound)
    (call : HashCall (List Coordinate) Digest)
    (answers : (query : Query Context Scheme (List Coordinate) Digest) → Range query) :
    Pr{let answer ← $ᵗ (Range (Query.hash (Context := Context) (Scheme := Scheme) call))}[
      Bad accepts context configuration fraction game (.hash call)
        (Function.update answers (.hash call) answer)] ≤
      (targetBound : ENNReal) / Fintype.card Digest := by
  set before := beforeFirstKey (.inr call) (jointKeys (tableQueryLog game answers))
  have fixed : ∀ answer : Digest,
      Bad accepts context configuration fraction game (.hash call)
          (Function.update answers (.hash call) answer) ↔
        answer ∈ targets leafHashing.scheme 1 (jointAnswers answers) before := by
    intro answer
    change Function.update answers (.hash call) answer (.hash call) ∈ targets leafHashing.scheme 1
      (jointAnswers (Function.update answers (.hash call) answer))
      (beforeFirstKey (.inr call) (jointKeys (tableQueryLog game
        (Function.update answers (.hash call) answer)))) ↔ _
    have prefixSame : beforeFirstKey (.inr call) (jointKeys (tableQueryLog game
        (Function.update answers (.hash call) answer))) = before := by
      change beforeFirstKey (jointKey (.hash call)) _ = beforeFirstKey (jointKey (.hash call)) _
      rw [← jointKeys_beforeFirst_hash, ← jointKeys_beforeFirst_hash,
        ZkcSecurity.Commitment.beforeFirst_update]
    rw [prefixSame, Function.update_self, jointAnswers_update,
      targets_update_inr leafHashing.scheme 1 (jointAnswers answers) call answer before
        (not_mem_beforeFirstKey (.inr call) _)]
  have length : (targets leafHashing.scheme 1 (jointAnswers answers) before).length ≤
      targetBound := by
    refine le_trans ?_ (bounded answers)
    have split := List.takeWhile_append_dropWhile (p := fun other =>
      decide (other ≠ (.inr call : JointKey (Event Context Scheme (List Coordinate) Digest) ℕ
        Digest (HashCall (List Coordinate) Digest))))
      (l := jointKeys (tableQueryLog game answers))
    conv_rhs => rw [← split]
    rw [targets_append, List.length_append]
    exact Nat.le_add_right _ _
  calc _ = Pr{let answer ← $ᵗ Digest}[
          answer ∈ targets leafHashing.scheme 1 (jointAnswers answers) before] :=
        prEvent_congr _ _ _ fun answer => fixed answer
    _ ≤ ((targets leafHashing.scheme 1 (jointAnswers answers) before).length : ENNReal) /
          Fintype.card Digest := prEvent_mem_le _
    _ ≤ (targetBound : ENNReal) / Fintype.card Digest :=
        ENNReal.div_le_div_right (by exact_mod_cast length) _

end Bad

/-! ### The trace and the bound -/

section Bound
variable [DecidableEq Context] [DecidableEq Scheme] [DecidableEq Coordinate] [DecidableEq Digest]

omit [DecidableEq Context] [DecidableEq Scheme] [DecidableEq Coordinate] [DecidableEq Digest] in
theorem hashRecord_mono {first second : Record Context Scheme (List Coordinate) Digest}
    (included : ∀ entry ∈ first, entry ∈ second) :
    ∀ entry ∈ hashRecord first, entry ∈ hashRecord second := by
  intro entry member
  unfold hashRecord at member ⊢
  rw [List.mem_filterMap] at member ⊢
  obtain ⟨recorded, recordedMember, found⟩ := member
  exact ⟨recorded, included _ recordedMember, found⟩

omit [DecidableEq Context] [DecidableEq Scheme] [DecidableEq Coordinate] [DecidableEq Digest] in
theorem mem_hashRecord {record : Record Context Scheme (List Coordinate) Digest}
    {call : HashCall (List Coordinate) Digest} {answer : Digest}
    (member : (⟨.hash call, answer⟩ : (query : Query Context Scheme (List Coordinate) Digest) ×
      Range query) ∈ record) :
    (⟨call, answer⟩ : (_ : HashCall (List Coordinate) Digest) × Digest) ∈ hashRecord record := by
  unfold hashRecord
  rw [List.mem_filterMap]
  exact ⟨_, member, rfl⟩

/-- The logged run in the lazily sampled joint oracle is the random-oracle run of the logged
experiment. -/
theorem loggedRun_eq [SampleableType Digest] {α : Type}
    (computation : OracleComp (spec Context Scheme (List Coordinate) Digest) α) :
    loggedRun computation = (simulateQ randomOracle computation.withQueryLog).run' ∅ := by
  unfold loggedRun
  rw [run_simulateQ_withLogging]

/-- An accepting run whose frozen table is far queries a bad key. -/
theorem trace (accepts : Scheme → List Coordinate → Bool) (absorbOpening : Bool) (context : Context)
    (configuration : Configuration Scheme) (fraction : ENNReal)
    (adversary : OracleComp (spec Context Scheme (List Coordinate) Digest)
      (List (Message (List Coordinate) Digest)))
    (answers : (query : Query Context Scheme (List Coordinate) Digest) → Range query)
    (event : AcceptsFar accepts extractor context configuration fraction
      (evalWithAnswerFn (QueryImpl.ofFn answers)
        (experiment accepts absorbOpening context configuration adversary).withQueryLog)) :
    ∃ entry ∈ tableQueryLog
        (experiment accepts absorbOpening context configuration adversary).withQueryLog answers,
      Bad accepts context configuration fraction
        (experiment accepts absorbOpening context configuration adversary) entry.1 answers := by
  rw [evalWithAnswerFn_withQueryLog, evalWithAnswerFn_experiment] at event
  rw [tableQueryLog_withQueryLog]
  set game := experiment accepts absorbOpening context configuration adversary
  set full := tableQueryLog game answers
  obtain ⟨accepted, key, keyOf, far⟩ := event
  obtain ⟨rootValue, row, siblings, rest, shape, width, depthLength, climbed, rowAccepted⟩ :=
    accepted_shape accepts absorbOpening context configuration answers _ accepted
  rw [shape] at keyOf
  simp only [proofKey, Option.some.injEq] at keyOf
  subst keyOf
  set index := decodeIndex configuration.depth
    (answers (.transcript (verifierKey context configuration rootValue)))
  set leafLabel := answers (.hash (HashCall.leaf row))
  have fullLog : full = tableQueryLog adversary answers ++
      (⟨.transcript (verifierKey context configuration rootValue),
        answers (.transcript (verifierKey context configuration rootValue))⟩ ::
        ⟨.hash (.leaf row), leafLabel⟩ :: climbEntries answers index.val siblings leafLabel) := by
    change tableQueryLog game answers = _
    rw [tableQueryLog_experiment, shape, tableQueryLog_verifier]
    simp only [width, depthLength, and_self, ↓reduceIte]
    rfl
  have keyEntry : (⟨.transcript (verifierKey context configuration rootValue),
      answers (.transcript (verifierKey context configuration rootValue))⟩ :
      (query : Query Context Scheme (List Coordinate) Digest) × Range query) ∈ full := by
    rw [fullLog]
    exact List.mem_append_right _ List.mem_cons_self
  have leafEntry : (⟨.hash (.leaf row), leafLabel⟩ :
      (query : Query Context Scheme (List Coordinate) Digest) × Range query) ∈ full := by
    rw [fullLog]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have climbIn : ∀ entry ∈ climbEntries answers index.val siblings leafLabel, entry ∈ full := by
    intro entry member
    rw [fullLog]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))
  -- A bad hash call in the record finishes the proof.
  by_cases someBad : ∃ call, (.inr call : JointKey (Event Context Scheme (List Coordinate) Digest) ℕ
      Digest (HashCall (List Coordinate) Digest)) ∈ jointKeys full ∧
      Bad accepts context configuration fraction game (.hash call) answers
  · obtain ⟨call, member, bad⟩ := someBad
    obtain ⟨entry, entryMember, keyed⟩ := List.mem_map.mp member
    have same : entry.1 = .hash call := jointKey_injective keyed
    exact ⟨entry, entryMember, by rw [same]; exact bad⟩
  have good : GoodFrom leafHashing.scheme 1 (jointAnswers answers) [] (jointKeys full) :=
    good_of_forall_not_bad leafHashing.scheme 1 (jointAnswers answers) [] (jointKeys full)
      fun call member _ hit => someBad ⟨call, member, by
        simp only [List.nil_append] at hit
        exact hit⟩
  have consistent : ∀ entry ∈ full, entry = ⟨entry.1, answers entry.1⟩ :=
    tableQueryLog_consistent answers game
  have hashFull : hashLog (jointAnswers answers) (jointKeys full) = hashRecord full :=
    hashLog_jointKeys answers full consistent
  have injective : MerkleTreeExtractor.ResponseInjectiveOn (hashRecord full) := by
    rw [← hashFull]
    simpa using responseInjective_of_good leafHashing.scheme 1 (jointAnswers answers) []
      (jointKeys full) (fun _ member => by simp at member) good
  -- The authenticated row is the row extracted from the whole record.
  have climbs : LeafHashing.Climbs leafHashing (hashRecord full) index.val siblings leafLabel
      rootValue := by
    have recorded := climbs_climbEntries answers index.val siblings leafLabel
    rw [show climb (hashOf answers) index.val siblings leafLabel = rootValue from climbed] at recorded
    exact LeafHashing.climbs_mono leafHashing (hashRecord_mono climbIn) _ _ _ _ recorded
  have label := LeafHashing.extractLabel_of_climbs leafHashing injective configuration.depth
    index.val siblings leafLabel rootValue depthLength index.isLt climbs
  have rowFound := LeafHashing.findRow_of_mem leafHashing injective (mem_hashRecord leafEntry)
    (leafHashing.leafRow_leaf row)
  have fullRow : leafHashing.extract (hashRecord full) configuration.depth rootValue index.val =
      some row := by
    simp only [LeafHashing.extract, index.isLt, ↓reduceIte, label, Option.bind_some, rowFound]
  -- The frozen table agrees with it.
  have stable : leafHashing.extract (hashRecord (CommittedOpening.beforeFirst
      (verifierKey context configuration rootValue) full)) configuration.depth rootValue =
      leafHashing.extract (hashRecord full) configuration.depth rootValue := by
    rw [← hashLog_jointKeys answers (CommittedOpening.beforeFirst
        (verifierKey context configuration rootValue) full) (fun entry member => consistent entry
        ((List.takeWhile_prefix _).subset member)), jointKeys_beforeFirst, ← hashFull]
    exact extract_checkpoint_eq leafHashing.scheme 1 (jointAnswers answers) (jointKeys full) good
      ((verifierKey context configuration rootValue).map absorbedOf, .position 0)
      (by unfold jointKeys; exact List.mem_map_of_mem (f := fun entry => jointKey entry.1) keyEntry)
      configuration.depth
      (List.mem_singleton_self rootValue)
  change Far accepts configuration fraction
    (frozen extractor configuration (verifierKey context configuration rootValue) full) at far
  refine ⟨_, keyEntry, ⟨rootValue, rfl⟩, _, rfl, far, ?_⟩
  change accepts configuration.scheme
    ((leafHashing.extract (hashRecord (CommittedOpening.beforeFirst
      (verifierKey context configuration rootValue) full)) configuration.depth rootValue
      index.val).getD []) = true
  rw [stable, fullRow]
  exact rowAccepted

/-- The intended bound of the committed-opening experiment holds for the straight-line extractor,
with factor `1`, extraction term `(q_M + k + 1) · 4 (q_T + q_M + k + 2) / |Digest|` and namespace
term `0`, whether the terminal opening is absorbed or omitted. -/
theorem intendedBound [SampleableType Digest] [Fintype Digest]
    (accepts : Scheme → List Coordinate → Bool) (absorbOpening : Bool) (context : Context)
    (configuration : Configuration Scheme) (fraction : ENNReal) (transcriptCalls merkleCalls : ℕ) :
    IntendedBound accepts absorbOpening (extractor (Context := Context) (Scheme := Scheme)
      (Coordinate := Coordinate) (Digest := Digest)) context configuration fraction 1
      (((merkleCalls + configuration.depth + 1 : ℕ) : ENNReal) *
        (((4 * (transcriptCalls + merkleCalls + configuration.depth + 2) : ℕ) : ENNReal) /
          Fintype.card Digest))
      0 transcriptCalls merkleCalls := by
  intro adversary budgets
  set game := experiment accepts absorbOpening context configuration adversary
  set hashError : ENNReal :=
    (((4 * (transcriptCalls + merkleCalls + configuration.depth + 2) : ℕ) : ENNReal) /
      Fintype.card Digest)
  let weight : Family → ENNReal := fun
    | .transcript => 1 - fraction
    | .merkle => hashError
  have gameCost : WorstCaseCostBound game.withQueryLog ⟨fun query => weight (familyOf query)⟩
      ((transcriptCalls * weight .transcript + merkleCalls * weight .merkle) +
        (((1 : ℕ) : ENNReal) * weight .transcript +
          ((configuration.depth + 1 : ℕ) : ENNReal) * weight .merkle)) := by
    refine (worstCaseCostBound_withQueryLog _ _ _).mpr (WorstCaseCostBound.bind
      (familyQueryBound_costBound weight adversary _ budgets) fun proof => ?_)
    have bound := familyQueryBound_costBound weight _ _
      (verifier_familyQueryBound accepts absorbOpening context configuration proof)
    dsimp only at bound
    exact (worstCaseCostBound_map_iff _ _ _ _).mpr bound
  have gameCount : IsTotalQueryBound game
      ((transcriptCalls + merkleCalls) + (1 + (configuration.depth + 1))) :=
    isTotalQueryBound_bind (familyQueryBound_total adversary _ budgets) fun proof =>
      (isQueryBound_map_iff _ _ _ _ _).mpr (familyQueryBound_total _ _
        (verifier_familyQueryBound accepts absorbOpening context configuration proof))
  have targetsBounded : ∀ answers : (query : Query Context Scheme (List Coordinate) Digest) →
      Range query, (targets leafHashing.scheme 1 (jointAnswers answers)
        (jointKeys (tableQueryLog game answers))).length ≤
        4 * (transcriptCalls + merkleCalls + configuration.depth + 2) := by
    intro answers
    refine (targets_length_le (leafHashing (Coordinate := Coordinate) (Digest := Digest)).scheme 1 2
      (LeafHashing.inputs_length (leafHashing (Coordinate := Coordinate) (Digest := Digest))) _
      _).trans ?_
    have length := tableQueryLog_length_le answers game _ gameCount
    simp only [jointKeys, List.length_map]
    omega
  rw [loggedRun_eq]
  refine (prEvent_randomOracle_le_of_bad_queries_weighted game.withQueryLog
    (fun query => weight (familyOf query)) _ gameCost
    (AcceptsFar accepts extractor context configuration fraction)
    (fun query answers => Bad accepts context configuration fraction game query answers)
    ?_ ?_).trans ?_
  · intro query answers
    cases query with
    | transcript key =>
        exact bad_transcript_resample accepts context configuration fraction game key answers
    | hash call =>
        exact bad_hash_resample accepts context configuration fraction game _ targetsBounded call
          answers
  · intro answers event
    rw [tableQueryLog_withQueryLog]
    have := trace accepts absorbOpening context configuration fraction adversary answers event
    rwa [tableQueryLog_withQueryLog] at this
  · simp only [weight, hashError]
    push_cast
    ring_nf
    exact le_rfl

end Bound

end ZkcSecurity.Examples.CommittedOpening
