module

public import ZkcArkLibExamples.FriFiatShamir
public import ZkcSecurity.Transformations.Commitment.Soundness
public import ZkcSecurity.Transformations.Commitment.HashedLeaves
public import ZkcSecurity.Transformations.Commitment.Cost

@[expose] public section

/-! # `fri::LowDegree` with committed words

`ZkcSecurity.Examples.FriFiatShamir` bounds the Fiat–Shamir transform of `fri::LowDegree` with
every committed word read in the clear. This module states the verifier that sees only the roots
of the committed words and authenticated openings of the entries it reads, and applies
`ZkcSecurity.Commitment.soundness` to it.

* **Verifier** (`verifier`). After the folding challenge of each round but the last, the verifier
  receives the commitment of the next word, of shape `(round, logSize)`; the initial word is the
  statement's commitment. After the final coefficients and the query block, each query reads the
  two entries of the pair it needs from the committed word of each round (`walkReads`), in the
  order of the source's checks.
* **Ideal reading** (`withTables_verifier`). Reading every committed word in the clear, the
  verifier is the verifier of `FriFiatShamir` after the initial word: `withTables words
  [tableOf (N + 1) word] (verifier N K) = afterCommit word`. The two steps are a pure lemma, that
  the reads of a query answered from the tables of a committed transcript decide as `walk` on the
  transcript (`withTables_walkReads`, `withTables_queryReads`), and the process equality of the
  commit phase (`withTables_foldPhaseReads`), whose invariant states that the tables received so
  far, and every later table, are the words of the transcript the commit phase completes.
* **Commitments.** Words are committed with Merkle trees with hashed leaves, one field element per
  leaf (a row of width one) and depth `logSize` (`scheme`), as the installed binary Merkle schemes
  hash every row before compression. An authentication makes at most `logSize + 1 ≤ N + 2` hash
  calls. The ideal reading receives an extracted table as the word with zero at every entry the
  extraction misses (`wordOf`), and the statement is false when that initial word is far
  (`FarStatement`).
* **Bound** (`soundness`). The typed certificate is `FriFiatShamir.typedCertificate`, whose doomed
  set holds the verifier after a far initial word under the folding proximity premise, which stays
  a hypothesis as in `FriFiatShamir.fiatShamir_soundness`. The verifier commits at most `K` words
  besides the statement's (`verifier_commitBound`), and charges every folding error, the query
  block's error and `2 s (K + 1)` reads of at most `N + 2` hash calls each (`verifier_costBound`,
  `verifier_queryBound`). The verifier accepts while the initial word extracted at the checkpoint
  of one of its transcript queries is at relative distance at least `δ` with probability at most
  the prover's charge plus the folding errors, the query block's error and
  `2 s (K + 1) (N + 2) · hashError`, with
  `hashError = (K + 4) (proverQueries + K + 2 + 2 s (K + 1) (N + 2)) / |Digest|`.
-/

set_option autoImplicit false

namespace ZkcSecurity.Examples.CommittedFri

open OracleComp OracleSpec Domain
open ZkcSecurity.ArkLib.Fri ZkcSecurity.FiatShamir ZkcSecurity.Commitment
open ZkcSecurity.Examples.FriFiatShamir (Block Event Raw absorb eventError typedCertificate)

variable {F : Type}

/-- Shapes of committed words: the round and the logarithm of the size. -/
abbrev Shape := ℕ × ℕ

/-- The table of a word of size `2 ^ logSize`: its entries, none beyond the word. -/
def tableOf (logSize : ℕ) (word : Fin (2 ^ logSize) → F) : Table F := fun position =>
  if below : position < 2 ^ logSize then some (word ⟨position, below⟩) else none

/-- The word of size `2 ^ logSize` a table describes, with zero where the table has no entry. -/
def wordOf [Zero F] (logSize : ℕ) (table : Table F) : Fin (2 ^ logSize) → F :=
  fun index => (table index.val).getD 0

/-- The ideal reading receives the committed word of shape `(round, logSize)` through the word
operation of that round and size. -/
def words [Zero F] : Words (operations F) Shape F where
  word shape := .word shape.1 shape.2
  toTable shape received := tableOf shape.2 received
  ofTable shape table := wordOf shape.2 table

/-- The signature of the verifier with committed words. -/
abbrev signature (F : Type) := committed (operations F) Shape F

/-- The folding challenges of a committed transcript, outermost round first. -/
def challenges : {m R : ℕ} → Layers F m R → List F
  | _, _, .final _ => []
  | _, _, .fold _ beta rest => beta :: challenges rest

/-- The tables from `handle` on are the words of `layers`, in order. -/
def Matches (tables : List (Table F)) : ℕ → {m R : ℕ} → Layers F m R → Prop
  | _, _, _, .final _ => True
  | handle, m + 1, _, .fold word _ rest =>
      tables[handle]? = some (tableOf (m + 1) word) ∧ Matches tables (handle + 1) rest

section Verifier
variable [Field F] [DecidableEq F] (roots : ℕ → F)

/-- One query's checks with committed words (`walk`), from the word committed at `handle`, of size
`2 ^ m`, at `position` with coset shift `current`: at a folding round it reads both entries of the
pair, checks the chain and moves to the halved word; at the end it checks the final polynomial.
The continuation receives the decision. -/
def walkReads (coefficients : List F) : List F → ℕ → ℕ → F → ℕ → F → ℕ →
    (Bool → PIR.Process (signature F) Bool) → PIR.Process (signature F) Bool
  | [], _, m, current, position, expected, _, onDecision =>
      onDecision (decide (terminal roots coefficients current m position = expected))
  | beta :: rest, handle, m + 1, current, position, expected, round, onDecision =>
      .call (.read handle (position % 2 ^ m)) fun lowValue =>
        .call (.read handle (position % 2 ^ m + 2 ^ m)) fun highValue =>
          if chain round (selectHalf lowValue highValue position (2 ^ m)) expected then
            walkReads coefficients rest (handle + 1) m (current * current) (position % 2 ^ m)
              (foldedValue roots lowValue highValue current (m + 1) (position % 2 ^ m) beta)
              (round + 1) onDecision
          else onDecision false
  | _ :: _, _, 0, _, _, _, _, onDecision => onDecision false

variable (t : ℕ) (shift : F) (s : ℕ)

/-- Every query's checks in order, from the initial word of size `2 ^ n`, rejecting at the first
failed query. -/
def queryReads (coefficients foldingChallenges : List F) (n : ℕ)
    (positions : Fin s → Fin (2 ^ n)) : List (Fin s) → PIR.Process (signature F) Bool
  | [] => .done true
  | query :: rest =>
      walkReads roots coefficients foldingChallenges 0 n shift (positions query).val 0 0
        fun accepted => if accepted then queryReads coefficients foldingChallenges n positions rest
          else .done false

/-- After the last folding challenge: the final coefficients, their bound, the query block and the
queries' reads. -/
def finalPhaseReads (n : ℕ) (foldingChallenges : List F) : PIR.Process (signature F) Bool :=
  .call (.base .final) fun coefficients =>
    if bounded t coefficients then
      .call (.base (.positions n s)) fun positions =>
        queryReads roots shift s coefficients foldingChallenges n positions (List.finRange s)
    else .halt .reject

/-- The commit phase from the word committed at round `round`, of size `2 ^ (m + 1)` with
`R + 1` folds left: the folding challenge, then the commitment of the next word, or the final
phase after the last fold. -/
def foldPhaseReads (n : ℕ) : (m R : ℕ) → ℕ → List F → PIR.Process (signature F) Bool
  | _, 0, round, foldingChallenges => .call (.base (.fold round)) fun beta =>
      finalPhaseReads roots t shift s n (foldingChallenges ++ ([beta] : List F))
  | m + 1, R + 1, round, foldingChallenges => .call (.base (.fold round)) fun beta =>
      .call (.commit (round + 1, m + 1)) fun _ =>
        foldPhaseReads n m R (round + 1) (foldingChallenges ++ ([beta] : List F))
  | 0, _ + 1, round, _ => .call (.base (.fold round)) fun _ => .halt .refused

/-- The verifier with committed words, for an initial word of size `2 ^ (N + 1)` and `K + 1`
folds. The initial word is the statement's commitment, with handle `0`. -/
def verifier (N K : ℕ) : PIR.Process (signature F) Bool :=
  foldPhaseReads roots t shift s (N + 1) N K 0 []

end Verifier

/-! ## The ideal reading -/

section Ideal
variable [Field F] [DecidableEq F] (roots : ℕ → F)

omit [Field F] [DecidableEq F] in
theorem lookup_tableOf {tables : List (Table F)} {handle logSize : ℕ}
    {word : Fin (2 ^ logSize) → F} (found : tables[handle]? = some (tableOf logSize word))
    (index : Fin (2 ^ logSize)) : lookup tables handle index.val = some (word index) := by
  simp [lookup, found, tableOf, index.isLt]

/-- The reads of one query, answered from the tables of a committed transcript, decide as the
query's checks on the transcript. -/
theorem withTables_walkReads (tables : List (Table F)) :
    ∀ {m R : ℕ} (layers : Layers F m R) (handle : ℕ) (current : F) (position : Fin (2 ^ m))
      (expected : F) (round : ℕ) (onDecision : Bool → PIR.Process (signature F) Bool),
      Matches tables handle layers →
      withTables words tables (walkReads roots layers.coefficients (challenges layers) handle m
          current position.val expected round onDecision) =
        withTables words tables (onDecision (walk roots layers current position expected round))
  | _, _, .final coefficients, handle, current, position, expected, round, onDecision, _ => by
      simp only [challenges, Layers.coefficients, walkReads, walk]
  | m + 1, _, .fold word beta rest, handle, current, position, expected, round, onDecision,
      matched => by
      obtain ⟨found, later⟩ := matched
      have lowFound : lookup tables handle (position.val % 2 ^ m) =
          some (word (lowIndex (lowHalf position))) :=
        lookup_tableOf found (lowIndex (lowHalf position))
      have highFound : lookup tables handle (position.val % 2 ^ m + 2 ^ m) =
          some (word (highIndex (lowHalf position))) :=
        lookup_tableOf found (highIndex (lowHalf position))
      simp only [challenges, Layers.coefficients, walkReads]
      rw [withTables, lowFound]
      simp only
      rw [withTables, highFound]
      simp only [walk]
      split
      · rename_i passed
        rw [passed, Bool.true_and]
        exact withTables_walkReads tables rest (handle + 1) (current * current)
          (lowHalf position) _ (round + 1) onDecision later
      · rename_i failed
        rw [Bool.not_eq_true] at failed
        rw [failed, Bool.false_and]

variable (shift : F) (s : ℕ)

/-- The reads of every query, answered from the tables of a committed transcript, decide as the
queries' checks on the transcript. -/
theorem withTables_queryReads (tables : List (Table F)) {n R : ℕ} (layers : Layers F n R)
    (matched : Matches tables 0 layers) (positions : Fin s → Fin (2 ^ n)) :
    ∀ queries : List (Fin s),
      withTables words tables (queryReads roots shift s layers.coefficients (challenges layers) n
          positions queries) =
        .done (queries.all fun query => walk roots layers shift (positions query) 0 0)
  | [] => by simp only [queryReads, withTables, List.all_nil]
  | query :: rest => by
      simp only [queryReads, List.all_cons]
      rw [withTables_walkReads roots tables layers 0 shift (positions query) 0 0 _ matched]
      cases walk roots layers shift (positions query) 0 0
      · simp only [Bool.false_eq_true, ↓reduceIte, withTables, Bool.false_and]
      · simp only [↓reduceIte, Bool.true_and]
        exact withTables_queryReads tables layers matched positions rest

omit [DecidableEq F] in
theorem withTables_base (tables : List (Table F)) (operation : Operation)
    (next : (signature F).Reply (.base operation) → PIR.Process (signature F) Bool) :
    withTables words tables (.call (.base operation) next) =
      .call operation fun reply => withTables words tables (next reply) := rfl

omit [DecidableEq F] in
theorem withTables_commit (tables : List (Table F)) (shape : Shape)
    (next : (signature F).Reply (.commit shape) → PIR.Process (signature F) Bool) :
    withTables words tables (.call (.commit shape) next) =
      .call (.word shape.1 shape.2) fun received =>
        withTables words (tables ++ [tableOf shape.2 received]) (next ()) := rfl

omit [DecidableEq F] in
theorem withTables_halt (tables : List (Table F)) (stop : PIR.Stop) :
    withTables words tables (.halt stop : PIR.Process (signature F) Bool) = .halt stop := rfl

variable (t : ℕ)

/-- The commit phase with committed words, read with every word in the clear, is the commit phase
of the ideal verifier. The tables received so far end with the current word, and every
completion of the commit phase is a transcript whose words are the tables, in order. -/
theorem withTables_foldPhaseReads {N K : ℕ} :
    ∀ {m R : ℕ} (round : ℕ) (wrap : Layers F (m + 1) (R + 1) → Layers F (N + 1) (K + 1))
      (word : Fin (2 ^ (m + 1)) → F) (tables : List (Table F)) (foldingChallenges : List F),
      tables.length = round + 1 →
      (∀ beta (rest : Layers F m R) (later : List (Table F)),
        Matches (tables ++ later) (round + 1) rest →
          Matches (tables ++ later) 0 (wrap (.fold word beta rest)) ∧
          challenges (wrap (.fold word beta rest)) = foldingChallenges ++ beta :: challenges rest ∧
          (wrap (.fold word beta rest)).coefficients = rest.coefficients) →
      withTables words tables (foldPhaseReads roots t shift s (N + 1) m R round foldingChallenges) =
        foldPhase roots t shift s round wrap word
  | m, 0, round, wrap, word, tables, foldingChallenges, _, completes => by
      rw [foldPhase_last, foldPhaseReads, withTables_base]
      refine congrArg (@PIR.Process.call (operations F) Bool (Operation.fold round))
        (funext fun (beta : F) => ?_)
      rw [finalPhaseReads, withTables_base, finalPhase]
      refine congrArg (@PIR.Process.call (operations F) Bool Operation.final)
        (funext fun (coefficients : List F) => ?_)
      obtain ⟨matched, completed, final⟩ := completes beta (.final coefficients) [] (by simp [Matches])
      rw [List.append_nil] at matched
      by_cases withinBound : bounded t coefficients = true
      · simp only [withinBound, ↓reduceIte]
        rw [withTables_base, queryPhase]
        refine congrArg (@PIR.Process.call (operations F) Bool (Operation.positions (N + 1) s))
          (funext fun (positions : Fin s → Fin (2 ^ (N + 1))) => ?_)
        have read := withTables_queryReads roots shift s tables
          (wrap (.fold word beta (.final coefficients))) matched positions (List.finRange s)
        rw [completed, final] at read
        simp only [challenges, Layers.coefficients] at read
        rw [read, verify, final]
        simp [Layers.coefficients, withinBound]
      · simp only [withinBound, Bool.false_eq_true, ↓reduceIte]
        rfl
  | m + 1, R + 1, round, wrap, word, tables, foldingChallenges, length, completes => by
      rw [foldPhase_next, foldPhaseReads, withTables_base]
      refine congrArg (@PIR.Process.call (operations F) Bool (Operation.fold round))
        (funext fun (beta : F) => ?_)
      rw [withTables_commit]
      refine congrArg (@PIR.Process.call (operations F) Bool (Operation.word (round + 1) (m + 1)))
        (funext fun (next : Fin (2 ^ (m + 1)) → F) => ?_)
      refine withTables_foldPhaseReads (round + 1) (fun rest => wrap (.fold word beta rest)) next
        (tables ++ [tableOf (m + 1) next]) (foldingChallenges ++ [beta])
        (by simp [length]) fun beta' rest later restMatches => ?_
      have earlier := completes beta (.fold next beta' rest) ([tableOf (m + 1) next] ++ later)
        ⟨by simp [length],
          by simpa only [List.append_assoc] using restMatches⟩
      simp only [List.append_assoc] at earlier ⊢
      refine ⟨earlier.1, ?_, earlier.2.2⟩
      rw [earlier.2.1]
      simp [challenges]
  | 0, R + 1, round, wrap, word, tables, foldingChallenges, _, _ => by
      rw [foldPhase_exhausted, foldPhaseReads, withTables_base]
      rfl

/-- Reading every committed word in the clear, the verifier with committed words is the ideal
verifier after the initial word. -/
theorem withTables_verifier {N K : ℕ} (word : Fin (2 ^ (N + 1)) → F) :
    withTables words [tableOf (N + 1) word] (verifier roots t shift s N K) =
      afterCommit (R := K) roots t shift s word :=
  withTables_foldPhaseReads roots shift s t 0 id word [tableOf (N + 1) word] [] rfl
    fun _ _ _ restMatches => ⟨⟨rfl, restMatches⟩, rfl, rfl⟩

end Ideal

/-! ## Commitments and charges -/

/-- The admissible shapes: words of size at most `2 ^ n`. -/
def Admissible (n : ℕ) (shape : Shape) : Prop := shape.2 ≤ n

section Charges
variable [Field F] [DecidableEq F] (roots : ℕ → F) (t : ℕ) (shift : F) (s : ℕ)

theorem walkReads_commitBound (coefficients : List F) (budget : ℕ) :
    ∀ (foldingChallenges : List F) (handle m : ℕ) (current : F) (position : ℕ) (expected : F)
      (round : ℕ) (onDecision : Bool → PIR.Process (signature F) Bool),
      (∀ accepted, CommitBound (onDecision accepted) budget) →
      CommitBound (walkReads roots coefficients foldingChallenges handle m current position
        expected round onDecision) budget
  | [], _, _, _, _, _, _, _, after => after _
  | _ :: _, _, 0, _, _, _, _, _, after => after _
  | _ :: rest, _, _ + 1, _, _, _, _, _, after => fun _ _ => by
      dsimp only
      split
      · exact walkReads_commitBound coefficients budget rest _ _ _ _ _ _ _ after
      · exact after _

theorem queryReads_commitBound (coefficients foldingChallenges : List F) (n : ℕ)
    (positions : Fin s → Fin (2 ^ n)) (budget : ℕ) :
    ∀ queries : List (Fin s),
      CommitBound (queryReads roots shift s coefficients foldingChallenges n positions queries)
        budget
  | [] => trivial
  | _ :: rest => walkReads_commitBound roots coefficients budget _ _ _ _ _ _ _ _ fun accepted => by
      cases accepted
      · trivial
      · exact queryReads_commitBound coefficients foldingChallenges n positions budget rest

/-- The commit phase commits at most one word per remaining fold but the last. -/
theorem foldPhaseReads_commitBound (n : ℕ) :
    ∀ (m R round : ℕ) (foldingChallenges : List F),
      CommitBound (foldPhaseReads roots t shift s n m R round foldingChallenges) R
  | _, 0, _, _ => by
      rw [foldPhaseReads]
      intro _ coefficients
      show CommitBound (if bounded t coefficients then _ else _) _
      split
      · exact fun _ => queryReads_commitBound roots shift s _ _ _ _ _ _
      · trivial
  | m + 1, R + 1, round, foldingChallenges => by
      rw [foldPhaseReads]
      exact fun _ => ⟨by omega, foldPhaseReads_commitBound n m R (round + 1) _⟩
  | 0, _ + 1, _, _ => by
      rw [foldPhaseReads]
      exact fun _ => trivial

theorem verifier_commitBound (N K : ℕ) : CommitBound (verifier roots t shift s N K) K :=
  foldPhaseReads_commitBound roots t shift s (N + 1) N K 0 []

variable {ω : Type} [AddCommMonoid ω] [PartialOrder ω] [CanonicallyOrderedAdd ω]
variable {b : ℕ} (block : Block b s) (charge : Event F → ω) (readCharge : ω) (n : ℕ)

theorem walkReads_charged (coefficients : List F) (budget : ω) :
    ∀ (foldingChallenges : List F) (handle m : ℕ) (current : F) (position : ℕ) (expected : F)
      (round : ℕ) (onDecision : Bool → PIR.Process (signature F) Bool),
      (∀ accepted, Charged (absorb block) (Admissible n) charge readCharge (onDecision accepted)
        budget) →
      Charged (absorb block) (Admissible n) charge readCharge
        (walkReads roots coefficients foldingChallenges handle m current position expected round
          onDecision)
        (foldingChallenges.length • (readCharge + readCharge) + budget)
  | [], _, _, _, _, _, _, _, after => by
      simp only [walkReads, List.length_nil, zero_nsmul, zero_add]
      exact after _
  | _ :: _, _, 0, _, _, _, _, _, after =>
      Charged.mono _ _ _ _ _ (after _) le_add_self
  | _ :: rest, _, _ + 1, _, _, _, _, _, after => by
      refine ⟨readCharge + (rest.length • (readCharge + readCharge) + budget), ?_, fun _ =>
        ⟨rest.length • (readCharge + readCharge) + budget, le_rfl, fun _ => ?_⟩⟩
      · rw [List.length_cons, succ_nsmul]
        exact le_of_eq (by abel_nf)
      · dsimp only
        split
        · exact walkReads_charged coefficients budget rest _ _ _ _ _ _ _ after
        · exact Charged.mono _ _ _ _ _ (after _) le_add_self

theorem queryReads_charged (coefficients foldingChallenges : List F) (logSize : ℕ)
    (positions : Fin s → Fin (2 ^ logSize)) :
    ∀ queries : List (Fin s),
      Charged (absorb block) (Admissible n) charge readCharge
        (queryReads roots shift s coefficients foldingChallenges logSize positions queries)
        (queries.length • (foldingChallenges.length • (readCharge + readCharge)))
  | [] => trivial
  | _ :: rest => by
      rw [List.length_cons, succ_nsmul']
      exact walkReads_charged roots s block charge readCharge n coefficients _ _ _ _ _ _ _ _ _
        fun accepted => by
          cases accepted
          · trivial
          · exact queryReads_charged coefficients foldingChallenges logSize positions rest

/-- The commit phase charges every remaining folding challenge, the query block, and two reads
per round for every query. -/
theorem foldPhaseReads_charged (total : ℕ) :
    ∀ (m R round : ℕ) (foldingChallenges : List F), m + 1 ≤ n →
      foldingChallenges.length + R + 1 = total →
      Charged (absorb block) (Admissible n) charge readCharge
        (foldPhaseReads roots t shift s n m R round foldingChallenges)
        ((∑ later ∈ Finset.range (R + 1), charge (.fold (round + later))) +
          charge (.positions n s) + s • (total • (readCharge + readCharge)))
  | _, 0, round, foldingChallenges, _, length => by
      rw [foldPhaseReads]
      refine ⟨charge (.positions n s) + s • (total • (readCharge + readCharge)), ?_,
        fun (beta : F) (coefficients : List F) => ?_⟩
      · simp [add_assoc]
      · show Charged _ _ _ _ (if bounded t coefficients then _ else _) _
        split
        · refine ⟨s • (total • (readCharge + readCharge)), le_rfl, fun positions => ?_⟩
          have charged := queryReads_charged roots shift s block charge readCharge n coefficients
            (foldingChallenges ++ [beta]) n positions (List.finRange s)
          rwa [List.length_finRange, List.length_append, List.length_singleton,
            show foldingChallenges.length + 1 = total by omega] at charged
        · trivial
  | m + 1, R + 1, round, foldingChallenges, size, length => by
      rw [foldPhaseReads]
      refine ⟨(∑ later ∈ Finset.range (R + 1), charge (.fold (round + 1 + later))) +
          charge (.positions n s) + s • (total • (readCharge + readCharge)), ?_, fun (beta : F) =>
        ⟨show m + 1 ≤ n by omega, ?_⟩⟩
      · rw [Finset.sum_range_succ' _ (R + 1)]
        refine le_of_eq ?_
        have shifted : ∑ later ∈ Finset.range (R + 1), charge (.fold (round + 1 + later)) =
            ∑ later ∈ Finset.range (R + 1), charge (.fold (round + (later + 1))) :=
          Finset.sum_congr rfl fun later _ => by rw [Nat.add_assoc, Nat.add_comm 1 later]
        rw [shifted, Nat.add_zero]
        abel_nf
      · exact foldPhaseReads_charged total m R (round + 1) (foldingChallenges ++ [beta])
          (by omega) (by rw [List.length_append, List.length_singleton]; omega)
  | 0, _ + 1, round, _, _, _ => by
      rw [foldPhaseReads]
      refine ⟨0, ?_, fun _ => trivial⟩
      rw [add_zero, Finset.sum_range_succ', Nat.add_zero, add_assoc]
      exact le_add_right le_add_self

/-- The verifier charges every folding challenge, the query block, and `2 s (K + 1)` reads. -/
theorem verifier_charged (N K : ℕ) :
    Charged (absorb block) (Admissible (N + 1)) charge readCharge (verifier roots t shift s N K)
      ((∑ round ∈ Finset.range (K + 1), charge (.fold round)) + charge (.positions (N + 1) s) +
        s • ((K + 1) • (readCharge + readCharge))) := by
  have charged := foldPhaseReads_charged roots t shift s block charge readCharge (N + 1) (K + 1)
    N K 0 [] le_rfl (by simp)
  unfold verifier
  simpa only [zero_add] using charged

end Charges

theorem nsmul_reads (s K N : ℕ) (hashError : ENNReal) :
    s • ((K + 1) • (((N + 2 : ℕ) : ENNReal) * hashError + ((N + 2 : ℕ) : ENNReal) * hashError)) =
      ((2 * s * (K + 1) * (N + 2) : ℕ) : ENNReal) * hashError := by
  rw [nsmul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

/-! ## The bound -/

section Bound
variable [Field F] [DecidableEq F] {Query Digest : Type} [DecidableEq Digest]

instance jointKeyDecidableEq [DecidableEq Query] :
    DecidableEq (JointKey (Event F) Shape Digest Query) := by
  haveI : DecidableEq (Event F) := inferInstance
  haveI : DecidableEq (Absorbed (Event F) Shape Digest) := inferInstance
  exact inferInstance

/-- Words committed with Merkle trees with hashed leaves, one field element per leaf, of depth the
word's logarithmic size. -/
def scheme (model : LeafHashing F Query Digest) : Extractable Shape F Query Digest :=
  model.scheme.comap Prod.snd

omit [DecidableEq F] in
theorem carries (model : LeafHashing F Query Digest) (log : HashLog Query Digest) (shape : Shape)
    (root : Digest) (position : ℕ) (value : F)
    (found : (scheme model).extract log shape root position = some value) :
    normalized words ((scheme model).extract log) shape root position = some value := by
  have below : position < 2 ^ shape.2 := by
    by_contra outside
    simp [scheme, Extractable.comap, LeafHashing.scheme, LeafHashing.extract, outside] at found
  simp [normalized, words, tableOf, wordOf, below, found]

/-- The statement's commitment: the root of the initial word, of shape `(0, N + 1)`. -/
def initial (N : ℕ) (root : Digest) : List (Absorbed (Event F) Shape Digest) :=
  [.root (0, N + 1) root]

/-- The statement's committed roots. -/
def statementRoots (N : ℕ) (root : Digest) : List (Shape × Digest) := [((0, N + 1), root)]

omit [Field F] [DecidableEq F] [DecidableEq Digest] in
theorem initial_determined (N : ℕ) : Typed.Determined (initial (F := F) (Digest := Digest) N) := by
  intro root other rest otherRest same
  simp only [initial, List.singleton_append, List.cons.injEq, Absorbed.root.injEq, true_and]
    at same
  exact same.1

/-- The statement is false when its initial word is at relative distance at least `δ` from the
code. -/
def FarStatement {N K : ℕ} (t : ℕ) (D : SmoothCosetFftDomain (N + 1) F) (δ : ℝ) (_root : Digest)
    (tables : List (Table F)) : Prop :=
  ∃ word, tables = [tableOf (N + 1) word] ∧ Far D (degreeBound (K + 1) (2 ^ t)) δ word

variable (model : LeafHashing F Query Digest)

omit [Field F] [DecidableEq F] in
theorem authenticate_queryBound (N : ℕ) (shape : Shape) (admissible : Admissible (N + 1) shape)
    (root : Digest) (position : ℕ) (opening : Opening F Digest) :
    IsTotalQueryBound ((scheme model).authenticate shape root position opening) (N + 2) :=
  (LeafHashing.authenticate_queryBound model shape.2 root position opening).mono
    (by unfold Admissible at admissible; omega)

variable (roots : ℕ → F) (t : ℕ) (shift : F) (s : ℕ)

theorem verifier_queryBound {N K : ℕ} (block : Block (N + 1) s) (root : Digest)
    (messages : List (Message (List F) Digest)) (openings : List (Opening F Digest)) :
    IsTotalQueryBound (run (absorb block) (scheme model) (verifier roots t shift s N K)
        (initial N root) (statementRoots N root) messages openings)
      (K + 1 + 1 + 2 * s * (K + 1) * (N + 2)) := by
  have charged := Charged.mono (absorb block) (Admissible (N + 1)) (fun _ => (1 : ℕ)) (N + 2) _
    (verifier_charged roots t shift s block (fun _ => (1 : ℕ)) (N + 2) N K)
    (le_of_eq (show _ = K + 1 + 1 + 2 * s * (K + 1) * (N + 2) by
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
      ring))
  exact run_queryBound (absorb block) (Admissible (N + 1)) (scheme model) (N + 2)
    (authenticate_queryBound model N) _ _ charged _ _ messages openings
    (fun pair member => by
      simp only [statementRoots, List.mem_singleton] at member
      subst member
      exact le_rfl)

theorem verifier_costBound {N K : ℕ} (block : Block (N + 1) s) (foldError : ℕ → ENNReal)
    (blockError hashError : ENNReal) (root : Digest) (messages : List (Message (List F) Digest))
    (openings : List (Opening F Digest)) :
    WorstCaseCostBound (run (absorb block) (scheme model) (verifier roots t shift s N K)
        (initial N root) (statementRoots N root) messages openings)
      ⟨(jointError (eventError foldError blockError) hashError :
        JointKey (Event F) Shape Digest Query → ENNReal)⟩
      ((∑ round ∈ Finset.range (K + 1), foldError round) + blockError +
        ((2 * s * (K + 1) * (N + 2) : ℕ) : ENNReal) * hashError) := by
  have charged := verifier_charged roots t shift s block (eventError foldError blockError)
    (((N + 2 : ℕ) : ENNReal) * hashError) N K
  rw [nsmul_reads] at charged
  exact run_costBound (absorb block) (Admissible (N + 1)) (scheme model)
    (eventError foldError blockError) hashError (N + 2) (authenticate_queryBound model N) _ _
    charged _ _ messages openings
    (fun pair member => by
      simp only [statementRoots, List.mem_singleton] at member
      subst member
      exact le_rfl)

/-- Soundness of `fri::LowDegree` with committed words: in the joint random-oracle experiment of
the transcript keys and the hash calls, the verifier accepts while the initial word extracted at
the checkpoint of one of its transcript queries is at relative distance at least `δ` with
probability at most the prover's charge plus every folding error, the query block's error and
`2 s (K + 1) (N + 2) · hashError`, from the folding proximity premise. -/
theorem soundness [SampleableType F] [Fintype F] [DecidableEq Query] [SampleableType Digest]
    [Fintype Digest] {N K : ℕ}
    (block : Block (N + 1) s) (D : SmoothCosetFftDomain (N + 1) F)
    (hD : ∀ i : Fin (2 ^ (N + 1)), D i = point roots shift (N + 1) i)
    (hcompat : Compatible roots (N + 1) (K + 1)) (θ δ : ℝ) (foldError : ℕ → ENNReal)
    (proximity : FoldingProximity t θ D (K + 1) foldError)
    (prover : OracleComp (joint (Raw F block) Shape Digest Query)
      (Digest × Proof (List F) F Digest))
    (proverQueries : ℕ) (proverCount : IsTotalQueryBound prover proverQueries)
    (proverCost : ENNReal)
    (proverBound : WorstCaseCostBound prover
      ⟨jointError (eventError foldError
          (block.factor * ENNReal.ofReal (1 - min θ δ) ^ s + block.slack))
        ((((K + 1 + 2 + 1) * (proverQueries + (K + 1 + 1 + 2 * s * (K + 1) * (N + 2))) : ℕ) :
          ENNReal) / Fintype.card Digest)⟩ proverCost) :
    Pr{let result ← (simulateQ randomOracle (ZkcSecurity.Commitment.experiment (absorb block)
        (scheme model) (fun _ => verifier roots t shift s N K) (initial N) (statementRoots N)
        prover)).run' ∅}[
      FalseAcceptance words (scheme model) (statementRoots N)
        (FarStatement (K := K) t D δ) (· = true) result] ≤
      proverCost + ((∑ round ∈ Finset.range (K + 1), foldError round) +
        (block.factor * ENNReal.ofReal (1 - min θ δ) ^ s + block.slack) +
        ((2 * s * (K + 1) * (N + 2) : ℕ) : ENNReal) *
          ((((K + 1 + 2 + 1) * (proverQueries + (K + 1 + 1 + 2 * s * (K + 1) * (N + 2))) : ℕ) :
            ENNReal) / Fintype.card Digest)) :=
  ZkcSecurity.Commitment.soundness (absorb block) words (scheme model)
    (fun _ => verifier roots t shift s N K) (initial N) (statementRoots N) prover
    (typedCertificate roots t shift block D hD hcompat θ δ foldError)
    (fun _ => ⟨_, _, rfl⟩) (carries model) (initial_determined N) (fun _ => rfl) (K + 1)
    (fun _ => by simp [statementRoots])
    (fun _ => by simpa [statementRoots] using verifier_commitBound roots t shift s N K)
    (FarStatement (K := K) t D δ)
    (fun _ tables falseStatement => by
      obtain ⟨word, rfl, far⟩ := falseStatement
      show Doomed (R₀ := K + 1) roots t shift s D θ δ foldError
        (withTables words [tableOf (N + 1) word] (verifier roots t shift s N K))
      rw [withTables_verifier]
      exact afterCommit_doomed_of_proximity D θ δ foldError proximity word far)
    2 (fun query => LeafHashing.inputs_length model query) proverQueries
    (K + 1 + 1 + 2 * s * (K + 1) * (N + 2)) proverCount
    (fun root proof => verifier_queryBound model roots t shift s block root proof.messages
      proof.openings)
    proverCost _ proverBound
    (fun root proof => verifier_costBound model roots t shift s block foldError _ _ root
      proof.messages proof.openings)

end Bound

end ZkcSecurity.Examples.CommittedFri
