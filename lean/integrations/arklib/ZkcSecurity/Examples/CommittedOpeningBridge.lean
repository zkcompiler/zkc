module

public import ZkcSecurity.Commitment.Soundness
public import ZkcSecurity.Commitment.Charges
public import ZkcSecurity.Commitment.HashedLeaves

@[expose] public section

/-! # One committed table, one challenge and one opening, through the general bridge

This module applies `ZkcSecurity.Commitment.soundness` to the smallest verifier with a committed
table: the statement is the root of a table of `2 ^ depth` rows, the verifier draws one index and
reads the row there, and it accepts exactly when the row is accepted (`validator`). It shows that
the premises of the general theorem are satisfiable together and reproduce the constants of the
committed-opening experiment (`ZkcSecurity.Examples.CommittedOpening.intendedBound`):

* the ideal reading receives the table in the clear and draws the index (`signature`, `absorb`);
  its certificate is one step: from a far table, the drawn row is accepted with probability at most
  `1 - δ` (`certificate`);
* the tables are committed with Merkle trees with hashed leaves of one depth
  (`LeafHashing.scheme`, read through `Extractable.comap`);
* the verifier makes one transcript query and one authentication of at most `depth + 1` hash calls
  (`validator_costBound`, `validator_queryBound`).

`soundness` bounds the probability that the verifier accepts while the table extracted at the
checkpoint of its query is far by the prover's charge plus `(1 - δ) + (depth + 1) · hashError`,
with `hashError = 4 (proverQueries + depth + 2) / |Digest|`. This is a statement about the general
joint experiment of `ZkcSecurity.Commitment`, whose transcript keys are pairs of a history and an
occurrence, not about the experiment of `CommittedOpening`, whose keys are histories; the two
encodings are in bijection on the keys the verifier queries, and the transport between the two
experiments is not stated here.
-/

set_option autoImplicit false

namespace ZkcSecurity.Examples.CommittedOpeningBridge

open OracleComp OracleSpec ZkcSecurity.FiatShamir ZkcSecurity.Commitment

variable {Row Query Digest : Type}

/-- Operations of the ideal reading: receive the table in the clear, draw the index. -/
inductive Op where
  | table
  | index
  deriving DecidableEq

/-- The ideal reading's signature for tables of `2 ^ depth` rows. -/
abbrev signature (Row : Type) (depth : ℕ) : PIR.Signature where
  Op := Op
  Reply
    | .table => Fin (2 ^ depth) → Row
    | .index => Fin (2 ^ depth)

/-- Absorbed events of the ideal reading. -/
inductive Event (Row : Type) where
  | table (rows : List Row)
  | index
  deriving DecidableEq

/-- The table a received list of rows describes, when it has `2 ^ depth` rows. -/
def recoverTable (depth : ℕ) : Event Row → Option (Fin (2 ^ depth) → Row)
  | .table rows =>
      if length : rows.length = 2 ^ depth then
        some fun index => rows[index.val]'(by rw [length]; exact index.isLt)
      else none
  | .index => none

/-- The ideal reading's transcript interface: the table is received in the clear and the index is
the raw answer itself. -/
def absorb (depth : ℕ) :
    Typed.Interface (signature Row depth) (Event Row) (List Row) (fun _ => Fin (2 ^ depth))
  | .table => .receive Event.table (recoverTable depth)
  | .index => .query .index fun _ raw => some raw

/-- The ideal reading receives a committed table through its table operation. -/
def words (depth : ℕ) (default : Row) : Words (signature Row depth) Unit Row where
  word _ := .table
  toTable _ rows position :=
    if below : position < 2 ^ depth then some (rows ⟨position, below⟩) else none
  ofTable _ table index := (table index.val).getD default

/-- The verifier: draw the index, read the committed row there, accept exactly when it is
accepted. The table is the statement's commitment, with handle `0`. -/
def validator (accepts : Row → Bool) (depth : ℕ) :
    PIR.Proc (committed (signature Row depth) Unit Row) Bool :=
  .call (.base .index) fun index => .call (.read 0 index.val) fun row => .done (accepts row)

/-- A table at least a `δ` fraction of whose rows are rejected. -/
def FarRows (accepts : Row → Bool) (depth : ℕ) (fraction : ENNReal) (rows : Fin (2 ^ depth) → Row) :
    Prop :=
  fraction * 2 ^ depth ≤ ((Finset.univ.filter fun index => accepts (rows index) = false).card :
    ENNReal)

/-- The statement is false when its committed table is far. -/
def FalseTable (accepts : Row → Bool) (depth : ℕ) (fraction : ENNReal) (default : Row)
    (_root : Digest) (tables : List (Table Row)) : Prop :=
  ∃ rows, tables = [(words depth default).toTable () rows] ∧ FarRows accepts depth fraction rows

/-- The ideal reading's doomed residuals: rejection, stops, and the verifier on a far table. -/
def Doomed (accepts : Row → Bool) (depth : ℕ) (fraction : ENNReal) (default : Row)
    (process : PIR.Proc (signature Row depth) Bool) : Prop :=
  process = .done false ∨ (∃ stop, process = .halt stop) ∨
    ∃ rows, FarRows accepts depth fraction rows ∧
      process = withTables (words depth default) [(words depth default).toTable () rows]
        (validator accepts depth)

/-- The error of each occurrence: `1 - δ` at the index draw. -/
def error (fraction : ENNReal) : Event Row → ENNReal
  | .index => 1 - fraction
  | .table _ => 0

/-- A far table accepts at most a `1 - δ` fraction of its rows. -/
theorem accepted_fraction_le (accepts : Row → Bool) (depth : ℕ) (fraction : ENNReal)
    (rows : Fin (2 ^ depth) → Row) (far : FarRows accepts depth fraction rows) :
    ((Finset.univ.filter fun index => accepts (rows index) = true).card : ENNReal) /
      (2 ^ depth : ℕ) ≤ 1 - fraction := by
  have total := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun index : Fin (2 ^ depth) => accepts (rows index) = true)
  simp only [Finset.card_univ, Fintype.card_fin, Bool.not_eq_true] at total
  have castTotal : ((Finset.univ.filter fun index : Fin (2 ^ depth) =>
      accepts (rows index) = true).card : ENNReal) +
      ((Finset.univ.filter fun index : Fin (2 ^ depth) => accepts (rows index) = false).card :
        ENNReal) = ((2 ^ depth : ℕ) : ENNReal) := by exact_mod_cast total
  apply ENNReal.div_le_of_le_mul
  rw [ENNReal.eq_sub_of_add_eq (by simp) castTotal, ENNReal.sub_mul (fun _ _ => by simp), one_mul]
  refine tsub_le_tsub_left ?_ _
  simpa [FarRows] using far

theorem withTables_validator (accepts : Row → Bool) (depth : ℕ) (default : Row)
    (rows : Fin (2 ^ depth) → Row) :
    withTables (words depth default) [(words depth default).toTable () rows]
        (validator accepts depth) =
      .call Op.index fun index => .done (accepts (rows index)) := by
  rw [validator, withTables]
  congr 1
  funext index
  have found : lookup [(words depth default).toTable () rows] 0 index.val = some (rows index) := by
    simp [lookup, words, index.isLt]
  rw [withTables, found]
  rfl

/-- The one-step certificate of the ideal reading. -/
def certificate (accepts : Row → Bool) (depth : ℕ) (fraction : ENNReal) (default : Row) :
    Typed.Certificate (absorb (Row := Row) depth) (· = true) (error fraction) where
  doomed := Doomed accepts depth fraction default
  step process doomed := by
    rcases doomed with rfl | ⟨stop, rfl⟩ | ⟨rows, far, rfl⟩
    · show ¬ (false = true)
      simp
    · trivial
    · rw [withTables_validator]
      intro preceding
      change Pr{let raw ← $ᵗ (Fin (2 ^ depth))}[∃ value, some raw = some value ∧
        ¬ Doomed accepts depth fraction default (.done (accepts (rows value)))] ≤ 1 - fraction
      refine (prEvent_mono _ _ (fun raw => accepts (rows raw) = true) fun raw escaping => ?_).trans ?_
      · obtain ⟨value, same, outside⟩ := escaping
        cases Option.some.inj same
        by_contra rejected
        exact outside (Or.inl (by simpa using rejected))
      · rw [SampleableType.prEvent_uniformSample, Fintype.card_fin]
        exact_mod_cast accepted_fraction_le accepts depth fraction rows far

/-- The concrete verifier's statement: the committed root, absorbed with its shape. -/
def initial (root : Digest) : List (Absorbed (Event Row) Unit Digest) := [.root () root]

theorem initial_determined : Typed.Determined (initial (Row := Row) (Digest := Digest)) := by
  intro root other rest otherRest same
  simp only [initial, List.singleton_append, List.cons.injEq, Absorbed.root.injEq, true_and] at same
  exact same.1

section Bound
variable [DecidableEq Row] [DecidableEq Query] [DecidableEq Digest]
variable (model : LeafHashing Row Query Digest)

/-- Merkle trees with hashed leaves of depth `depth`. -/
def scheme (depth : ℕ) : Extractable Unit Row Query Digest :=
  model.scheme.comap fun _ => depth

omit [DecidableEq Row] [DecidableEq Query] in
theorem carries (depth : ℕ) (default : Row) (log : HashLog Query Digest) (shape : Unit) (root : Digest)
    (position : ℕ) (value : Row)
    (found : (scheme model depth).extract log shape root position = some value) :
    normalized (words depth default) ((scheme model depth).extract log) shape root position =
      some value := by
  have below : position < 2 ^ depth := by
    by_contra outside
    simp [scheme, Extractable.comap, LeafHashing.scheme, LeafHashing.extract, outside] at found
  simp [normalized, words, below, found]

omit [DecidableEq Row] [DecidableEq Query] [DecidableEq Digest] in
theorem validator_commitBound (accepts : Row → Bool) (depth : ℕ) :
    CommitBound (validator accepts depth) 0 := fun _ _ => trivial

variable [SampleableType Digest]

omit [DecidableEq Row] [DecidableEq Query] [SampleableType Digest] in
theorem validator_queryBound (accepts : Row → Bool) (depth : ℕ) (root : Digest)
    (messages : List (Message (List Row) Digest)) (openings : List (Opening Row Digest)) :
    IsTotalQueryBound (run (absorb depth) (scheme model depth) (validator accepts depth)
      (initial root) [((), root)] messages openings) (depth + 2) := by
  unfold validator
  rw [run.eq_def]
  simp only [absorb]
  rw [isTotalQueryBound_query_bind_iff]
  refine ⟨by omega, fun raw => ?_⟩
  rw [run.eq_def]
  simp only [List.getElem?_cons_zero]
  match openings with
  | [] => trivial
  | opening :: rest =>
      simp only
      rw [show depth + 2 - 1 = depth + 1 + 0 by omega]
      exact isTotalQueryBound_bind
        (liftHash_queryBound (R := fun _ : List (Event Row) => Fin (2 ^ depth)) (Shape := Unit) _ _
          (LeafHashing.authenticate_queryBound model depth root raw.val opening))
        fun accepted => by cases accepted <;> trivial

omit [DecidableEq Row] [DecidableEq Query] [SampleableType Digest] in
theorem validator_costBound (accepts : Row → Bool) (depth : ℕ) (fraction hashError : ENNReal)
    (root : Digest) (messages : List (Message (List Row) Digest))
    (openings : List (Opening Row Digest)) :
    WorstCaseCostBound (run (absorb depth) (scheme model depth) (validator accepts depth)
        (initial root) [((), root)] messages openings)
      ⟨jointError (Shape := Unit) (Y := Digest) (Query := Query) (error fraction) hashError⟩
      ((1 - fraction) + ((depth + 1 : ℕ) : ENNReal) * hashError) := by
  unfold validator
  rw [run.eq_def]
  simp only [absorb]
  rw [worstCaseCostBound_query_bind_iff]
  intro raw cost member
  refine add_le_add le_rfl ?_
  revert cost
  rw [← worstCaseCostBound_iff_support_bound]
  rw [run.eq_def]
  simp only [List.getElem?_cons_zero]
  match openings with
  | [] => exact (worstCaseCostBound_pure _ _ _).mpr zero_le
  | opening :: rest =>
      simp only
      rw [← add_zero (((depth + 1 : ℕ) : ENNReal) * hashError)]
      exact WorstCaseCostBound.bind
        (liftHash_costBound (R := fun _ : List (Event Row) => Fin (2 ^ depth)) (Shape := Unit)
          (error fraction) hashError _ _
          (LeafHashing.authenticate_queryBound model depth root raw.val opening))
        fun accepted => by cases accepted <;> exact (worstCaseCostBound_pure _ _ _).mpr le_rfl

/-- The committed-opening verifier through the general bridge: it accepts while the table
extracted at the checkpoint of its query is far with probability at most the prover's charge plus
`(1 - δ) + (depth + 1) · 4 (proverQueries + depth + 2) / |Digest|`. -/
theorem soundness [Fintype Digest] (accepts : Row → Bool) (depth : ℕ) (fraction : ENNReal)
    (default : Row)
    (prover : OracleComp (joint (fun _ : List (Event Row) => Fin (2 ^ depth)) Unit Digest Query)
      (Digest × Proof (List Row) Row Digest))
    (proverQueries : ℕ) (proverCount : IsTotalQueryBound prover proverQueries)
    (proverCost : ENNReal)
    (proverBound : WorstCaseCostBound prover
      ⟨jointError (error fraction) ((((1 + 2 + 1) * (proverQueries + (depth + 2)) : ℕ) : ENNReal) /
        Fintype.card Digest)⟩ proverCost) :
    Pr{let result ← (simulateQ randomOracle (experiment (absorb depth) (scheme model depth)
        (fun _ => validator accepts depth) initial (fun root => [((), root)]) prover)).run' ∅}[
      FalseAcceptance (words depth default) (scheme model depth) (fun root => [((), root)])
        (FalseTable accepts depth fraction default) (· = true) result] ≤
      proverCost + ((1 - fraction) + ((depth + 1 : ℕ) : ENNReal) *
        ((((1 + 2 + 1) * (proverQueries + (depth + 2)) : ℕ) : ENNReal) / Fintype.card Digest)) :=
  ZkcSecurity.Commitment.soundness (absorb depth) (words depth default) (scheme model depth)
    (fun _ => validator accepts depth) initial (fun root => [((), root)]) prover
    (certificate accepts depth fraction default) (fun _ => ⟨_, _, rfl⟩)
    (carries model depth default) initial_determined (fun _ => rfl) 1 (fun _ => le_rfl)
    (fun _ => validator_commitBound accepts depth)
    (FalseTable accepts depth fraction default)
    (fun _ tables falseTable => by
      obtain ⟨rows, rfl, far⟩ := falseTable
      exact Or.inr (Or.inr ⟨rows, far, rfl⟩))
    2 (fun query => LeafHashing.inputs_length model query) proverQueries (depth + 2) proverCount
    (fun root proof => validator_queryBound model accepts depth root proof.messages proof.openings)
    proverCost _ proverBound
    (fun root proof => validator_costBound model accepts depth fraction _ root proof.messages
      proof.openings)

end Bound

end ZkcSecurity.Examples.CommittedOpeningBridge
