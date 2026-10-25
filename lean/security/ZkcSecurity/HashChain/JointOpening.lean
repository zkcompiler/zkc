module

public import ZkcSecurity.HashChain.Joint
public import ZkcSecurity.Commitment.Opening
public import ZkcSecurity.FiatShamir.Laws

@[expose] public section

/-! # One committed table and one opening over a Keccak hash chain

The committed-opening verifier of `ZkcSecurity.Examples.CommittedOpeningBridge` reads one row of a
committed table at one drawn index and accepts exactly when the row is accepted. Deployed over a
hash-chain suite, the index is decoded from the counter blocks of one request at the state that
binds the committed root (`chainAbsorb`), and the opening is authenticated with the Merkle tree's
row calls (`rowHashing`) on the same byte hash as the chain.

**The commitment stage** (`chainStage`). The ideal reading receives the table in the clear and
draws the index from the decoded blocks. When the decoder sends uniform blocks to a uniform index
(`ZkcSecurity.FiatShamir.ExactLaw`), the drawn row of a far table is accepted with probability at most `1 - δ`
(`chainCertificate`), and the bridge's stage has the loss
`q · ((1 - δ) + h q) + ((1 - δ) + (depth + 1) · h q)` at `q` prover queries, with
`h q = 4 (q + depth + 2) / |S|` (`chainStage_loss`).

**The provider stage.** The deployed verifier makes `width + depth + 3` calls of the byte hash: the
binding of the root, `width` counter blocks and the absorption of the index occurrence, a leaf call
and `depth` node calls (`deployed_queryBound`); its joint-oracle reading makes `depth + 2` queries
(`jointReading_queryBound`).

**The theorem** (`opening_soundness`). An adversary with at most `q` calls of the byte hash makes
the deployed verifier accept while the table extracted, at the checkpoint of its index key, from
the row calls before that checkpoint is far, with probability at most

```text
(q + V)² / |S| + q · ((1 - δ) + h q) + ((1 - δ) + (depth + 1) · h q),   V = width + depth + 3.
```

The commitment loss is evaluated at the provider's transported budget, `q` joint-oracle queries,
which `ZkcSecurity.HashChain.Joint.translate_queryBound` proves. `keccak_soundness` instantiates
the row and node tags with the installed Keccak-256 rows and the chain's role tags, whose
separation is checked from bytes (`keccak_tagsSeparated`).
-/

set_option autoImplicit false

namespace ZkcSecurity.HashChain.Joint
open OracleComp OracleSpec ZkcSecurity.FiatShamir ZkcSecurity.Commitment
  ZkcSecurity.HashChain.Encoding ZkcSecurity.Examples.CommittedOpeningBridge

variable {Row S : Type}

section Reading
variable (depth width : ℕ)

/-- The ideal reading over a hash chain: the table is received in the clear, and the index is
decoded from the request's counter blocks. -/
def chainAbsorb (decode : (Fin width → S) → Fin (2 ^ depth)) :
    Typed.Interface (signature Row depth) (Event Row) (List Row) (fun _ => Fin width → S)
  | .table => .receive Event.table (recoverTable depth)
  | .index => .query .index fun raw => some (decode raw)

variable [SampleableType S]

/-- The one-step certificate of the ideal reading over a hash chain: from a far table, the decoded
row is accepted with probability at most `1 - δ`. -/
def chainCertificate (accepts : Row → Bool) (fraction : ENNReal) (default : Row)
    (decode : (Fin width → S) → Fin (2 ^ depth)) (uniform : ExactLaw decode) :
    Typed.Certificate (chainAbsorb (Row := Row) depth width decode) (· = true)
      (error (Row := Row) fraction) where
  doomed := Doomed accepts depth fraction default
  step process doomed := by
    rcases doomed with rfl | ⟨stop, rfl⟩ | ⟨rows, far, rfl⟩
    · show ¬ (false = true)
      simp
    · trivial
    · rw [withTables_validator]
      change Pr{let raw ← $ᵗ (Fin width → S)}[∃ value, some (decode raw) = some value ∧
        ¬ Doomed accepts depth fraction default (.done (accepts (rows value)))] ≤ 1 - fraction
      refine (prEvent_mono _ _ (fun raw => accepts (rows (decode raw)) = true)
        fun raw escaping => ?_).trans ?_
      · obtain ⟨value, same, outside⟩ := escaping
        cases Option.some.inj same
        by_contra rejected
        exact outside (Or.inl (by simpa using rejected))
      · rw [uniform (fun index => accepts (rows index) = true), SampleableType.prEvent_uniformSample,
          Fintype.card_fin]
        exact_mod_cast accepted_fraction_le accepts depth fraction rows far

end Reading

section Stage
variable [DecidableEq Row] [DecidableEq S] [SampleableType S] [Fintype S] (depth width : ℕ)
  (decode : (Fin width → S) → Fin (2 ^ depth))

omit [DecidableEq Row] [SampleableType S] [Fintype S] in
/-- The joint-oracle reading of the committed-opening verifier makes one transcript query and at
most `depth + 1` hash calls. -/
theorem chainValidator_queryBound (accepts : Row → Bool) (root : S)
    (messages : List (Message (List Row) S)) (openings : List (Opening Row S)) :
    IsTotalQueryBound (run (chainAbsorb (Row := Row) depth width decode)
      (scheme (rowHashing Row S) depth) (validator accepts depth) (initial root) [((), root)] messages
      openings) (depth + 2) := by
  unfold validator
  rw [run.eq_def]
  simp only [chainAbsorb]
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
        (liftHash_queryBound (Raw := fun _ : Event Row => Fin width → S) (Shape := Unit) _ _
          (LeafHashing.authenticate_queryBound (rowHashing Row S) depth root (decode raw).val
            opening))
        fun accepted => by cases accepted <;> trivial

omit [DecidableEq Row] [SampleableType S] [Fintype S] in
/-- The committed-opening verifier's charge: `1 - δ` at its transcript query and one hash charge
per hash call. -/
theorem chainValidator_costBound (accepts : Row → Bool) (fraction hashError : ENNReal) (root : S)
    (messages : List (Message (List Row) S)) (openings : List (Opening Row S)) :
    WorstCaseCostBound (run (chainAbsorb (Row := Row) depth width decode)
        (scheme (rowHashing Row S) depth) (validator accepts depth) (initial root) [((), root)]
        messages openings)
      ⟨jointError (Shape := Unit) (Y := S) (Query := RowCall Row S) (error fraction) hashError⟩
      ((1 - fraction) + ((depth + 1 : ℕ) : ENNReal) * hashError) := by
  unfold validator
  rw [run.eq_def]
  simp only [chainAbsorb]
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
        (liftHash_costBound (Raw := fun _ : Event Row => Fin width → S) (Shape := Unit)
          (error fraction) hashError _ _
          (LeafHashing.authenticate_queryBound (rowHashing Row S) depth root (decode raw).val opening))
        fun accepted => by cases accepted <;> exact (worstCaseCostBound_pure _ _ _).mpr le_rfl

/-- The hash charge of the committed-opening verifier at `q` prover queries:
`4 (q + depth + 2) / |S|`. -/
noncomputable abbrev openingHash (queries : ℕ) : ENNReal :=
  Stage.hashCharge S 1 2 (depth + 2) queries

/-- The commitment stage of the committed-opening verifier over a hash chain, from the trivial
game to its joint game. -/
noncomputable def chainStage (accepts : Row → Bool) (fraction : ENNReal) (default : Row)
    (uniform : ExactLaw decode) :
    Stage.Relation Stage.Game.trivial
      (Stage.jointGame (chainAbsorb (Row := Row) depth width decode) (words depth default)
        (scheme (rowHashing Row S) depth) (fun _ : S => validator accepts depth) initial
        (fun root => [((), root)]) (FalseTable accepts depth fraction default) (· = true)) :=
  Stage.commitmentRelation (chainAbsorb depth width decode) (words depth default)
    (scheme (rowHashing Row S) depth) (fun _ : S => validator accepts depth) initial
    (fun root => [((), root)]) (chainCertificate depth width accepts fraction default decode uniform)
    (siteBound := 1 - fraction) (fun event => by cases event <;> simp [error]) (fun _ => ⟨_, _, rfl⟩)
    (carries (rowHashing Row S) depth default) initial_determined (fun _ => rfl) 1 (fun _ => le_rfl)
    (fun _ => validator_commitBound accepts depth) (FalseTable accepts depth fraction default)
    (fun _ tables falseTable => by
      obtain ⟨rows, rfl, far⟩ := falseTable
      exact Or.inr (Or.inr ⟨rows, far, rfl⟩))
    2 (fun query => LeafHashing.inputs_length (rowHashing Row S) query) (depth + 2)
    (fun root proof => chainValidator_queryBound depth width decode accepts root proof.messages
      proof.openings)
    (fun queries => (1 - fraction) + ((depth + 1 : ℕ) : ENNReal) * openingHash (S := S) depth queries)
    fun queries root proof => chainValidator_costBound depth width decode accepts fraction _ root
      proof.messages proof.openings

theorem chainStage_loss (accepts : Row → Bool) (fraction : ENNReal) (default : Row)
    (uniform : ExactLaw decode) (queries : ℕ) :
    (chainStage depth width decode accepts fraction default uniform).loss queries =
      queries * ((1 - fraction) + openingHash (S := S) depth queries) +
        ((1 - fraction) + ((depth + 1 : ℕ) : ENNReal) * openingHash (S := S) depth queries) :=
  rfl

end Stage

section Calls
variable {E Shape Query : Type}

theorem collect_byteCall_queryBound :
    ∀ (count : ℕ) (bytesOf : Fin count → Bytes),
      IsTotalQueryBound (collect count fun index => byteCall (S := S) (bytesOf index)) count
  | 0, _ => trivial
  | count + 1, bytesOf => by
      simp only [collect, byteCall]
      refine isTotalQueryBound_query_bind_iff.mpr ⟨Nat.succ_pos _, fun head => ?_⟩
      have tail := isTotalQueryBound_bind (ob := fun tail : Fin count → S =>
        (pure (Fin.cons head tail) : OracleComp (ByteHash S) (Fin (count + 1) → S)))
        (n₂ := 0) (collect_byteCall_queryBound count fun index => bytesOf index.succ) fun _ => trivial
      simpa [byteCall] using tail

/-- Hash calls on the byte hash keep a computation's query bound. -/
theorem byteHash_queryBound (encoding : Encoding E Shape S Query) {α : Type} :
    ∀ (computation : OracleComp (Query →ₒ S) α) (bound : ℕ), IsTotalQueryBound computation bound →
      IsTotalQueryBound (simulateQ (byteHash encoding) computation) bound := by
  intro computation
  induction computation using OracleComp.inductionOn with
  | pure value => intro _ _; trivial
  | query_bind query next ih =>
      intro bound bounded
      rw [isTotalQueryBound_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_spec_query, byteHash, byteCall]
      exact isTotalQueryBound_query_bind_iff.mpr ⟨bounded.1, fun reply => ih reply _ (bounded.2 reply)⟩

end Calls

section Deployed
variable [DecidableEq Row] [DecidableEq S] [SampleableType S] (depth width : ℕ)
  (decode : (Fin width → S) → Fin (2 ^ depth))

omit [DecidableEq Row] [SampleableType S] in
/-- The deployed committed-opening verifier makes `width + depth + 3` calls of the byte hash: the
binding of the root, the counter blocks and absorption of the index request, and the
authentication of the opening. -/
theorem deployed_queryBound (encoding : Encoding (Event Row) Unit S (RowCall Row S))
    (accepts : Row → Bool) (root : S) (proof : Proof (List Row) Row S) :
    IsTotalQueryBound (deployed encoding width (chainAbsorb (Row := Row) depth width decode)
      (scheme (rowHashing Row S) depth) (fun _ : S => validator accepts depth) initial
      (fun root => [((), root)]) root proof) (width + depth + 3) := by
  unfold deployed
  simp only [initial, chainVerify, absorbAll, pure_bind, byteChain]
  refine isTotalQueryBound_query_bind_iff.mpr ⟨by omega, fun state => ?_⟩
  unfold validator
  rw [chainRead.eq_def]
  simp only [chainAbsorb]
  rw [show width + depth + 3 - 1 = width + (1 + (depth + 1)) by omega]
  refine isTotalQueryBound_bind (collect_byteCall_queryBound width _) fun raw => ?_
  refine isTotalQueryBound_query_bind_iff.mpr ⟨by omega, fun advanced => ?_⟩
  rw [show 1 + (depth + 1) - 1 = depth + 1 by omega]
  simp only [map_eq_bind_pure_comp]
  rw [show depth + 1 = depth + 1 + 0 by omega]
  refine isTotalQueryBound_bind ?_ fun _ => trivial
  rw [chainRead.eq_def]
  simp only [List.getElem?_cons_zero]
  match proof.openings with
  | [] => trivial
  | opening :: rest =>
      simp only
      rw [show depth + 1 = depth + 1 + 0 by omega]
      refine isTotalQueryBound_bind (byteHash_queryBound encoding _ _
        ((isTotalQueryBound_withQueryLog_iff _ _).mpr (LeafHashing.authenticate_queryBound
          (rowHashing Row S) depth root (decode raw).val opening))) fun authenticated => ?_
      cases authenticated.1 <;> simp [chainRead] <;> trivial

omit [DecidableEq Row] [SampleableType S] in
/-- The committed-opening verifier's joint-oracle reading makes at most `depth + 2` queries. -/
theorem jointReading_queryBound (accepts : Row → Bool) (root : S) (proof : Proof (List Row) Row S) :
    IsTotalQueryBound (jointReading width (chainAbsorb (Row := Row) depth width decode)
      (scheme (rowHashing Row S) depth) (fun _ : S => validator accepts depth) initial
      (fun root => [((), root)]) root proof) (depth + 2) :=
  (isTotalQueryBound_withQueryLog_iff _ _).mpr
    (chainValidator_queryBound depth width decode accepts root proof.messages proof.openings)

end Deployed

section Soundness
variable [DecidableEq Row] [DecidableEq S] [Inhabited S] [SampleableType S] [Fintype S]
  (depth width : ℕ) (decode : (Fin width → S) → Fin (2 ^ depth))

/-- Soundness of the committed-opening verifier over a hash chain on one byte hash, with row calls
in their own namespace: an adversary with at most `q` calls of the byte hash makes the deployed
verifier accept while the table extracted at the checkpoint of its index key is far with
probability at most `(q + V)² / |S|`, `V = width + depth + 3`, plus the commitment stage's loss at
`q`: `q · ((1 - δ) + h q) + ((1 - δ) + (depth + 1) · h q)` with `h q = 4 (q + depth + 2) / |S|`. -/
theorem opening_soundness (encoding : Encoding (Event Row) Unit S (RowCall Row S))
    (positive : 0 < width) (small : width ≤ 2 ^ 64) (uniform : ExactLaw decode)
    (accepts : Row → Bool) (fraction : ENNReal) (default : Row)
    (adversary : OracleComp (ByteHash S) (S × Proof (List Row) Row S)) {calls : ℕ}
    (bounded : IsTotalQueryBound adversary calls) :
    concreteFailure encoding width (chainAbsorb depth width decode) (scheme (rowHashing Row S) depth)
        (words depth default) (fun _ : S => validator accepts depth) initial (fun root => [((), root)])
        (FalseTable accepts depth fraction default) (· = true) adversary () ≤
      (((calls + (width + depth + 3)) * (calls + (width + depth + 3)) : ℕ) : ENNReal) /
          Fintype.card S +
        (calls * ((1 - fraction) + openingHash (S := S) depth calls) +
          ((1 - fraction) + ((depth + 1 : ℕ) : ENNReal) * openingHash (S := S) depth calls)) := by
  have composed := committed_soundness encoding width (chainAbsorb depth width decode)
    (scheme (rowHashing Row S) depth) (words depth default) (fun _ : S => validator accepts depth)
    initial (fun root => [((), root)]) (FalseTable accepts depth fraction default) (· = true) positive
    small (fun _ => List.cons_ne_nil _ _) (width + depth + 3)
    (deployed_queryBound depth width decode encoding accepts)
    (jointReading_queryBound depth width decode accepts)
    (chainStage depth width decode accepts fraction default uniform) adversary bounded
  rwa [chainStage_loss] at composed

end Soundness

section Keccak

/-- Keccak-256 digests as numbers below `2^256`. -/
abbrev KeccakDigest := Fin (2 ^ 256)

/-- A digest's 32 big-endian bytes. -/
def digestBytes (digest : KeccakDigest) : Bytes :=
  List.ofFn fun index : Fin 32 => UInt8.ofNat (digest.val / 256 ^ (31 - index.val))

theorem digestBytes_length (digest : KeccakDigest) : (digestBytes digest).length = 32 := by
  simp [digestBytes]

theorem digestBytes_injective : Function.Injective digestBytes := by
  intro first second same
  have bytes := fun index => congrArg UInt8.toNat (congrFun (List.ofFn_injective same) index)
  simp only [UInt8.toNat_ofNat'] at bytes
  have digits : ∀ index < 32, first.val / 256 ^ index % 256 = second.val / 256 ^ index % 256 := by
    intro index below
    have := bytes ⟨31 - index, by omega⟩
    simp only [show 31 - (31 - index) = index by omega] at this
    simp at this
    exact this
  have residues := mod_pow_eq_of_digits 32 digits
  have firstBelow : first.val < 256 ^ 32 := by simp
  have secondBelow : second.val < 256 ^ 32 := by simp
  rw [Nat.mod_eq_of_lt firstBelow, Nat.mod_eq_of_lt secondBelow] at residues
  exact Fin.ext residues

/-- The index of `2^depth` rows read from one digest: its residue modulo `2^depth`. -/
def keccakIndex (depth : ℕ) (fits : depth ≤ 256) (raw : Fin 1 → KeccakDigest) : Fin (2 ^ depth) :=
  (Prod.swap (finProdFinEquiv.symm
    (finCongr (by rw [← pow_add, Nat.sub_add_cancel fits]) (raw 0) :
      Fin (2 ^ (256 - depth) * 2 ^ depth)))).1

theorem keccakIndex_val (depth : ℕ) (fits : depth ≤ 256) (raw : Fin 1 → KeccakDigest) :
    (keccakIndex depth fits raw).val = (raw 0).val % 2 ^ depth := by
  simp [keccakIndex, finProdFinEquiv, Fin.modNat]

/-- The residue of a uniform digest modulo `2^depth` is a uniform index. -/
theorem keccakIndex_uniform (depth : ℕ) (fits : depth ≤ 256) :
    ExactLaw (keccakIndex depth fits) := by
  intro predicate
  let pair : (Fin 1 → KeccakDigest) → Fin (2 ^ depth) × Fin (2 ^ (256 - depth)) := fun raw =>
    Prod.swap (finProdFinEquiv.symm
      (finCongr (by rw [← pow_add, Nat.sub_add_cancel fits]) (raw 0) :
        Fin (2 ^ (256 - depth) * 2 ^ depth)))
  have bijective : Function.Bijective pair :=
    ((Equiv.funUnique (Fin 1) KeccakDigest).trans ((finCongr (by rw [← pow_add,
      Nat.sub_add_cancel fits])).trans (finProdFinEquiv.symm.trans (Equiv.prodComm _ _)))).bijective
  have law : (keccakIndex depth fits <$> ($ᵗ (Fin 1 → KeccakDigest))) =ᵈ ($ᵗ (Fin (2 ^ depth))) := by
    have factored : keccakIndex depth fits = Prod.fst ∘ pair := rfl
    rw [factored, comp_map]
    refine ((SampleableType.map_uniformSample_evalDistEq_of_bijective bijective).map Prod.fst).trans ?_
    rw [SampleableType.uniformSample_prod_eq_bind]
    simp only [map_bind, map_pure]
    simpa only [bind_pure] using
      (EvalDistEq.bind_right ($ᵗ (Fin (2 ^ depth))) fun index =>
        OracleComp.EvalDistEq.bind_const ($ᵗ (Fin (2 ^ (256 - depth)))) (pure index))
  have same := _root_.EvalDistEq.prEvent_eq law predicate
  rw [prEvent_map] at same
  exact same

variable {Row : Type}

/-- The chain events of the committed opening as bytes: a root, the index occurrence, and a table
received in the clear. -/
def openingEventBytes (rowBytes : Row → Bytes) : Absorbed (Event Row) Unit KeccakDigest → Bytes
  | .root () root => 0 :: digestBytes root
  | .event .index => [1]
  | .event (.table rows) => 2 :: rows.flatMap rowBytes

theorem flatMap_injective {rowBytes : Row → Bytes} {rowLength : ℕ} (positive : 0 < rowLength)
    (rowLengths : ∀ row, (rowBytes row).length = rowLength) (rowInjective : Function.Injective rowBytes) :
    Function.Injective fun rows : List Row => rows.flatMap rowBytes := by
  intro first
  induction first with
  | nil =>
      intro second same
      cases second with
      | nil => rfl
      | cons row rest =>
          have lengths := congrArg List.length same
          simp only [List.flatMap_nil, List.length_nil, List.flatMap_cons, List.length_append,
            rowLengths] at lengths
          omega
  | cons row rest ih =>
      intro second same
      cases second with
      | nil =>
          have lengths := congrArg List.length same
          simp only [List.flatMap_cons, List.length_append, rowLengths, List.flatMap_nil,
            List.length_nil] at lengths
          omega
      | cons row' rest' =>
          simp only [List.flatMap_cons] at same
          obtain ⟨rows, rests⟩ := List.append_inj same (by rw [rowLengths, rowLengths])
          rw [rowInjective rows, ih rests]

theorem openingEventBytes_injective {rowBytes : Row → Bytes} {rowLength : ℕ} (positive : 0 < rowLength)
    (rowLengths : ∀ row, (rowBytes row).length = rowLength) (rowInjective : Function.Injective rowBytes) :
    Function.Injective (openingEventBytes rowBytes) := by
  intro first second same
  cases first with
  | root shape root =>
      cases shape
      cases second with
      | root shape' root' =>
          cases shape'
          simp only [openingEventBytes, List.cons.injEq, true_and] at same
          rw [digestBytes_injective same]
      | event event =>
          cases event <;>
            simp only [openingEventBytes, List.cons.injEq] at same <;> exact absurd same.1 (by decide)
  | event event =>
      cases event with
      | index =>
          cases second with
          | root shape' root' =>
              cases shape'
              simp only [openingEventBytes, List.cons.injEq] at same
              exact absurd same.1 (by decide)
          | event event' =>
              cases event' with
              | index => rfl
              | table rows' =>
                  simp only [openingEventBytes, List.cons.injEq] at same
                  exact absurd same.1 (by decide)
      | table rows =>
          cases second with
          | root shape' root' =>
              cases shape'
              simp only [openingEventBytes, List.cons.injEq] at same
              exact absurd same.1 (by decide)
          | event event' =>
              cases event' with
              | index =>
                  simp only [openingEventBytes, List.cons.injEq] at same
                  exact absurd same.1 (by decide)
              | table rows' =>
                  simp only [openingEventBytes, List.cons.injEq, true_and] at same
                  rw [flatMap_injective positive rowLengths rowInjective same]

/-- The byte encodings of the committed opening over the Keccak hash chain: the installed Keccak-256
rows of one table shape, 32-byte digests and the opening's event bytes, with the Keccak and chain
tags separated. -/
def keccakEncoding (codec : Bytes) (tableWidth tableHeight : ℕ) (rowBytes : Row → Bytes)
    {rowLength : ℕ} (positive : 0 < rowLength) (rowLengths : ∀ row, (rowBytes row).length = rowLength)
    (rowInjective : Function.Injective rowBytes) :
    Encoding (Event Row) Unit KeccakDigest (RowCall Row KeccakDigest) :=
  (keccakRows codec tableWidth tableHeight rowBytes rowInjective).encoding digestBytes
    (openingEventBytes rowBytes) 32 digestBytes_length digestBytes_injective
    (openingEventBytes_injective positive rowLengths rowInjective)

/-- The hash charge of the committed opening over Keccak-256 at `q` prover queries:
`4 (q + depth + 2) / 2^256`. -/
noncomputable def keccakHash (depth queries : ℕ) : ENNReal :=
  ((4 * (queries + (depth + 2)) : ℕ) : ENNReal) / 2 ^ 256

/-- Soundness of the committed-opening verifier over the Keccak-256 hash chain with byte tags: the
row calls are the installed Keccak-256 leaf and node inputs, the chain inputs carry the chain's role
tags, and the index of `2^depth` rows is one request's digest modulo `2^depth`. An adversary with at
most `q` calls of the byte hash, read as a random oracle, makes the deployed verifier accept while
the table extracted from its row calls at the checkpoint of the index key is far with probability
at most

```text
(q + depth + 4)² / 2^256 + q · ((1 - δ) + 4 (q + depth + 2) / 2^256)
  + ((1 - δ) + (depth + 1) · 4 (q + depth + 2) / 2^256).
```

The first term is the chain's collision-or-prediction bound over the joint trace of the adversary's
`q` calls and the verifier's `depth + 4`; the rest is the commitment stage's loss at the provider's
transported budget `q`. -/
theorem keccak_soundness [DecidableEq Row] (codec : Bytes) (tableWidth tableHeight : ℕ)
    (rowBytes : Row → Bytes) {rowLength : ℕ} (positive : 0 < rowLength)
    (rowLengths : ∀ row, (rowBytes row).length = rowLength) (rowInjective : Function.Injective rowBytes)
    (depth : ℕ) (fits : depth ≤ 256) (accepts : Row → Bool) (fraction : ENNReal) (default : Row)
    (adversary : OracleComp (ByteHash KeccakDigest) (KeccakDigest × Proof (List Row) Row KeccakDigest))
    {calls : ℕ} (bounded : IsTotalQueryBound adversary calls) :
    concreteFailure (keccakEncoding codec tableWidth tableHeight rowBytes positive rowLengths rowInjective)
        1 (chainAbsorb depth 1 (keccakIndex depth fits)) (scheme (rowHashing Row KeccakDigest) depth)
        (words depth default) (fun _ : KeccakDigest => validator accepts depth) initial
        (fun root => [((), root)]) (FalseTable accepts depth fraction default) (· = true) adversary () ≤
      (((calls + (depth + 4)) * (calls + (depth + 4)) : ℕ) : ENNReal) / 2 ^ 256 +
        (calls * ((1 - fraction) + keccakHash depth calls) +
          ((1 - fraction) + ((depth + 1 : ℕ) : ENNReal) * keccakHash depth calls)) := by
  have composed := opening_soundness depth 1 (keccakIndex depth fits)
    (keccakEncoding codec tableWidth tableHeight rowBytes positive rowLengths rowInjective) Nat.one_pos
    (by norm_num) (keccakIndex_uniform depth fits) accepts fraction default adversary bounded
  have verifierCalls : 1 + depth + 3 = depth + 4 := by omega
  have digests : ((Fintype.card KeccakDigest : ℕ) : ENNReal) = 2 ^ 256 := by
    rw [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  simp only [openingHash, Stage.hashCharge, verifierCalls, digests] at composed
  simpa [keccakHash] using composed

end Keccak

end ZkcSecurity.HashChain.Joint
