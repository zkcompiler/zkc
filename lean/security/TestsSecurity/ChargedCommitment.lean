import ZkcSecurity.Commitment.Opening
import ZkcTools.DeclarationAudit

/-! A verifier with a committed table through the charged bridge, with an ideal charge that reads
the extracted table.

The verifier of `ZkcSecurity.Examples.CommittedOpeningBridge` draws one index and reads the
committed row there. Its ideal reading receives the table in the clear as a table event
(`messages`), so the ideal history at the draw holds the table as extracted at the checkpoint. The
charged certificate (`certificate`) charges the draw with the smaller of the received table's
accepted fraction and `1 - δ` (`idealCharge`): a charge that reads the extracted history. From a
far table the drawn row is accepted with probability exactly the accepted fraction, which is at
most `1 - δ`.

The concrete history holds only the root, so the concrete-key charge is `1 - δ` at the draw; it
dominates the ideal charge at the key's history read through every extraction (`dominates`).
Two extractions of one root give different ideal charges (`idealCharge_reads_extraction`), so the
domination is over a charge that really depends on the extraction. The general bridge for charged
certificates (`ZkcSecurity.Commitment.soundness_charged`) then bounds the verifier with the
pathwise costs of the concrete reading: the prover's charge plus
`(1 - δ) + (depth + 1) · hashError` (`charged_soundness`). -/

namespace TestsSecurity.ChargedCommitment
open OracleComp OracleSpec ZkcSecurity.FiatShamir ZkcSecurity.Commitment
open ZkcSecurity.Examples.CommittedOpeningBridge
open scoped ENNReal

variable {Row Query Digest : Type}

theorem recoverTable_ofFn (depth : ℕ) (rows : Fin (2 ^ depth) → Row) :
    recoverTable depth (Event.table (List.ofFn rows)) = some rows := by
  simp [recoverTable]

/-- The ideal reading receives the committed table as the table event of its rows. -/
def messages (depth : ℕ) (default : Row) :
    WordMessages (absorb (Row := Row) depth) (words depth default) where
  event _ := Event.table
  recover _ := recoverTable depth
  absorbed _ := rfl
  message _ rows := List.ofFn rows
  recovers _ rows := recoverTable_ofFn depth rows

/-- The fraction of rows that are accepted. -/
noncomputable def acceptedFraction (accepts : Row → Bool) (depth : ℕ)
    (rows : Fin (2 ^ depth) → Row) : ENNReal :=
  ((Finset.univ.filter fun index => accepts (rows index) = true).card : ENNReal) / (2 ^ depth : ℕ)

/-- The accepted fraction of the table an ideal history received, and one when the history is
not one received table. -/
noncomputable def receivedFraction (accepts : Row → Bool) (depth : ℕ) :
    List (Event Row) → ENNReal
  | [event] =>
      match recoverTable depth event with
      | some rows => acceptedFraction accepts depth rows
      | none => 1
  | _ => 1

/-- The ideal charge: the draw is charged the smaller of the received table's accepted fraction
and `1 - δ`. -/
noncomputable def idealCharge (accepts : Row → Bool) (depth : ℕ) (fraction : ENNReal)
    (history : List (Event Row)) : Event Row → ENNReal
  | .index => min (receivedFraction accepts depth history) (1 - fraction)
  | .table _ => 0

theorem receivedFraction_rows (accepts : Row → Bool) (depth : ℕ) (rows : Fin (2 ^ depth) → Row) :
    receivedFraction accepts depth [Event.table (List.ofFn rows)] =
      acceptedFraction accepts depth rows := by
  simp only [receivedFraction, recoverTable_ofFn]

/-- The doomed pairs: rejection, stops, and the verifier on a far table after the ideal history
that received it. -/
def Doomed (accepts : Row → Bool) (depth : ℕ) (fraction : ENNReal) (default : Row)
    (history : List (Event Row)) (process : PIR.Proc (signature Row depth) Bool) : Prop :=
  process = .done false ∨ (∃ stop, process = .halt stop) ∨
    ∃ rows, FarRows accepts depth fraction rows ∧ history = [Event.table (List.ofFn rows)] ∧
      process = withTables (words depth default) [(words depth default).toTable () rows]
        (validator accepts depth)

/-- The charged certificate of the ideal reading. -/
noncomputable def certificate (accepts : Row → Bool) (depth : ℕ) (fraction : ENNReal)
    (default : Row) :
    Typed.ChargedCertificate (absorb (Row := Row) depth) (· = true)
      (idealCharge accepts depth fraction) where
  doomed := Doomed accepts depth fraction default
  step history process doomed := by
    rcases doomed with rfl | ⟨stop, rfl⟩ | ⟨rows, far, rfl, rfl⟩
    · show ¬ (false = true)
      simp
    · trivial
    · rw [withTables_validator]
      change Pr{let raw ← $ᵗ (Fin (2 ^ depth))}[∃ value, some raw = some value ∧
        ¬ Doomed accepts depth fraction default (_ ++ [Event.index]) (.done (accepts (rows value)))] ≤
          min (receivedFraction accepts depth [Event.table (List.ofFn rows)]) (1 - fraction)
      rw [receivedFraction_rows]
      have escape : Pr{let raw ← $ᵗ (Fin (2 ^ depth))}[∃ value, some raw = some value ∧
          ¬ Doomed accepts depth fraction default ([Event.table (List.ofFn rows)] ++ [Event.index])
            (.done (accepts (rows value)))] ≤ acceptedFraction accepts depth rows := by
        refine (prEvent_mono _ _ (fun raw => accepts (rows raw) = true) fun raw escaping => ?_).trans ?_
        · obtain ⟨value, same, outside⟩ := escaping
          cases Option.some.inj same
          by_contra rejected
          exact outside (Or.inl (by simpa using rejected))
        · rw [SampleableType.prEvent_uniformSample, Fintype.card_fin]
          rfl
      exact le_min escape ((escape.trans (le_of_eq rfl)).trans
        (accepted_fraction_le accepts depth fraction rows far))

/-- The concrete-key charge, `1 - δ` at the draw, dominates the ideal charge at the key's history
read through every extraction. -/
theorem dominates (accepts : Row → Bool) (depth : ℕ) (fraction : ENNReal) (default : Row)
    (extracted : Unit → Digest → Table Row) (history : List (Absorbed (Event Row) Unit Digest))
    (occurrence : Event Row) :
    idealCharge accepts depth fraction ((messages depth default).ideal.read extracted history)
        occurrence ≤ error fraction occurrence := by
  cases occurrence with
  | index => exact min_le_right _ _
  | table _ => exact zero_le

theorem rows_of_falseTable (accepts : Row → Bool) (depth : ℕ) (fraction : ENNReal) (default : Row)
    (extracted : Unit → Digest → Table Row) (root : Digest)
    (falseTable : FalseTable accepts depth fraction default root
      (rootTables (words depth default) extracted [((), root)])) :
    FarRows accepts depth fraction ((words depth default).ofTable () (extracted () root)) := by
  obtain ⟨rows, same, far⟩ := falseTable
  have equal : (words depth default).ofTable () (extracted () root) = rows := by
    funext index
    simp only [rootTables, List.map_cons, List.map_nil, List.cons.injEq, and_true] at same
    have at_index := congrFun same index.val
    simpa [normalized, words, index.isLt] using at_index
  rwa [equal]

section Bound
variable [DecidableEq Row] [DecidableEq Query] [DecidableEq Digest] [SampleableType Digest]
  [Fintype Digest] (model : LeafHashing Row Query Digest)

/-- The committed-opening verifier through the bridge for charged certificates: it accepts while
the table extracted at the checkpoint of its query is far with probability at most the prover's
charge plus `(1 - δ) + (depth + 1) · hashError`, with `hashError` computed from the query counts. -/
theorem charged_soundness (accepts : Row → Bool) (depth : ℕ) (fraction : ENNReal) (default : Row)
    (prover : OracleComp (joint (fun _ : Event Row => Fin (2 ^ depth)) Unit Digest Query)
      (Digest × Proof (List Row) Row Digest))
    (proverQueries : ℕ) (proverCount : IsTotalQueryBound prover proverQueries)
    (proverCost : ENNReal)
    (proverBound : WorstCaseCostBound prover
      ⟨jointCharge (Shape := Unit) (Y := Digest) (Query := Query) (fun _ event => error fraction event)
        ((((1 + 2 + 1) * (proverQueries + (depth + 2)) : ℕ) : ENNReal) /
          Fintype.card Digest)⟩ proverCost) :
    Pr{let result ← (simulateQ randomOracle (experiment (absorb depth) (scheme model depth)
        (fun _ => validator accepts depth) initial (fun root => [((), root)]) prover)).run' ∅}[
      FalseAcceptance (words depth default) (scheme model depth) (fun root => [((), root)])
        (FalseTable accepts depth fraction default) (· = true) result] ≤
      proverCost + ((1 - fraction) + ((depth + 1 : ℕ) : ENNReal) *
        ((((1 + 2 + 1) * (proverQueries + (depth + 2)) : ℕ) : ENNReal) / Fintype.card Digest)) := by
  have targetsBounded : ∀ table : JointTable (fun _ : Event Row => Fin (2 ^ depth)) Unit Digest Query,
      (targets (scheme model depth) 1 table ((tableQueryLog (experiment (absorb depth)
        (scheme model depth) (fun _ => validator accepts depth) initial (fun root => [((), root)])
          prover) table).map Sigma.fst)).length ≤ (1 + 2 + 1) * (proverQueries + (depth + 2)) := by
    intro table
    refine (targets_length_le (scheme model depth) 1 2
      (fun query => LeafHashing.inputs_length model query) table _).trans
        (Nat.mul_le_mul_left _ ?_)
    rw [List.length_map]
    exact tableQueryLog_length_le table _ _ (experiment_queryBound (absorb depth)
      (scheme model depth) (fun _ => validator accepts depth) initial (fun root => [((), root)])
      prover proverQueries (depth + 2) proverCount fun root proof =>
        validator_queryBound model accepts depth root proof.messages proof.openings)
  have verifierBound : ∀ (root : Digest) (proof : Proof (List Row) Row Digest),
      WorstCaseCostBound (run (absorb depth) (scheme model depth) (validator accepts depth)
        (initial root) [((), root)] proof.messages proof.openings)
        ⟨jointCharge (Shape := Unit) (Y := Digest) (Query := Query)
          (fun _ event => error fraction event)
          ((((1 + 2 + 1) * (proverQueries + (depth + 2)) : ℕ) : ENNReal) / Fintype.card Digest)⟩
        ((1 - fraction) + ((depth + 1 : ℕ) : ENNReal) *
          ((((1 + 2 + 1) * (proverQueries + (depth + 2)) : ℕ) : ENNReal) /
            Fintype.card Digest)) := by
    intro root proof
    rw [← jointError_eq]
    exact validator_costBound model accepts depth fraction _ root proof.messages proof.openings
  exact ZkcSecurity.Commitment.soundness_charged (absorb depth) (words depth default)
    (scheme model depth) (fun _ => validator accepts depth) initial (fun root => [((), root)]) prover
    (certificate accepts depth fraction default) (messages depth default).ideal
    ((messages depth default).commitDoomed (certificate accepts depth fraction default))
    (fun _ event => error fraction event) (dominates accepts depth fraction default)
    (carries model depth default) initial_determined (fun _ => rfl) 1 (fun _ => le_rfl)
    (fun _ => validator_commitBound accepts depth) (FalseTable accepts depth fraction default)
    (fun root extracted falseTable => .inr (.inr ⟨_, rows_of_falseTable accepts depth fraction
      default extracted root falseTable, rfl, by simp [rootTables, normalized]⟩))
    _ targetsBounded proverCost _ proverBound verifierBound

end Bound

/-- Two extractions of one root give different ideal charges at the draw: the table of one
accepted row and the table of one rejected row. -/
theorem idealCharge_reads_extraction (root : Digest) :
    idealCharge (Row := Bool) id 0 0 ((messages 0 false).ideal.read
        (fun _ _ _ => some true) [.root () root]) .index ≠
      idealCharge (Row := Bool) id 0 0 ((messages 0 false).ideal.read
        (fun _ _ _ => some false) [.root () root]) .index := by
  simp [idealCharge, WordMessages.ideal, messages, words, receivedFraction, recoverTable,
    acceptedFraction]

end TestsSecurity.ChargedCommitment

run_cmd ZkcTools.DeclarationAudit.checkCurrent "CHARGED-COMMITMENT-AXIOM-PASS"
