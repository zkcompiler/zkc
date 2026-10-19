import ZkcSecurity.FiatShamir.Obligations
import ZkcSecurity.Examples.CommittedOpening
import TestsSecurity.Counterexamples.Support
import Mathlib.Data.ZMod.Basic

/-! Counterexamples for commitment openings and hash effects.

- **Pruned and unpruned verification under a stateful handler.** A verifier that
  hashes the same leaf twice and its pruned form that hashes it once return the
  same outcome under every handler with the hash laws (`lawful_preserves`),
  including one whose stop depends on the input alone (`inputStopping_lawful`,
  which is not a total handler, `inputStopping_not_total`). A handler that
  answers a repeated input differently (`repeating`), or one that stops after
  one call (`limited`), makes the two outcomes differ (`repeating_differs`,
  `limited_differs`); neither has the laws (`repeating_inconsistent`,
  `limited_inconsistent`).
- **Extraction from the terminal record.** An adversary queries a transcript
  cell, then a leaf hash whose row depends on the answer. Extraction from the
  terminal record changes when that cell is resampled (`terminal_moves`), so it
  does not respect the checkpoint convention (`terminal_not_frozen`); extraction
  from the record before the cell's first query does not move
  (`frozen_unmoved`).
- **Depth from the proof (security attack).** With one hash function for rows
  and nodes, a verifier that takes the path length from the proof accepts two
  internal digests as a row at depth one, for every hash function
  (`internal_accepted`). In the ideal reading that row is no committed row
  (`internal_not_committed`); the configured depth refuses the path
  (`internal_wrong_depth`). The depth is not fixed at the receive point
  (`depth_not_fixed`).
- **Unbound commitment metadata (security attack).** The deployment
  authenticates the base interpretation of the committed rows. A flawed
  construction binds only the depth and the width (`flawedBinding`) and reads
  the scheme from a runtime parameter the producer supplies. The producer
  commits rows that the base interpretation rejects, so the claim is false
  (`committed_far`), takes the challenge at the flawed key and opens under the
  quartic interpretation: accepted for every challenge and hash function
  (`flawed_accepted`), and with probability one in the random-oracle experiment
  (`flawed_acceptance`). The flawed binding does not fix the scheme
  (`flawedBinding_not_fixed`); the committed-opening protocol's binding does
  (`binding_fixes_scheme`), and under it the same rows are rejected
  (`bound_rejects`).
-/

namespace TestsSecurity.Counterexamples.Openings
open OracleComp OracleSpec ZkcSecurity.FiatShamir ZkcSecurity.FiatShamir.Obligations
open ZkcSecurity.Examples.CommittedOpening
open TestsSecurity.Counterexamples

/-! ### Pruned and unpruned verification under a stateful handler -/

/-- One hash family on one-bit inputs. -/
inductive HashOp where
  | hash (input : Fin 2)

abbrev hashSignature : PIR.Signature where
  Op := HashOp
  Reply
    | .hash _ => Fin 2

/-- Authenticate the same leaf twice. -/
def unpruned (expected : Fin 2) : PIR.Proc hashSignature Bool :=
  .call (.hash 0) fun first => .call (.hash 0) fun second =>
    .done (decide (first = expected ∧ second = expected))

/-- Authenticate it once and reuse the digest. -/
def pruned (expected : Fin 2) : PIR.Proc hashSignature Bool :=
  .call (.hash 0) fun first => .done (decide (first = expected ∧ first = expected))

/-- Under every handler with the hash laws, possibly stopping on an input, the
pruned and unpruned verifiers have the same outcome. -/
theorem lawful_preserves {S E : Type} (handler : PIR.Handler hashSignature S E)
    (lawful : HashLaws (fun _ => True) handler) (expected : Fin 2) (state : S) :
    ((unpruned expected).run handler state).outcome = ((pruned expected).run handler state).outcome := by
  obtain ⟨result, results⟩ := lawful
  have first := results (.hash 0) trivial state
  have second := results (.hash 0) trivial (handler (.hash 0) state).state
  simp only [unpruned, pruned, PIR.Proc.run, PIR.Execution.follow, first]
  rcases outcome : result (.hash 0) with answer | stop
  · simp only [second, outcome]
  · rfl

/-- A handler that answers the first call `0` and every later call `1`. -/
def repeating : PIR.Handler hashSignature ℕ Unit
  | .hash _, calls => ⟨.returned (if calls = 0 then 0 else 1), calls + 1, []⟩

/-- A handler that stops after one call. -/
def limited : PIR.Handler hashSignature ℕ Unit
  | .hash _, calls => if calls = 0 then ⟨.returned 0, 1, []⟩ else ⟨.stopped .exhausted, calls, []⟩

/-- A handler that refuses the input `1` and answers `0` otherwise, whatever its
state: its stop depends on the input alone. -/
def inputStopping : PIR.Handler hashSignature ℕ Unit
  | .hash input, calls =>
      if input = 1 then ⟨.stopped .exhausted, calls + 1, []⟩ else ⟨.returned 0, calls + 1, []⟩

theorem repeating_differs :
    ((unpruned 0).run repeating 0).outcome ≠ ((pruned 0).run repeating 0).outcome := by
  decide

theorem limited_differs :
    ((unpruned 0).run limited 0).outcome ≠ ((pruned 0).run limited 0).outcome := by
  decide

theorem repeating_inconsistent : ¬ HashLaws (fun _ => True) repeating := fun lawful =>
  repeating_differs (lawful_preserves repeating lawful 0 0)

theorem limited_inconsistent : ¬ HashLaws (fun _ => True) limited := fun lawful =>
  limited_differs (lawful_preserves limited lawful 0 0)

/-- An input-determined stop keeps the hash laws. -/
theorem inputStopping_lawful : HashLaws (fun _ => True) inputStopping :=
  ⟨fun | .hash input => if input = 1 then .stopped .exhausted else .returned 0,
    fun | .hash input, _, calls => by
          by_cases refused : input = 1 <;> simp [inputStopping, refused]⟩

/-- It is not a total handler: the total specialization is stronger than the
laws. -/
theorem inputStopping_not_total : ¬ TotalConsistentHandler (fun _ => True) inputStopping := by
  rintro ⟨answer, answers⟩
  have refused := answers (.hash 1) trivial 0
  simp [inputStopping] at refused

/-! ### Extraction from the terminal record -/

abbrev Probe := Query Unit Unit (List Bool) Bool

/-- The transcript cell: a request of one bit. -/
def cell : List (Event Unit Unit (List Bool) Bool) := [.position 1]

/-- Query the cell, then hash a row that depends on its answer. -/
def arranging : OracleComp (spec Unit Unit (List Bool) Bool) Bool := do
  let answer ← liftM ((spec Unit Unit (List Bool) Bool).query (.transcript cell))
  liftM ((spec Unit Unit (List Bool) Bool).query (.hash (.leaf [decide (answer.val = 0)])))

/-- The rows of the leaf hashes in a record: what an extractor reads. -/
def seenRows (record : Record Unit Unit (List Bool) Bool) : List (List Bool) :=
  record.filterMap fun entry =>
    match entry.1 with
    | .hash (.leaf row) => some row
    | _ => none

/-- Answer tables in which the cell answers `0` and every leaf hash `false`. -/
def answers : (query : Probe) → Range query
  | .transcript _ => 0
  | .hash _ => false

/-- The resampled answer at the cell. -/
def resampled : Range (Query.transcript (Context := Unit) (Scheme := Unit) (Row := List Bool)
    (Digest := Bool) cell) := ⟨1, by decide⟩

theorem terminal_moves :
    seenRows (tableQueryLog arranging (Function.update answers (.transcript cell) resampled)) ≠
      seenRows (tableQueryLog arranging answers) := by
  simp [arranging, seenRows, answers, resampled]

/-- Extraction from the terminal record does not respect the checkpoint
convention at the cell. -/
theorem terminal_not_frozen : ¬ FrozenAt cell seenRows := by
  intro frozen
  apply terminal_moves
  apply frozen
  rw [beforeFirst_update]

/-- Extraction from the record before the cell's first query does not move. -/
theorem frozen_unmoved :
    seenRows (beforeFirst cell
        (tableQueryLog arranging (Function.update answers (.transcript cell) resampled))) =
      seenRows (beforeFirst cell (tableQueryLog arranging answers)) := by
  rw [beforeFirst_update]

/-! ### Depth from the proof -/

/-- One hash function for rows and nodes: a row is a pair of digests. -/
def shared {Digest : Type} (hash : Digest × Digest → Digest) :
    HashCall (Digest × Digest) Digest → Digest
  | .leaf row => hash row
  | .node left right => hash (left, right)

/-- A table of four rows. -/
def committed {Digest : Type} (rows : Fin 4 → Digest × Digest) : PTree (Digest × Digest) 2 :=
  .node (.node (.leaf (rows 0)) (.leaf (rows 1))) (.node (.leaf (rows 2)) (.leaf (rows 3)))

/-- The two leaf digests below the first internal node, presented as a row. -/
def internalRow {Digest : Type} (hash : Digest × Digest → Digest) (rows : Fin 4 → Digest × Digest) :
    Digest × Digest :=
  (hash (rows 0), hash (rows 1))

/-- The path of length one: the right subtree's root. -/
def internalPath {Digest : Type} (hash : Digest × Digest → Digest) (rows : Fin 4 → Digest × Digest) :
    List Digest :=
  [hash (hash (rows 2), hash (rows 3))]

/-- For every hash function, climbing the one-level path from the internal row
reaches the committed root. -/
theorem internal_accepted {Digest : Type} (hash : Digest × Digest → Digest)
    (rows : Fin 4 → Digest × Digest) :
    climb (shared hash) 0 (internalPath hash rows) (shared hash (.leaf (internalRow hash rows))) =
      root (shared hash) (committed rows) :=
  rfl

/-- Every row of the table is one of its four rows. -/
theorem committed_get {Digest : Type} (rows : Fin 4 → Digest × Digest) (index : ℕ) :
    ∃ position, (committed rows).get index = rows position := by
  simp only [committed, PTree.get]
  split_ifs <;> exact ⟨_, rfl⟩

/-- In the ideal reading, with the tree of committed rows as carrier, the
accepted row is no committed row. -/
theorem internal_not_committed (values : Fin 4 → Bool × Bool) (index : ℕ) :
    internalRow (fun pair => Carrier.node pair.1 pair.2)
        (fun position => (Carrier.leaf (values position).1, Carrier.leaf (values position).2)) ≠
      (committed fun position =>
        (Carrier.leaf (values position).1, Carrier.leaf (values position).2)).get index := by
  obtain ⟨position, row⟩ := committed_get
    (fun position => (Carrier.leaf (values position).1, Carrier.leaf (values position).2)) index
  rw [row]
  intro same
  have first := congrArg Prod.fst same
  simp [internalRow] at first

/-- The configured depth is two; the attack's path has length one. -/
theorem internal_wrong_depth {Digest : Type} (hash : Digest × Digest → Digest)
    (rows : Fin 4 → Digest × Digest) : (internalPath hash rows).length ≠ 2 := by
  simp [internalPath]

/-- The depth the verifier uses is the received path's length, which the
absorbed root does not fix. -/
theorem depth_not_fixed :
    ¬ FixedAtReceivePoint (fun _ : List Bool => ()) List.length :=
  not_determines (first := []) (second := [true]) rfl (by decide)

/-! ### Unbound commitment metadata -/

abbrev Coordinate := ZMod 5

abbrev Digest := Fin 4

/-- The scheme reads a row of four coordinates as four base elements (`false`)
or as one quartic element (`true`). The base reading accepts a row whose first
coordinate is zero; the quartic reading accepts a nonzero element. -/
def accepts : Bool → List Coordinate → Bool
  | false, row => decide (row.headD 1 = 0)
  | true, row => decide (row ≠ [0, 0, 0, 0])

/-- The authenticated intended configuration: the base interpretation. -/
def intended : Configuration Bool := ⟨false, 1, 4⟩

/-- Both committed rows are the coordinates `1, 0, 0, 0`. -/
def rows : PTree (List Coordinate) 1 := .node (.leaf [1, 0, 0, 0]) (.leaf [1, 0, 0, 0])

theorem rows_get (index : ℕ) : rows.get index = [1, 0, 0, 0] := by
  simp only [rows, PTree.get]
  split <;> rfl

theorem rows_width (index : ℕ) : (rows.get index).length = 4 := by
  rw [rows_get]
  rfl

/-- Under the intended interpretation every committed row is rejected: the claim
that the committed table is acceptable is false, at fraction one. -/
theorem committed_far : Far accepts intended 1 (some fun index => rows.get index.val) := by
  show (1 : ENNReal) * 2 ^ 1 ≤ ((Finset.univ.filter fun index : Fin (2 ^ 1) =>
    accepts false (rows.get index.val) = false).card : ENNReal)
  have count : (Finset.univ.filter fun index : Fin (2 ^ 1) =>
      accepts false (rows.get index.val) = false).card = 2 := by
    decide
  rw [count]
  norm_num

/-- The flawed binding records the depth and the width; the scheme is not part
of the transcript. -/
def flawedBinding (configuration : Configuration Bool) : Configuration Unit :=
  ⟨(), configuration.depth, configuration.width⟩

/-- The flawed construction's initial history. -/
def flawedInitial (configuration : Configuration Bool) : List (Event Unit Unit (List Coordinate) Digest) :=
  [.binding () (flawedBinding configuration)]

/-- The flawed verifier: the intended depth and width, and the scheme the
producer supplies as a runtime parameter. -/
def flawedVerifier (scheme : Bool) : PIR.Proc (signature (List Coordinate) Digest) Bool :=
  verifier accepts ⟨scheme, intended.depth, intended.width⟩

/-- The flawed construction's key for a root. -/
def flawedKey (rootValue : Digest) : List (Event Unit Unit (List Coordinate) Digest) :=
  flawedInitial intended ++ [.root rootValue] ++ [.position intended.depth]

/-- The producer's proof in the concrete reading: the root of the rows, the
opening at the challenge of the flawed key, and the quartic interpretation. -/
def flawedProof (challenge : (key : List (Event Unit Unit (List Coordinate) Digest)) → Answer key)
    (hash : HashCall (List Coordinate) Digest → Digest) : Bool × List (Message (List Coordinate) Digest) :=
  let index := decodeIndex intended.depth (challenge (flawedKey (root hash rows)))
  (true, [.root (root hash rows), .opening (rows.get index.val) (path hash rows index.val)])

/-- For every challenge and hash function, the flawed construction accepts the
false claim. -/
theorem flawed_accepted (challenge : (key : List (Event Unit Unit (List Coordinate) Digest)) → Answer key)
    (hash : HashCall (List Coordinate) Digest → Digest) (absorbOpening : Bool) :
    (interpret (m := Id) (concreteOracle challenge hash) absorbOpening
        (flawedVerifier (flawedProof challenge hash).1) (flawedInitial intended)
        (flawedProof challenge hash).2).1 = .returned true := by
  refine (congrArg Prod.fst (interpret_verifier_from (concreteOracle challenge hash) absorbOpening
    accepts ⟨true, intended.depth, intended.width⟩ (flawedInitial intended) _ _ _ [])).trans ?_
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by
    exact ⟨rows_width _, path_length _ _ _, climb_path _ _ _ (Fin.isLt _)⟩)), rows_get]
  rfl

/-- The producer with oracle access: commit, take the challenge at the flawed
key, open, and claim the quartic interpretation. -/
def flawedProver :
    OracleComp (spec Unit Unit (List Coordinate) Digest) (Bool × List (Message (List Coordinate) Digest)) := do
  let rootValue ← rootQueries rows
  let raw ← liftM ((spec Unit Unit (List Coordinate) Digest).query (.transcript (flawedKey rootValue)))
  let index := decodeIndex intended.depth raw
  let siblings ← pathQueries rows index.val
  pure (true, [.root rootValue, .opening (rows.get index.val) siblings])

/-- The flawed experiment: the producer, then the flawed verifier with the
scheme it supplied, in one oracle. -/
def flawedExperiment (absorbOpening : Bool) :
    OracleComp (spec Unit Unit (List Coordinate) Digest)
      (Bool × (PIR.Outcome Bool × List (Message (List Coordinate) Digest))) :=
  flawedProver >>= fun claimed => (claimed.1, ·) <$>
    oracleReading absorbOpening (flawedVerifier claimed.1) (flawedInitial intended) claimed.2

/-- The false claim is accepted with probability one. -/
theorem flawed_acceptance (absorbOpening : Bool) :
    Pr{let result ← (simulateQ randomOracle (flawedExperiment absorbOpening)).run' ∅}[
      result.2.1 = PIR.Outcome.returned true] = 1 := by
  refine prEvent_randomOracle_eq_one _ _ fun answers => ?_
  simp only [flawedExperiment, flawedProver, evalWithAnswerFn_bind, evalWithAnswerFn_map,
    evalWithAnswerFn_liftM_query, evalWithAnswerFn_pathQueries, evalWithAnswerFn_pure,
    evalWithAnswerFn_interpret]
  rw [evalWithAnswerFn_rootQueries]
  refine (congrArg Prod.fst (interpret_verifier_from (fun query => answers query) absorbOpening
    accepts ⟨true, intended.depth, intended.width⟩ (flawedInitial intended) _ _ _ [])).trans ?_
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by
    exact ⟨rows_width _, path_length _ _ _, climb_path _ _ _ (Fin.isLt _)⟩)), rows_get]
  rfl

/-- The base and quartic configurations have one flawed binding but different
schemes: the flawed binding does not fix the scheme. -/
theorem flawedBinding_not_fixed : ¬ FixedAtReceivePoint flawedBinding Configuration.scheme :=
  not_determines (first := intended) (second := ⟨true, 1, 4⟩) rfl (by decide)

/-- The committed-opening protocol's binding determines the scheme. -/
theorem binding_fixes_scheme :
    FixedAtReceivePoint (fun configuration : Configuration Bool =>
      (initial () configuration : List (Event Unit Bool (List Coordinate) Digest)))
      Configuration.scheme := by
  intro first second same
  simp only [initial, List.cons.injEq, Event.binding.injEq, true_and, and_true] at same
  rw [same]

/-- With the scheme bound and authenticated, the honest proof of the same rows
is rejected under the intended interpretation, for every challenge and hash
function. -/
theorem bound_rejects (challenge : (key : List (Event Unit Bool (List Coordinate) Digest)) → Answer key)
    (hash : HashCall (List Coordinate) Digest → Digest) (absorbOpening : Bool) :
    interpret (m := Id) (concreteOracle challenge hash) absorbOpening (verifier accepts intended)
        (initial () intended) (honestProof challenge hash () intended rows) =
      (.returned false, []) := by
  rw [concrete_honest accepts challenge hash absorbOpening () intended rows rows_width]
  exact congrArg (fun row => (PIR.Outcome.returned (accepts false row),
    ([] : List (Message (List Coordinate) Digest)))) (rows_get _)

end TestsSecurity.Counterexamples.Openings
