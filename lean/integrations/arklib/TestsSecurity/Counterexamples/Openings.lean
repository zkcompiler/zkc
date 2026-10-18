import ZkcSecurity.FiatShamir.Obligations
import ZkcSecurity.Examples.CommittedOpening
import TestsSecurity.Counterexamples.Support
import Mathlib.Data.ZMod.Basic

/-! Counterexamples for commitment openings and hash effects.

- **Pruned and unpruned verification under a stateful handler.** A verifier that
  hashes the same leaf twice and its pruned form that hashes it once return the
  same outcome under every handler with the hash-consistency and failure laws
  (`consistent_preserves`). A handler that answers a repeated input differently
  (`repeating`), or one that stops after one call (`limited`), makes the two
  outcomes differ (`repeating_differs`, `limited_differs`); neither has the laws
  (`repeating_inconsistent`, `limited_inconsistent`).
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
- **Unbound commitment metadata (security attack).** The committed-opening
  protocol with the scheme identity unbound: one root of rows read under the base
  interpretation (all rows rejected, so the extracted table is far,
  `base_far`) and under the quartic interpretation (accepted for every
  challenge and hash function, `quartic_accepted`). A binding of the depth and
  width alone does not fix the scheme (`scheme_not_fixed`), and gives both
  configurations one key (`unbound_key`).
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

theorem consistent_preserves {S E : Type} (handler : PIR.Handler hashSignature S E)
    (consistent : ConsistentHandler (fun _ => True) handler) (expected : Fin 2) (state : S) :
    ((unpruned expected).run handler state).outcome = ((pruned expected).run handler state).outcome := by
  obtain ⟨answer, answers⟩ := consistent
  have first := answers (.hash 0) trivial state
  simp only [unpruned, pruned, PIR.Proc.run, PIR.Execution.follow, first]
  have second := answers (.hash 0) trivial (handler (.hash 0) state).state
  simp only [second]

/-- A handler that answers the first call `0` and every later call `1`. -/
def repeating : PIR.Handler hashSignature ℕ Unit
  | .hash _, calls => ⟨.returned (if calls = 0 then 0 else 1), calls + 1, []⟩

/-- A handler that stops after one call. -/
def limited : PIR.Handler hashSignature ℕ Unit
  | .hash _, calls => if calls = 0 then ⟨.returned 0, 1, []⟩ else ⟨.stopped .exhausted, calls, []⟩

theorem repeating_differs :
    ((unpruned 0).run repeating 0).outcome ≠ ((pruned 0).run repeating 0).outcome := by
  decide

theorem limited_differs :
    ((unpruned 0).run limited 0).outcome ≠ ((pruned 0).run limited 0).outcome := by
  decide

theorem repeating_inconsistent : ¬ ConsistentHandler (fun _ => True) repeating := fun consistent =>
  repeating_differs (consistent_preserves repeating consistent 0 0)

theorem limited_inconsistent : ¬ ConsistentHandler (fun _ => True) limited := fun consistent =>
  limited_differs (consistent_preserves limited consistent 0 0)

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

/-- The scheme reads a row of four coordinates as four base elements (`false`)
or as one quartic element (`true`). The base reading accepts a row whose first
coordinate is zero; the quartic reading accepts a nonzero element. -/
def accepts : Bool → List Coordinate → Bool
  | false, row => decide (row.headD 1 = 0)
  | true, row => decide (row ≠ [0, 0, 0, 0])

def base : Configuration Bool := ⟨false, 1, 4⟩

def quartic : Configuration Bool := ⟨true, 1, 4⟩

/-- Both rows are the coordinates `1, 0, 0, 0`. -/
def rows : PTree (List Coordinate) 1 := .node (.leaf [1, 0, 0, 0]) (.leaf [1, 0, 0, 0])

theorem rows_get (index : ℕ) : rows.get index = [1, 0, 0, 0] := by
  simp only [rows, PTree.get]
  split <;> rfl

theorem rows_width (index : ℕ) : (rows.get index).length = 4 := by
  rw [rows_get]
  rfl

/-- Under the quartic configuration the honest proof of the rows is accepted,
for every challenge and hash function. -/
theorem quartic_accepted {Digest : Type} [DecidableEq Digest]
    (challenge : (key : List (Event Unit Bool (List Coordinate) Digest)) → Answer key)
    (hash : HashCall (List Coordinate) Digest → Digest) (absorbOpening : Bool) :
    interpret (m := Id) (concreteOracle challenge hash) absorbOpening (verifier accepts quartic)
        (initial () quartic) (honestProof challenge hash () quartic rows) =
      (.returned true, []) := by
  rw [concrete_honest accepts challenge hash absorbOpening () quartic rows rows_width]
  exact congrArg (fun row => (PIR.Outcome.returned (accepts true row),
    ([] : List (Message (List Coordinate) Digest)))) (rows_get _)

/-- Under the base configuration every row is rejected, so the table is far at
fraction one. -/
theorem base_far : Far accepts base 1 (some fun index => rows.get index.val) := by
  show (1 : ENNReal) * 2 ^ 1 ≤ ((Finset.univ.filter fun index : Fin (2 ^ 1) =>
    accepts false (rows.get index.val) = false).card : ENNReal)
  have count : (Finset.univ.filter fun index : Fin (2 ^ 1) =>
      accepts false (rows.get index.val) = false).card = 2 := by
    decide
  rw [count]
  norm_num

/-- A binding of the depth and width alone. -/
def shape (configuration : Configuration Bool) : ℕ × ℕ := (configuration.depth, configuration.width)

theorem unbound_key : shape base = shape quartic := rfl

/-- The scheme is not fixed by a binding of the depth and width. -/
theorem scheme_not_fixed : ¬ FixedAtReceivePoint shape Configuration.scheme :=
  not_determines unbound_key (by decide)

end TestsSecurity.Counterexamples.Openings
