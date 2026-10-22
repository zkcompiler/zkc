module

public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshQuery
public import VCVio.CryptoFoundations.MerkleTree.Extractor

@[expose] public section

/-! # Table commitments with straight-line extraction

A verifier with committed oracle messages sees a commitment (a root) where the ideal protocol has
a table in the clear, and later reads single entries of that table through openings that it
authenticates with a hash oracle `Query →ₒ Y`. The security argument replaces every root by the
table that an extractor reads from the record of hash calls (`HashLog`).

`Extractable` states what the argument needs of such a scheme, as two deterministic laws about
the extractor:

* `opening_agrees`: an opening accepted by hash calls that are all recorded in a record without
  two calls answered alike (`ResponseInjectiveOn`) agrees with the table extracted from that
  record;
* `extract_append`: recording one more call changes an extraction only when the call is new to the
  record and its answer is the root, or a label that an earlier recorded call took as input
  (`inputs`).

Both laws are statements about records, not probabilities. The joint security argument charges
every hash call whose answer repeats an earlier answer, the root of an earlier checkpoint or an
earlier input; outside that event the laws make the extracted tables stable and the openings
consistent with them. `ZkcSecurity.Commitment.Merkle` proves both laws for Merkle trees with
VCVio's transcript extractor.
-/

set_option autoImplicit false

namespace ZkcSecurity.Commitment

open OracleComp OracleSpec

/-- A table of committed entries by position: `none` where nothing is committed or extracted. -/
abbrev Table (Value : Type) := ℕ → Option Value

/-- A record of hash calls in call order. -/
abbrev HashLog (Query Y : Type) := MerkleTreeExtractor.QueryLog Query Y

/-- An opening of one table position: the claimed entry and its authentication path. -/
structure Opening (Value Y : Type) where
  value : Value
  path : List Y

/-- A commitment scheme for tables over the hash oracle `Query →ₒ Y` with a straight-line
extractor that reads the record of hash calls. A commitment has a shape, which fixes how its
tables are authenticated (for Merkle trees, the height and the position-to-address map). -/
structure Extractable (Shape Value Query Y : Type) where
  /-- Authenticate an opening of `position` against `root`, through hash calls. -/
  authenticate : Shape → Y → ℕ → Opening Value Y → OracleComp (Query →ₒ Y) Bool
  /-- The table committed by `root`, as extracted from a record of hash calls. -/
  extract : HashLog Query Y → Shape → Y → Table Value
  /-- The labels a hash call takes as input. -/
  inputs : Query → List Y
  /-- An opening accepted by recorded hash calls agrees with the extraction from a record without
  two calls answered alike. -/
  opening_agrees : ∀ (answer : Query → Y) (log : HashLog Query Y) (shape : Shape) (root : Y)
    (position : ℕ) (opening : Opening Value Y),
    MerkleTreeExtractor.ResponseInjectiveOn log →
    (∀ entry ∈ tableQueryLog (authenticate shape root position opening) answer, entry ∈ log) →
    evalWithAnswerFn (QueryImpl.ofFn answer) (authenticate shape root position opening) = true →
    extract log shape root position = some opening.value
  /-- Recording one more call changes an extraction only when the call is new and its answer is
  the root or an earlier recorded input. -/
  extract_append : ∀ (log : HashLog Query Y) (entry : (_ : Query) × Y) (shape : Shape) (root : Y),
    extract (log ++ [entry]) shape root ≠ extract log shape root →
      entry ∉ log ∧ (entry.2 = root ∨ ∃ recorded ∈ log, entry.2 ∈ inputs recorded.1)

end ZkcSecurity.Commitment
