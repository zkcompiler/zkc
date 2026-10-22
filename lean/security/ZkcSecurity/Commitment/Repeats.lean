module

public import ZkcSecurity.VCVio.Memo
public import ZkcSecurity.Commitment.Soundness
public import ZkcSecurity.Commitment.HashedLeaves
public import ZkcSecurity.Commitment.Charges

@[expose] public section

/-! # Repeated prover queries and checkpoint extraction

A provider simulation answers a prover's repeated calls from its record, so the translated prover
asks each key once: its log is the first occurrence of each key in the original prover's log
(`ZkcSecurity.VCVio.Memo`). The bridge's event reads the prover's log through checkpoint
extractions, so a simulation composes with the bridge when extraction does not see repeated
entries.

An extractor reads its record through first matches (`Extractable.FirstMatch`) when records
with the same first match for every predicate extract the same tables. The extractor of Merkle
trees with hashed leaves does (`LeafHashing.scheme_firstMatch`), and so does every scheme read
through a map of shapes (`Extractable.comap_firstMatch`). The hash calls before a transcript key's
first query are read through first matches of the whole log
(`find?_hashEntries_beforeFirst`), and dropping repeated prover entries keeps every first match
when the prover's log agrees with a cache, so for such extractors the checkpoint tables
(`checkpointTables_unseen`) and the bridge's event (`falseAcceptance_unseen`) are unchanged.
Hence the bridge's event is at most as likely for a prover as for its memoized version
(`falseAcceptance_le_memo`), against the lazily sampled joint oracle.
-/

set_option autoImplicit false

namespace ZkcSecurity.Commitment
open OracleComp OracleSpec ZkcSecurity.FiatShamir ZkcSecurity.VCVio.Memo
open OracleComp.ProgramLogic.Relational

section FirstMatch
variable {Shape Value Query Y : Type}

/-- An extractor that reads a record only through first matches: records with the same first
match for every predicate extract the same tables. -/
def Extractable.FirstMatch (scheme : Extractable Shape Value Query Y) : Prop :=
  ∀ log other : HashLog Query Y, (∀ match? : ((_ : Query) × Y) → Bool,
    log.find? match? = other.find? match?) → scheme.extract log = scheme.extract other

theorem Extractable.comap_firstMatch {Shape' : Type} (scheme : Extractable Shape Value Query Y)
    (firstMatch : scheme.FirstMatch) (shapeOf : Shape' → Shape) :
    (scheme.comap shapeOf).FirstMatch := by
  intro log other same
  funext shape
  exact congrFun (firstMatch log other same) (shapeOf shape)

variable {Row : Type} [DecidableEq Y] (model : LeafHashing Row Query Y)

theorem LeafHashing.extract_firstMatch (log other : HashLog Query Y)
    (same : ∀ match? : ((_ : Query) × Y) → Bool, log.find? match? = other.find? match?) :
    model.extract log = model.extract other := by
  have children : ∀ label, model.findChildren log label = model.findChildren other label :=
    fun label => by simp only [LeafHashing.findChildren, same]
  have rows : ∀ label, model.findRow log label = model.findRow other label :=
    fun label => by simp only [LeafHashing.findRow, same]
  have labels : ∀ depth label index,
      model.extractLabel log depth label index = model.extractLabel other depth label index := by
    intro depth
    induction depth with
    | zero => intro label index; rfl
    | succ depth ih =>
        intro label index
        simp only [LeafHashing.extractLabel, children, ih]
  funext depth root index
  simp only [LeafHashing.extract, labels, rows]

/-- Merkle trees with hashed leaves extract through first matches. -/
theorem LeafHashing.scheme_firstMatch : model.scheme.FirstMatch :=
  model.extract_firstMatch

end FirstMatch

section Logs
variable {J : PIR.Signature} {E Shape Value Y Query Stmt : Type} {Raw : E → Type} [DecidableEq E]
  [DecidableEq Shape]
  [DecidableEq Y] [DecidableEq Query]

/-- A joint entry read as a hash call, if it is one. -/
def hashCallOf (entry : (key : JointKey E Shape Y Query) × JointRange Raw Shape Y Query key) :
    Option ((_ : Query) × Y) :=
  match entry with
  | ⟨.inr query, answer⟩ => some ⟨query, answer⟩
  | ⟨.inl _, _⟩ => none

/-- The first match among the hash calls before a key's first query, as a first match of the
whole log. -/
theorem find?_hashEntries_beforeFirst (key : TranscriptKey E Shape Y)
    (match? : ((_ : Query) × Y) → Bool) :
    ∀ log : QueryLog (joint Raw Shape Y Query),
      (hashEntries (beforeFirst (.inl key) log)).find? match? =
        (log.find? fun entry => decide (entry.1 = .inl key) ||
          ((hashCallOf entry).map match?).getD false).bind hashCallOf
  | [] => rfl
  | ⟨first, answer⟩ :: rest => by
      rw [beforeFirst_cons, List.find?_cons]
      by_cases here : first = .inl key
      · subst here
        simp [hashEntries, hashCallOf]
      · cases first with
        | inl other =>
            have tail := find?_hashEntries_beforeFirst key match? rest
            simp only [here, ↓reduceIte, hashEntries, List.filterMap_cons] at tail ⊢
            simp only [hashCallOf, Option.map_none, Option.getD_none, decide_false,
              Bool.or_false]
            exact tail
        | inr query =>
            have tail := find?_hashEntries_beforeFirst key match? rest
            simp only [here, ↓reduceIte, hashEntries, List.filterMap_cons] at tail ⊢
            simp only [hashCallOf, Option.map_some, Option.getD_some, decide_false,
              Bool.false_or, List.find?_cons]
            cases match? ⟨query, answer⟩ with
            | true => rfl
            | false => exact tail

variable (words : Words J Shape Value) (scheme : Extractable Shape Value Query Y)
  (statementRoots : Stmt → List (Shape × Y))

/-- Dropping the prover's repeated entries leaves the checkpoint tables unchanged, for an
extractor that reads first matches and a prover log that agrees with a cache. -/
theorem checkpointTables_unseen (firstMatch : scheme.FirstMatch)
    (log rest : QueryLog (joint Raw Shape Y Query))
    (cache : (joint Raw Shape Y Query).QueryCache)
    (agree : ∀ entry ∈ log, cache entry.1 = some entry.2) (key : TranscriptKey E Shape Y)
    (statement : Stmt) :
    checkpointTables words scheme statementRoots (unseen ∅ log ++ rest) key statement =
      checkpointTables words scheme statementRoots (log ++ rest) key statement := by
  unfold checkpointTables
  have same : scheme.extract (hashEntries (beforeFirst (.inl key) (unseen ∅ log ++ rest))) =
      scheme.extract (hashEntries (beforeFirst (.inl key) (log ++ rest))) := by
    refine firstMatch _ _ fun match? => ?_
    rw [find?_hashEntries_beforeFirst, find?_hashEntries_beforeFirst,
      find?_unseen_append _ cache rest log ∅ (fun _ _ found => by cases found)
        (fun _ _ found => by cases found) agree]
  simp only [normalized, same]

/-- Dropping the prover's repeated entries leaves the bridge's event unchanged, for an extractor
that reads first matches and a prover log that agrees with a cache. -/
theorem falseAcceptance_unseen {P A : Type} (firstMatch : scheme.FirstMatch)
    (falseStatement : Stmt → List (Table Value) → Prop) (accepts : A → Prop)
    (result : JointRun Stmt P Value Y A (QueryLog (joint Raw Shape Y Query)))
    (cache : (joint Raw Shape Y Query).QueryCache)
    (agree : ∀ entry ∈ result.proverLog, cache entry.1 = some entry.2) :
    FalseAcceptance words scheme statementRoots falseStatement accepts
        { result with proverLog := unseen ∅ result.proverLog } ↔
      FalseAcceptance words scheme statementRoots falseStatement accepts result := by
  unfold FalseAcceptance
  simp only [checkpointTables_unseen words scheme statementRoots firstMatch result.proverLog
    result.verifierLog cache agree]

section Memo
variable [∀ key, SampleableType (Raw key)] [SampleableType Y]

/-- The bridge's event is at most as likely for a prover as for its memoized version, which asks
each key once, for an extractor that reads first matches. -/
theorem falseAcceptance_le_memo {P A : Type} (absorb : Typed.Interface J E P Raw)
    (firstMatch : scheme.FirstMatch) (verifier : Stmt → PIR.Process (committed J Shape Value) A)
    (initial : Stmt → List (Absorbed E Shape Y)) (falseStatement : Stmt → List (Table Value) → Prop)
    (accepts : A → Prop)
    (prover : OracleComp (joint Raw Shape Y Query) (Stmt × Proof P Value Y)) :
    Pr{let result ← (simulateQ randomOracle
        (experiment absorb scheme verifier initial statementRoots prover)).run' ∅}[
      FalseAcceptance words scheme statementRoots falseStatement accepts result] ≤
      Pr{let result ← (simulateQ randomOracle (experiment absorb scheme verifier initial
          statementRoots (Prod.fst <$> (simulateQ memoImpl prover).run ∅))).run' ∅}[
        FalseAcceptance words scheme statementRoots falseStatement accepts result] := by
  let continuation : Stmt × Proof P Value Y →
      OracleComp (joint Raw Shape Y Query) (PIR.Outcome A × QueryLog (joint Raw Shape Y Query)) :=
    fun claim => (run absorb scheme (verifier claim.1) (initial claim.1) (statementRoots claim.1)
      claim.2.messages claim.2.openings).withQueryLog
  let assemble : Stmt × Proof P Value Y → QueryLog (joint Raw Shape Y Query) →
      PIR.Outcome A × QueryLog (joint Raw Shape Y Query) →
        JointRun Stmt P Value Y A (QueryLog (joint Raw Shape Y Query)) :=
    fun claim log verifierRun => ⟨claim.1, claim.2, verifierRun.1, log, verifierRun.2⟩
  have shape : ∀ prover : OracleComp (joint Raw Shape Y Query) (Stmt × Proof P Value Y),
      experiment absorb scheme verifier initial statementRoots prover =
        prover.withQueryLog >>= fun proverRun =>
          assemble proverRun.1 proverRun.2 <$> continuation proverRun.1 := by
    intro prover
    unfold experiment
    simp only [map_eq_bind_pure_comp, Function.comp_def]
    rfl
  rw [shape, shape]
  refine prEvent_le_of_relTriple (experiment_coupling prover continuation assemble) ?_
  rintro direct memo ⟨claim, log, rest, cache, rfl, rfl, agree⟩ holds
  exact (falseAcceptance_unseen words scheme statementRoots firstMatch falseStatement accepts
    (assemble claim log rest) cache agree).mpr holds

end Memo

end Logs

end ZkcSecurity.Commitment
