module

public import ZkcSecurity.Stage.FiatShamir
public import ZkcSecurity.Commitment.Soundness

@[expose] public section

/-! # The commitment bridge as a stage

The joint game of a verifier that sees roots and openings (`jointGame`): provers are oracle
computations on the joint oracle of transcript keys and hash calls that output a statement and a
proof, admissible at `q` with at most `q` queries on every path; the bad event is
`ZkcSecurity.Commitment.FalseAcceptance`, acceptance while the statement is false for its tables
extracted at the checkpoint of one of the verifier's transcript queries.

The bridge from the ideal reading, which receives every committed table in the clear, to the
concrete reading, which sees roots and openings, does not translate one adversary class into
another: the ideal reading enters as a certificate, and `ZkcSecurity.Commitment.soundness` bounds
the joint game. Its stage is therefore a relation from the trivial game (`commitmentRelation`),
whose loss at `q` prover queries is `q · (siteBound + hashCharge q) + verifierCost q`: every key
the prover asks is charged at most the certificate's largest site error plus the hash charge
`hashCharge q = (rootBound + inputBound + 1) · (q + verifierQueries) / |Y|`, and the verifier's
own keys at most `verifierCost q`.

The bridge changes the statement interpretation: its bad event reads the statement's tables
through the extraction at a checkpoint, the hash calls before the first query of one of the
verifier's transcript keys. That extraction is frozen once the key is queried
(`checkpointTables_append`), and the event needs a transcript query of the verifier: it is false
when the verifier queries nothing (`not_falseAcceptance_of_verifierLog_nil`). A stage after the
bridge that is about an intended application event therefore needs that event to imply this one
(`ZkcSecurity.Stage.Joint.Contract.implies`).
-/

set_option autoImplicit false

namespace ZkcSecurity.Stage
open OracleComp OracleSpec ZkcSecurity.FiatShamir ZkcSecurity.Commitment

variable {J : PIR.Signature} {E P Shape Value Query Y A Stmt : Type} {Raw : E → Type}
variable [DecidableEq E] [DecidableEq Shape] [DecidableEq Y] [DecidableEq Query]

section Interpretation
variable (words : Words J Shape Value) (scheme : Extractable Shape Value Query Y)
  (statementRoots : Stmt → List (Shape × Y))

/-- The tables extracted at a transcript key's checkpoint do not change once the key has been
queried. -/
theorem checkpointTables_append (log later : QueryLog (joint Raw Shape Y Query))
    (key : TranscriptKey E Shape Y) (statement : Stmt) (queried : ∃ entry ∈ log, entry.1 = .inl key) :
    checkpointTables words scheme statementRoots (log ++ later) key statement =
      checkpointTables words scheme statementRoots log key statement := by
  simp only [checkpointTables, beforeFirst_append_of_mem _ later log queried]

/-- The bridge's event needs a transcript query of the verifier: it is false when the verifier
queries nothing. -/
theorem not_falseAcceptance_of_verifierLog_nil (falseStatement : Stmt → List (Table Value) → Prop)
    (accepts : A → Prop)
    (result : JointRun Stmt P Value Y A (QueryLog (joint Raw Shape Y Query)))
    (empty : result.verifierLog = []) :
    ¬ FalseAcceptance words scheme statementRoots falseStatement accepts result := by
  rintro ⟨_, entry, member, _⟩
  rw [empty] at member
  exact List.not_mem_nil member

end Interpretation

variable [∀ key, SampleableType (Raw key)] [SampleableType Y]

/-- The joint game of a verifier that sees roots and openings: provers on the joint oracle,
admissible at their total query count; the bad event is a false acceptance at a checkpoint. -/
noncomputable def jointGame (absorb : Typed.Interface J E P Raw) (words : Words J Shape Value)
    (scheme : Extractable Shape Value Query Y) (verifier : Stmt → PIR.Proc (committed J Shape Value) A)
    (initial : Stmt → List (Absorbed E Shape Y)) (statementRoots : Stmt → List (Shape × Y))
    (falseStatement : Stmt → List (Table Value) → Prop) (accepts : A → Prop) : Game :=
  oracleGame (JointRange Raw Shape Y Query)
    (OracleComp (joint Raw Shape Y Query) (Stmt × Proof P Value Y)) ℕ
    (fun queries prover => IsTotalQueryBound prover queries)
    (experiment absorb scheme verifier initial statementRoots)
    (FalseAcceptance words scheme statementRoots falseStatement accepts)

/-- The charge of a hash call when the prover makes at most `queries` queries and the verifier
at most `verifierQueries`: `(rootBound + inputBound + 1) · (queries + verifierQueries) / |Y|`. -/
noncomputable def hashCharge (Y : Type) [Fintype Y] (rootBound inputBound verifierQueries queries : ℕ) :
    ENNReal :=
  (((rootBound + inputBound + 1) * (queries + verifierQueries) : ℕ) : ENNReal) / Fintype.card Y

variable [Fintype Y]

/-- The commitment bridge as a stage from the trivial game: with every site error of the ideal
reading's certificate at most `siteBound`, the loss at `q` prover queries is
`q · (siteBound + hashCharge q) + verifierCost q`. -/
noncomputable def commitmentRelation (absorb : Typed.Interface J E P Raw) (words : Words J Shape Value)
    (scheme : Extractable Shape Value Query Y) (verifier : Stmt → PIR.Proc (committed J Shape Value) A)
    (initial : Stmt → List (Absorbed E Shape Y)) (statementRoots : Stmt → List (Shape × Y))
    {accepts : A → Prop} {error : E → ENNReal} (certificate : Typed.Certificate absorb accepts error)
    {siteBound : ENNReal} (bounded : ∀ event, error event ≤ siteBound)
    (commitReceives : ∀ shape, ∃ event recover, absorb (words.word shape) = .receive event recover)
    (carries : ∀ log shape root position value, scheme.extract log shape root position = some value →
      normalized words (scheme.extract log) shape root position = some value)
    (determined : Typed.Determined initial)
    (initialRoots : ∀ statement,
      (initial statement).filterMap Absorbed.committed = statementRoots statement)
    (rootBound : ℕ)
    (statementBound : ∀ statement, (statementRoots statement).length ≤ rootBound)
    (commitBound : ∀ statement,
      CommitBound (verifier statement) (rootBound - (statementRoots statement).length))
    (falseStatement : Stmt → List (Table Value) → Prop)
    (doomedValidator : ∀ statement tables, falseStatement statement tables →
      certificate.doomed (withTables words tables (verifier statement)))
    (inputBound : ℕ) (inputs : ∀ query, (scheme.inputs query).length ≤ inputBound)
    (verifierQueries : ℕ)
    (verifierCount : ∀ statement (proof : Proof P Value Y), IsTotalQueryBound
      (run absorb scheme (verifier statement) (initial statement) (statementRoots statement)
        proof.messages proof.openings) verifierQueries)
    (verifierCost : ℕ → ENNReal)
    (verifierBound : ∀ queries statement (proof : Proof P Value Y), WorstCaseCostBound
      (run absorb scheme (verifier statement) (initial statement) (statementRoots statement)
        proof.messages proof.openings)
      ⟨jointError error (hashCharge Y rootBound inputBound verifierQueries queries)⟩
      (verifierCost queries)) :
    Relation Game.trivial
      (jointGame absorb words scheme verifier initial statementRoots falseStatement accepts) :=
  Relation.ofBound _
    (fun (queries : ℕ) =>
      queries * (siteBound + hashCharge Y rootBound inputBound verifierQueries queries) +
        verifierCost queries)
    fun (queries : ℕ) prover admissible =>
      Commitment.soundness absorb words scheme verifier initial statementRoots prover certificate
        commitReceives carries determined initialRoots rootBound statementBound commitBound
        falseStatement doomedValidator inputBound inputs queries verifierQueries admissible
        verifierCount _ (verifierCost queries)
        (Typed.worstCaseCostBound_of_isTotalQueryBound _ (fun key => by
          cases key with
          | inl key => exact (bounded key.2).trans le_self_add
          | inr _ => exact le_add_self) prover queries admissible)
        (verifierBound queries)

end ZkcSecurity.Stage
