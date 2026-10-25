module

public import ZkcSecurity.HashChain.JointBridge
public import ZkcSecurity.Stage.Joint
public import ZkcSecurity.Stage.Commitment

@[expose] public section

/-! # The hash-chain frame of a verifier with committed tables

A verifier with committed tables deployed over a native hash-chain suite calls one byte hash for
its transcript and for its Merkle trees. This module states the joint stage's frame
(`ZkcSecurity.Stage.Joint.Frame`) for that deployment and composes it with the commitment stage.

**The concrete experiment.** The adversary calls the byte hash on any bytes and outputs a
statement and a proof; the deployed verifier (`deployed`) then runs on the same byte hash, binding
the statement's initial history, absorbing events and roots, reading each query's raw answer from
the counter blocks of a request at the current state, and authenticating openings with tagged row
calls. Its failure (`concreteFailure`) is the bridge's false acceptance on the classified run: the
verifier accepts and the statement is false for its tables extracted, from the row calls before the
first call that realizes one of the verifier's transcript keys, at that checkpoint.

**The simulation** (`simulation`). The joint simulator (`jointSimulator`) translates an adversary
with at most `q` calls of the byte hash: a private tape of `q` digests, row calls passed through to
their own cells of the joint oracle, and every other call handled by the chain simulator. Its
inequality is the chain of `concrete_le_lazy` (the concrete experiment exceeds the lazily sampled
joint simulation by at most `(q + V)² / |S|`), `lazy_eq_translated` and `translated_eq_ideal`.

**Budgets.** The provider's budget map is proved, not assumed: every program the simulation
translates makes at most `q` joint-oracle queries, transcript and hash cells together, on every
path, since each call of the byte hash makes at most one query and only at the first call of its
attempt (`Provider.Simulation.transport`, from `queryCost.cost q = q` and `covers`). The verifier's
calls `V`, every binding, absorbing, request and row call of the deployed verifier, enter the loss
`(q + V)² / |S|` on the joint trace (`joint`); the commitment stage is evaluated at the transported
budget `q` (`provider_budget`).

**The frame** (`frame`) records the simulation with every obligation of
`ZkcSecurity.Stage.Joint.Frame`, proved: the namespaces are the encodings' own (`Encoding.namespaces`),
a row call's bytes belong to its own cell in every state and only they realize it, transcript cells
are realized only by chain calls, a row call's reply is its cell's answer, recording a row answer
leaves the chain simulator's state unchanged, and every other call reads and moves the state only
through it.

**Composition** (`committed_soundness`). The frame's contract (`contract`) has the bridge's
checkpoint extraction and checkpoint event and the concrete failure as intended event, and composes
with any commitment stage over the joint game: the concrete failure of an adversary with at most `q`
calls is at most `(q + V)² / |S| + commitment.loss q`.
-/

set_option autoImplicit false

namespace ZkcSecurity.HashChain.Joint
open OracleComp OracleSpec ZkcSecurity.FiatShamir ZkcSecurity.Commitment
  ZkcSecurity.HashChain.Encoding

variable {J : PIR.Signature} {E P Shape Value Query S A Stmt : Type} [DecidableEq E]
  [DecidableEq Shape] [DecidableEq S] [DecidableEq Query] [Inhabited S] [SampleableType S]
  [Fintype S]

section Frame
variable (encoding : Encoding E Shape S Query) (width : ℕ)
  (absorb : Typed.Interface J E P (fun _ => Fin width → S)) (scheme : Extractable Shape Value Query S)
  (words : Words J Shape Value) (verifier : Stmt → PIR.Process (committed J Shape Value) A)
  (initial : Stmt → List (Absorbed E Shape S)) (statementRoots : Stmt → List (Shape × S))
  (falseStatement : Stmt → List (Table Value) → Prop) (accepts : A → Prop)

omit [DecidableEq E] [DecidableEq Shape] [DecidableEq S] [DecidableEq Query] [Inhabited S]
  [SampleableType S] [Fintype S] in
/-- A total bound on the byte hash's calls is a bound on its single family. -/
theorem familyQueryBound_of_total' {α : Type} :
    ∀ (adversary : OracleComp (ByteHash S) α) (calls : ℕ),
      IsTotalQueryBound adversary calls →
        Provider.FamilyQueryBound (fun _ => ()) adversary (fun _ => calls) := by
  intro adversary
  induction adversary using OracleComp.inductionOn with
  | pure value => intro _ _; trivial
  | query_bind query next ih =>
      intro calls bounded
      obtain ⟨positive, rest⟩ := isTotalQueryBound_query_bind_iff.mp bounded
      refine (Provider.familyQueryBound_query_bind_iff _).mpr ⟨positive, fun reply => ?_⟩
      have same : Function.update (fun _ : Unit => calls) () (calls - 1) = fun _ => calls - 1 := by
        funext point
        cases point
        simp
      rw [same]
      exact ih reply (calls - 1) (rest reply)

/-- The concrete failure: the bridge's false acceptance in the concrete experiment, read through the
classification of the adversary's calls. -/
noncomputable def concreteFailure (adversary : OracleComp (ByteHash S) (Stmt × Proof P Value S))
    (_ : Unit) : ENNReal :=
  Pr{let result ← (simulateQ randomOracle (concreteExperiment encoding width absorb scheme verifier
      initial statementRoots adversary)).run' ∅}[
    FalseAcceptance words scheme statementRoots falseStatement accepts result]

/-- The ideal failure of a mixture of provers: the bridge's false acceptance in the joint
experiment after drawing the prover. -/
noncomputable def idealFailure
    (provers : ProbComp (OracleComp (OracleSpec.ofFn (Cells E Shape S Query width))
      (Stmt × Proof P Value S))) (_ : Unit) : ENNReal :=
  Stage.Joint.oracleMixture (ZkcSecurity.Commitment.experiment absorb scheme verifier initial
    statementRoots) (FalseAcceptance words scheme statementRoots falseStatement accepts) provers

/-- The hash-chain provider simulation of a verifier with committed tables: the joint simulator
with a private tape of `q` digests, cost `q`, the deployed verifier's calls as expansion and loss
`(q + V)² / |S|`. -/
noncomputable def simulation (positive : 0 < width) (small : width ≤ 2 ^ 64)
    (nonempty : ∀ statement, initial statement ≠ []) (verifierCalls : ℕ)
    (verifierBound : ∀ statement proof, IsTotalQueryBound
      (deployed encoding width absorb scheme verifier initial statementRoots statement proof)
      verifierCalls)
    {queries : ℕ}
    (queryBounded : ∀ statement proof, IsTotalQueryBound
      (jointReading width absorb scheme verifier initial statementRoots statement proof) queries) :
    Provider.Simulation (ByteHash S) (fun _ => ()) (Cells E Shape S Query width)
      (concreteFailure encoding width absorb scheme words verifier initial statementRoots falseStatement
        accepts)
      (idealFailure width absorb scheme words verifier initial statementRoots falseStatement
        accepts) where
  Tape budget := Fin (budget ()) → S
  tapeSampleable _ := inferInstance
  simulator budget := jointSimulator encoding width (budget ())
  charged _ := True
  chargedDecidable _ := instDecidableTrue
  carries _ _ _ _ _ := trivial
  queryCost :=
    { cost := fun budget => budget ()
      monotone := fun _ _ le => le ()
      expansion := fun _ => verifierCalls
      loss := fun budget calls =>
        (((budget () + calls) * (budget () + calls) : ℕ) : ENNReal) / Fintype.card S }
  covers budget := by simp [Provider.chargedBudget]
  bound adversary budget _ bounded := by
    have total : IsTotalQueryBound adversary (budget ()) := by
      simpa using Provider.FamilyQueryBound.isTotalQueryBound (fun _ => ()) adversary budget bounded
    refine (concrete_le_lazy encoding width absorb scheme verifier initial statementRoots small
      nonempty adversary total verifierCalls verifierBound _).trans (le_of_eq ?_)
    congr 1
    rw [_root_.EvalDistEq.prEvent_eq (lazy_eq_translated encoding width absorb
      scheme verifier initial statementRoots positive adversary total queryBounded),
      translated_eq_ideal encoding width absorb scheme verifier initial statementRoots words
        (budget ()) adversary falseStatement accepts]
    rfl

/-- The joint stage's frame for the hash chain with row calls passed through: every obligation
holds. -/
noncomputable def frame (positive : 0 < width) (small : width ≤ 2 ^ 64)
    (nonempty : ∀ statement, initial statement ≠ []) (verifierCalls : ℕ)
    (verifierBound : ∀ statement proof, IsTotalQueryBound
      (deployed encoding width absorb scheme verifier initial statementRoots statement proof)
      verifierCalls)
    {queries : ℕ}
    (queryBounded : ∀ statement proof, IsTotalQueryBound
      (jointReading width absorb scheme verifier initial statementRoots statement proof) queries) :
    Stage.Joint.Frame (ByteHash S) (fun _ => ()) (Cells E Shape S Query width) (ChainCall E Shape S)
      (concreteFailure encoding width absorb scheme words verifier initial statementRoots falseStatement
        accepts)
      (fun provers _ => Stage.Joint.oracleMixture (ZkcSecurity.Commitment.experiment absorb scheme
        verifier initial statementRoots) (FalseAcceptance words scheme statementRoots falseStatement
          accepts) provers) where
  simulation := simulation encoding width absorb scheme words verifier initial statementRoots
    falseStatement accepts positive small nonempty verifierCalls verifierBound queryBounded
  namespaces := encoding.namespaces
  passThrough _ state call := attempt_callBytes state call
  separated _ _ _ _ assigned := eq_callBytes_of_attempt assigned
  chainOnly _ _ _ _ assigned := chainCall_of_attempt assigned
  hashRange _ := Equiv.refl S
  hashAnswer _ _ _ := rfl
  ChainState budget := ChainState (Absorbed E Shape S) S Bytes width (budget ())
  chainState _ state := state.chain
  recordHash _ state call ideal := record_hash_chain state call ideal
  attemptChain _ _ _ query same _ := attempt_chain same query
  recordedChain _ _ _ key same := recorded_chain same key
  recordTranscript _ _ _ key ideal same := record_transcript_chain same key ideal
  respondChain _ _ _ query same := (respond_chain same query).1
  respondState _ _ _ query same := (respond_chain same query).2
  jointLoss total := ((total * total : ℕ) : ENNReal) / Fintype.card S
  joint budget expansion := by
    change (((budget () + expansion) * (budget () + expansion) : ℕ) : ENNReal) / Fintype.card S ≤
      ((((∑ each, budget each) + expansion) * ((∑ each, budget each) + expansion) : ℕ) : ENNReal) /
        Fintype.card S
    simp

/-- The frame's contract: the bridge's checkpoint extraction and checkpoint event over the joint
game, and the concrete failure as intended event. -/
noncomputable def contract (positive : 0 < width) (small : width ≤ 2 ^ 64)
    (nonempty : ∀ statement, initial statement ≠ []) (verifierCalls : ℕ)
    (verifierBound : ∀ statement proof, IsTotalQueryBound
      (deployed encoding width absorb scheme verifier initial statementRoots statement proof)
      verifierCalls)
    {queries : ℕ}
    (queryBounded : ∀ statement proof, IsTotalQueryBound
      (jointReading width absorb scheme verifier initial statementRoots statement proof) queries) :=
  (frame encoding width absorb scheme words verifier initial statementRoots falseStatement accepts
      positive small nonempty verifierCalls verifierBound queryBounded).contract
    (ZkcSecurity.Commitment.experiment absorb scheme verifier initial statementRoots)
    (FalseAcceptance words scheme statementRoots falseStatement accepts)
    (Stage.Joint.bridgeCheckpoint words scheme statementRoots)
    (fun result => Stage.Joint.transcriptKeys result.verifierLog)
    (fun result => result.proverLog ++ result.verifierLog)
    (fun result extraction => Accepted accepts result.outcome ∧
      falseStatement result.statement (extraction result.statement))
    (Stage.Joint.falseAcceptance_iff_checkpoint words scheme statementRoots falseStatement accepts) ()
    (fun adversary => concreteFailure encoding width absorb scheme words verifier initial
      statementRoots falseStatement accepts adversary ())
    (fun _ => le_rfl)

/-- The provider's budget map is the adversary's total number of calls: every translated program
makes at most that many joint-oracle queries. -/
theorem provider_budget (positive : 0 < width) (small : width ≤ 2 ^ 64)
    (nonempty : ∀ statement, initial statement ≠ []) (verifierCalls : ℕ)
    (verifierBound : ∀ statement proof, IsTotalQueryBound
      (deployed encoding width absorb scheme verifier initial statementRoots statement proof)
      verifierCalls)
    {queries : ℕ}
    (queryBounded : ∀ statement proof, IsTotalQueryBound
      (jointReading width absorb scheme verifier initial statementRoots statement proof) queries)
    (budget : Provider.Budget Unit) :
    (contract encoding width absorb scheme words verifier initial statementRoots falseStatement accepts
      positive small nonempty verifierCalls verifierBound queryBounded).provider.budget budget =
        budget () :=
  rfl

/-- The provider's budget map is sound: every program the simulation translates from an adversary
within a budget makes at most the budget's number of joint-oracle queries on every path. -/
theorem translate_queryBound (positive : 0 < width) (small : width ≤ 2 ^ 64)
    (nonempty : ∀ statement, initial statement ≠ []) (verifierCalls : ℕ)
    (verifierBound : ∀ statement proof, IsTotalQueryBound
      (deployed encoding width absorb scheme verifier initial statementRoots statement proof)
      verifierCalls)
    {queries : ℕ}
    (queryBounded : ∀ statement proof, IsTotalQueryBound
      (jointReading width absorb scheme verifier initial statementRoots statement proof) queries)
    (adversary : OracleComp (ByteHash S) (Stmt × Proof P Value S)) {calls : ℕ}
    (bounded : IsTotalQueryBound adversary calls) :
    ∀ program ∈ support ((simulation encoding width absorb scheme words verifier initial
        statementRoots falseStatement accepts positive small nonempty verifierCalls verifierBound
        queryBounded).translate (fun _ => calls) adversary),
      IsTotalQueryBound program calls :=
  (simulation encoding width absorb scheme words verifier initial statementRoots falseStatement
    accepts positive small nonempty verifierCalls verifierBound queryBounded).transport adversary
    (fun _ => calls) (familyQueryBound_of_total' adversary calls bounded)

/-- Soundness of a verifier with committed tables over a hash-chain suite on one byte hash: for any
commitment stage over the joint game, an adversary with at most `q` calls of the byte hash makes the
deployed verifier accept a statement that is false for its tables extracted at the checkpoint of
one of its transcript keys with probability at most `(q + V)² / |S|` plus the commitment stage's
loss at `q`, with `V` the deployed verifier's calls of every kind. -/
theorem committed_soundness (positive : 0 < width) (small : width ≤ 2 ^ 64)
    (nonempty : ∀ statement, initial statement ≠ []) (verifierCalls : ℕ)
    (verifierBound : ∀ statement proof, IsTotalQueryBound
      (deployed encoding width absorb scheme verifier initial statementRoots statement proof)
      verifierCalls)
    {queries : ℕ}
    (queryBounded : ∀ statement proof, IsTotalQueryBound
      (jointReading width absorb scheme verifier initial statementRoots statement proof) queries)
    (commitment : Stage.Relation Stage.Game.trivial
      (contract encoding width absorb scheme words verifier initial statementRoots falseStatement
        accepts positive small nonempty verifierCalls verifierBound queryBounded).jointGame)
    (adversary : OracleComp (ByteHash S) (Stmt × Proof P Value S)) {calls : ℕ}
    (bounded : IsTotalQueryBound adversary calls) :
    concreteFailure encoding width absorb scheme words verifier initial statementRoots falseStatement
        accepts adversary () ≤
      (((calls + verifierCalls) * (calls + verifierCalls) : ℕ) : ENNReal) / Fintype.card S +
        commitment.loss calls := by
  refine ((contract encoding width absorb scheme words verifier initial statementRoots falseStatement
    accepts positive small nonempty verifierCalls verifierBound queryBounded).bounded commitment
    (fun _ => calls) adversary (familyQueryBound_of_total' adversary calls bounded)).trans
    (le_of_eq ?_)
  change (((calls + verifierCalls) * (calls + verifierCalls) : ℕ) : ENNReal) / Fintype.card S + 0 +
    commitment.loss calls = _
  rw [add_zero]

end Frame

end ZkcSecurity.HashChain.Joint
