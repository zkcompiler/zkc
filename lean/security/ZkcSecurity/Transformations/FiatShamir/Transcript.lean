module

public import ZkcSecurity.Mathematics.Oracle.UniformChallenge
public import Zkc.Construction.FiatShamir
public import VCVio.CryptoFoundations.FiatShamir.Sigma.KnowledgeExtraction
public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation

@[expose] public section

open scoped ZkcSecurity.VCVio.UniformChallenge

/-! Transcript shapes, routing and the shared history-oracle experiment.
These interfaces fix prover access and cached execution independently of
knowledge endpoint evidence. Sigma correspondence and replay bounds are proved
in `Transformations.FiatShamir.Knowledge`. -/

set_option autoImplicit false

namespace ZkcSecurity.Endpoint.Sigma
open OracleComp OracleSpec
open Zkc.Construction

/-- A one-challenge transcript shape: the commitment's message events and the
challenge occurrence, with checked encoders and decoders of commitments and
typed proofs. -/
structure Shape (F G Commit Resp : Type) where
  /-- The events that absorb a commitment, in order. -/
  commitments : Commit → History F G
  /-- The number of commitment events; zero is allowed, the challenge then
  directly follows the prior history. -/
  width : Nat
  width_eq : ∀ commitment, (commitments commitment).length = width
  /-- The commitment that a list of events absorbs, if any. -/
  readCommitment : History F G → Option Commit
  read_commitments : ∀ commitment, readCommitment (commitments commitment) = some commitment
  commitments_read : ∀ events commitment, readCommitment events = some commitment →
    commitments commitment = events
  /-- The challenge occurrence. -/
  challenge : Event F G
  /-- A commitment and a response as a typed proof, in delivered order. -/
  proof : Commit → Resp → Proof F G
  /-- The commitment and response a typed proof is read as. -/
  read : Proof F G → Commit × Resp
  read_proof : ∀ commitment response, read (proof commitment response) = (commitment, response)
  /-- The commitment routed with histories that end in no challenge key. -/
  fallback : Commit

/-- Prover oracles: uniform coins and the transcript oracle on histories. -/
abbrev HistorySpec (F G : Type) := unifSpec + (History F G →ₒ F)

/-- VCVio's Fiat–Shamir oracle keys: a prior history or any other history, and a
commitment. -/
abbrev Key (F G Commit : Type) := (History F G ⊕ History F G) × Commit

/-- VCVio's Fiat–Shamir oracles over routed keys. -/
abbrev KeySpec (F G Commit : Type) := unifSpec + (Key F G Commit →ₒ F)

/-- The transcript challenge: one oracle query on the absorbed history. -/
def historyChallenge {F G : Type} (history : History F G) : OracleComp (HistorySpec F G) F :=
  HasQuery.query (spec := History F G →ₒ F) history

/-- A prover of a fixed statement: given the statement and the initial
transcript, it outputs a commitment and a response, with uniform coins and the
transcript oracle on every history. -/
abbrev Prover (F G Stmt Commit Resp : Type) :=
  Stmt → History F G → OracleComp (HistorySpec F G) (Commit × Resp)

section Correspondence
variable {F G Stmt Wit Commit PrvState Resp : Type} {rel : Stmt → Wit → Bool}

/-- A verifier corresponds to a Sigma protocol at a statement and an initial
transcript: on every commitment and response it asks one challenge, at the
initial transcript followed by the commitment's events and the challenge
occurrence, and returns the protocol's verification of it. -/
def Corresponds (shape : Shape F G Commit Resp) (sigma : SigmaProtocol Stmt Wit Commit PrvState F Resp rel)
    (statement : Stmt) (initial : History F G) (verify : Commit × Resp → OracleComp (HistorySpec F G) Bool) :
    Prop :=
  ∀ proof, verify proof = historyChallenge (initial ++ shape.commitments proof.1 ++ [shape.challenge]) >>=
    fun answer => pure (sigma.verify statement proof.1 answer proof.2)

end Correspondence

section Experiment
variable {F G Stmt Commit Resp : Type} [DecidableEq F] [DecidableEq G] [SampleableType F]

/-- The transcript oracle's cache, on histories. -/
abbrev Cache (F G : Type) := (History F G →ₒ F).QueryCache

/-- Uniform coins, forwarded to VCVio's replay oracle. -/
def forwardUniform :
    QueryImpl unifSpec (StateT (Cache F G) (OracleComp (_root_.FiatShamir.Fork.wrappedSpec F))) :=
  fun n => StateT.lift (_root_.FiatShamir.Fork.wrappedUniformQuery F n)

/-- One lazily sampled oracle on histories: a new history receives a fresh
uniform challenge, a repeated one its recorded answer. -/
def historyOracle :
    QueryImpl (History F G →ₒ F)
      (StateT (Cache F G) (OracleComp (_root_.FiatShamir.Fork.wrappedSpec F))) :=
  QueryImpl.withCaching (fun _ => _root_.FiatShamir.Fork.wrappedChallengeQuery F)

/-- The knowledge experiment: the prover sees the statement and the initial
transcript; its coins and oracle queries precede verification of its output in
one initially empty cache. -/
def run (prover : Prover F G Stmt Commit Resp) (verify : Commit × Resp → OracleComp (HistorySpec F G) Bool)
    (statement : Stmt) (initial : History F G) : OracleComp (_root_.FiatShamir.Fork.wrappedSpec F) Bool :=
  StateT.run' (simulateQ (forwardUniform (F := F) (G := G) + historyOracle (F := F) (G := G)) (do
    let proof ← prover statement initial
    verify proof)) (∅ : Cache F G)

/-- The probability that the verifier accepts the prover's output. -/
noncomputable def acceptance (prover : Prover F G Stmt Commit Resp)
    (verify : Commit × Resp → OracleComp (HistorySpec F G) Bool) (statement : Stmt) (initial : History F G) :
    ENNReal :=
  Pr{let accepted ← run prover verify statement initial}[accepted = true]

end Experiment

namespace Shape
variable {F G Commit Resp : Type} [DecidableEq F] [DecidableEq G] (shape : Shape F G Commit Resp)

/-- The prior history and commitment of a history that ends in a commitment's
events and the challenge occurrence. -/
def challengeKey (history : History F G) : Option (History F G × Commit) :=
  if history.getLast? = some shape.challenge then
    (shape.readCommitment (history.dropLast.drop (history.dropLast.length - shape.width))).map
      fun commitment => (history.dropLast.take (history.dropLast.length - shape.width), commitment)
  else none

theorem challengeKey_append (prior : History F G) (commitment : Commit) :
    shape.challengeKey (prior ++ shape.commitments commitment ++ [shape.challenge]) =
      some (prior, commitment) := by
  have length : (prior ++ shape.commitments commitment).length - shape.width = prior.length := by
    rw [List.length_append, shape.width_eq]
    omega
  simp only [challengeKey, List.getLast?_concat, ite_true, List.dropLast_concat, length,
    List.drop_left, shape.read_commitments, Option.map_some, List.take_left]

theorem challengeKey_some {history prior : History F G} {commitment : Commit}
    (found : shape.challengeKey history = some (prior, commitment)) :
    history = prior ++ shape.commitments commitment ++ [shape.challenge] := by
  unfold challengeKey at found
  split_ifs at found with last
  obtain ⟨read, readEq, same⟩ := Option.map_eq_some_iff.mp found
  simp only [Prod.mk.injEq] at same
  obtain ⟨priorEq, commitmentEq⟩ := same
  subst priorEq commitmentEq
  rw [shape.commitments_read _ _ readEq, List.take_append_drop]
  exact (List.dropLast_append_getLast? _ last).symm

/-- Route each history to a key of VCVio's transform: a challenge key to its
prior history and commitment, any other history to itself. -/
def route (history : History F G) : Key F G Commit :=
  match shape.challengeKey history with
  | some (prior, commitment) => (.inl prior, commitment)
  | none => (.inr history, shape.fallback)

/-- Routing is injective on all histories, malformed and empty ones included. -/
theorem route_injective : Function.Injective shape.route := by
  intro first second same
  unfold route at same
  cases firstKey : shape.challengeKey first with
  | none =>
      cases secondKey : shape.challengeKey second with
      | none => simp_all
      | some key => obtain ⟨prior, commitment⟩ := key; simp_all
  | some key =>
      obtain ⟨prior, commitment⟩ := key
      cases secondKey : shape.challengeKey second with
      | none => simp_all
      | some other =>
          obtain ⟨otherPrior, otherCommitment⟩ := other
          simp only [firstKey, secondKey, Prod.mk.injEq, Sum.inl.injEq] at same
          rw [shape.challengeKey_some firstKey, shape.challengeKey_some secondKey, same.1, same.2]

theorem route_append (prior : History F G) (commitment : Commit) :
    shape.route (prior ++ shape.commitments commitment ++ [shape.challenge]) = (.inl prior, commitment) := by
  rw [route, challengeKey_append]

/-- Route each history query to its key; uniform coins pass through. -/
def routeQueries : QueryImpl (HistorySpec F G) (OracleComp (KeySpec F G Commit)) :=
  (fun n => (liftM (unifSpec.query n) : OracleComp (KeySpec F G Commit) (Fin (n + 1)))) +
    (fun history => (liftM ((Key F G Commit →ₒ F).query (shape.route history)) :
      OracleComp (KeySpec F G Commit) F))

theorem routeQueries_inl (n : ℕ) :
    shape.routeQueries (.inl n) =
      (liftM (unifSpec.query n) : OracleComp (KeySpec F G Commit) (Fin (n + 1))) := rfl

theorem routeQueries_inr (history : History F G) :
    shape.routeQueries (.inr history) =
      (liftM ((Key F G Commit →ₒ F).query (shape.route history)) : OracleComp (KeySpec F G Commit) F) := rfl

theorem route_challenge {history : History F G} {key : Key F G Commit} (routed : shape.route history = key) :
    simulateQ shape.routeQueries (historyChallenge history) =
      (liftM ((Key F G Commit →ₒ F).query key) : OracleComp (KeySpec F G Commit) F) := by
  subst routed
  unfold historyChallenge routeQueries
  exact QueryImpl.simulateQ_add_liftM_query_right _ _ history

/-- The same prover, querying VCVio's oracle through the routing. -/
def reduce {Stmt : Type} (prover : Prover F G Stmt Commit Resp) :
    _root_.FiatShamir.KnowledgeProver Stmt Commit F Resp (History F G ⊕ History F G) :=
  fun statement message => simulateQ shape.routeQueries (prover statement (message.elim id id))

/-- Routing issues exactly one Fiat–Shamir oracle query per history query and no
other oracle query. -/
theorem reduce_bound {Stmt : Type} [DecidableEq Commit] (prover : Prover F G Stmt Commit Resp)
    (statement : Stmt) (message : History F G) (budget : Nat)
    (bounded : IsQueryBoundP (prover statement message) (· matches .inr _) budget) :
    _root_.FiatShamir.nmaHashQueryBound (M := History F G ⊕ History F G)
      (shape.reduce prover statement (.inl message)) budget := by
  unfold _root_.FiatShamir.nmaHashQueryBound reduce
  refine IsQueryBoundP.simulateQ_of_step bounded ?_ ?_
  · intro query oracle
    cases query with
    | inl n => cases oracle
    | inr history =>
        change IsQueryBoundP (liftM ((KeySpec F G Commit).query (.inr (shape.route history))) :
          OracleComp (KeySpec F G Commit) F) _ 1
        simp
  · intro query notOracle
    cases query with
    | inl n =>
        change IsQueryBoundP (liftM ((KeySpec F G Commit).query (.inl n)) :
          OracleComp (KeySpec F G Commit) (Fin (n + 1))) _ 0
        simp
    | inr history => exact absurd rfl notOracle

end Shape

end ZkcSecurity.Endpoint.Sigma

namespace ZkcSecurity.Endpoint
open OracleComp
open Zkc.Construction

/-- A prover of typed proofs for a fixed statement, with uniform coins and the
transcript oracle on every history. -/
abbrev TypedProver (F G Stmt : Type) := Stmt → History F G → OracleComp (Sigma.HistorySpec F G) (Proof F G)

/-- A prover of proof bytes for a fixed statement, with uniform coins and the
transcript oracle on every history. -/
abbrev BytesProver (F G Stmt : Type) := Stmt → History F G → OracleComp (Sigma.HistorySpec F G) (List UInt8)

end ZkcSecurity.Endpoint
