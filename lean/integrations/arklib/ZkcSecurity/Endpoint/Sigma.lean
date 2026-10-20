module

public import ZkcSecurity.FiatShamir.Soundness
public import ZkcSecurity.Oracle.Encoding
public import VCVio.CryptoFoundations.FiatShamir.Sigma.KnowledgeExtraction
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
public import VCVio.OracleComp.SimSemantics.QueryImpl.Compose
public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation

@[expose] public section

/-! # The generic Sigma bridge

Knowledge soundness of a verifier that asks one transcript challenge, from
VCVio's replay extraction for the Fiat–Shamir transform of a Sigma protocol.

A one-challenge transcript shape (`Shape`) describes how the verifier absorbs a
proof: the commitment's message events, in their order (any number, zero
included; a Chaum–Pedersen or AND proof sends two commitments before the
challenge), and
the challenge occurrence; how a commitment and a response are delivered as a
typed proof (`Shape.proof`, commitments then responses), and how a typed proof
is read back (`Shape.read`). The encoders and decoders are checked: reading the
events of a commitment gives it back, and events that read as a commitment are
its events, so the shape determines where in a history a challenge key ends.

A verifier corresponds to a Sigma protocol at a statement and an initial
transcript (`Corresponds`) when, on every commitment and response, it asks the
transcript oracle once, at the initial transcript followed by the commitment's
events and the challenge occurrence, and returns the protocol's verification of
the answer.

Routing (`Shape.route`) sends every history to a key of VCVio's transform: a
history that ends in a commitment's events and the challenge occurrence goes to
its prior history and the commitment, any other history, malformed and empty
ones included, to itself and a fixed commitment, on a separate branch. It is
injective on all histories (`Shape.route_injective`), so the routed cache seen
on histories is the history cache (`Shape.run_eq`): the experiment in which the
prover queries a lazily sampled oracle on all typed histories and the verifier
then checks its output is exactly VCVio's knowledge verification run of the
routed prover (`Shape.reduce`). Routing issues one VCVio oracle query per
history query and nothing else (`Shape.reduce_bound`), so the prover's budget
transports. `Shape.knowledge_soundness` then applies VCVio's replay extractor
(`FiatShamir.knowledgeExtractor_success`) under special soundness.

The challenges are exactly uniform field elements (the registered model
`model.exact-uniform-challenges`), answered by one lazily sampled oracle on
typed histories (`historyOracle`, `model.history-oracle`) shared by the prover's
queries and final verification. The statement is fixed before the prover runs.
-/

set_option autoImplicit false

namespace ZkcSecurity.Endpoint.Sigma
open OracleComp OracleSpec
open Zkc.Construction
open ZkcSecurity.Oracle.Encoding (view view_cacheQuery)

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

local instance : ∀ t, MeasurableSpace ((_root_.FiatShamir.Fork.wrappedSpec F).Range t) :=
  fun _ => ⊤
local instance : ∀ t, DiscreteMeasurableSpace ((_root_.FiatShamir.Fork.wrappedSpec F).Range t) :=
  fun _ => inferInstance
noncomputable local instance : IsUniformMeasureSpec (_root_.FiatShamir.Fork.wrappedSpec F) :=
  IsUniformMeasureSpec.ofFiniteNonempty _

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

section Run
variable {Stmt Wit PrvState : Type} {rel : Stmt → Wit → Bool}

/-- Routed, a corresponding verifier is VCVio's Fiat–Shamir verifier, with the
initial transcript as the context message. -/
theorem route_verify [DecidableEq Commit] (sigma : SigmaProtocol Stmt Wit Commit PrvState F Resp rel)
    (generable : GenerableRelation Stmt Wit rel) (statement : Stmt) (initial : History F G)
    {verify : Commit × Resp → OracleComp (HistorySpec F G) Bool}
    (corresponds : Corresponds shape sigma statement initial verify) (proof : Commit × Resp) :
    simulateQ shape.routeQueries (verify proof) =
      (_root_.FiatShamir (m := OracleComp (KeySpec F G Commit)) sigma generable
        (History F G ⊕ History F G)).verify statement (.inl initial) proof := by
  rw [corresponds]
  rcases proof with ⟨commitment, response⟩
  simp only [simulateQ_bind, shape.route_challenge (shape.route_append initial commitment), simulateQ_pure]
  simp [_root_.FiatShamir, HasQuery.query, map_eq_bind_pure_comp]

/-- The knowledge experiment of a corresponding verifier is exactly VCVio's
knowledge verification run of the routed prover: the routed cache restricted to
histories is the history cache. -/
theorem run_eq [DecidableEq Commit] (sigma : SigmaProtocol Stmt Wit Commit PrvState F Resp rel)
    (generable : GenerableRelation Stmt Wit rel) (prover : Prover F G Stmt Commit Resp) (statement : Stmt)
    (initial : History F G) {verify : Commit × Resp → OracleComp (HistorySpec F G) Bool}
    (corresponds : Corresponds shape sigma statement initial verify) :
    run prover verify statement initial =
      _root_.FiatShamir.knowledgeVerifyRun sigma generable (History F G ⊕ History F G)
        (shape.reduce prover) statement (.inl initial) := by
  unfold run _root_.FiatShamir.knowledgeVerifyRun
  have routed : (do
      let proof ← shape.reduce prover statement (.inl initial)
      (_root_.FiatShamir sigma generable (History F G ⊕ History F G)).verify statement (.inl initial) proof) =
      simulateQ shape.routeQueries (do
        let proof ← prover statement initial
        verify proof) := by
    simp only [simulateQ_bind, reduce, Sum.elim_inl, id, shape.route_verify sigma generable statement initial
      corresponds]
  rw [routed, ← QueryImpl.simulateQ_compose]
  symm
  have projected := run'_simulateQ_eq_of_query_map_eq
    ((_root_.FiatShamir.Fork.unifForward (History F G ⊕ History F G) Commit F +
      _root_.FiatShamir.Fork.roImpl (History F G ⊕ History F G) Commit F) ∘ₛ shape.routeQueries)
    (forwardUniform (F := F) (G := G) + historyOracle (F := F) (G := G))
    (fun state : _root_.FiatShamir.Fork.SimState (History F G ⊕ History F G) Commit F =>
      view shape.route state.1) ?step
    (do
      let proof ← prover statement initial
      verify proof) (∅, [])
  · simpa using projected
  · intro query state
    obtain ⟨cache, log⟩ := state
    cases query with
    | inl n =>
        rw [QueryImpl.apply_compose, routeQueries_inl,
          QueryImpl.simulateQ_add_liftM_query_left, _root_.FiatShamir.Fork.unifForward_run]
        simp [forwardUniform]
    | inr history =>
        rw [QueryImpl.apply_compose, routeQueries_inr, QueryImpl.simulateQ_add_liftM_query_right]
        cases hit : cache (shape.route history) with
        | some answer =>
            have viewed : view shape.route cache history = some answer := hit
            rw [_root_.FiatShamir.Fork.roImpl_run_some _ _ _ _ _ hit, QueryImpl.add_apply_inr,
              historyOracle, QueryImpl.withCaching_run_some _ viewed]
            simp
        | none =>
            have viewed : view shape.route cache history = none := hit
            rw [_root_.FiatShamir.Fork.roImpl_run_none _ _ _ _ hit, QueryImpl.add_apply_inr,
              historyOracle, QueryImpl.withCaching_run_none _ viewed]
            simp [map_eq_bind_pure_comp, view_cacheQuery shape.route shape.route_injective]

/-- **Knowledge soundness through the Sigma bridge.** For a specially sound Sigma
protocol and a verifier that corresponds to it at a fixed statement and initial
transcript, every prover whose transcript-oracle queries number at most `budget`
on every path is accepted with probability `accepting` such that VCVio's replay
extractor, run on the routed prover, finds a witness of the protocol's relation
with probability at least `accepting * (accepting / (budget + 1) - 1 / |F|)`.
Subtraction is truncated in `ENNReal`. -/
theorem knowledge_soundness [DecidableEq Commit] [SampleableType F] [Fintype F] [Inhabited F]
    [SampleableType Wit] (sigma : SigmaProtocol Stmt Wit Commit PrvState F Resp rel)
    (generable : GenerableRelation Stmt Wit rel) (sound : sigma.SpeciallySound)
    (prover : Prover F G Stmt Commit Resp) (statement : Stmt) (initial : History F G)
    {verify : Commit × Resp → OracleComp (HistorySpec F G) Bool}
    (corresponds : Corresponds shape sigma statement initial verify) (budget : Nat)
    (bounded : IsQueryBoundP (prover statement initial) (· matches .inr _) budget) :
    let accepting := acceptance prover verify statement initial
    accepting * (accepting / (budget + 1 : ENNReal) - _root_.FiatShamir.challengeSpaceInv F) ≤
      Pr{let witness ← _root_.FiatShamir.knowledgeExtractor sigma generable (History F G ⊕ History F G)
          (shape.reduce prover) (.inl initial) budget statement}[rel statement witness = true] := by
  have upstream := _root_.FiatShamir.knowledgeExtractor_success sigma generable (History F G ⊕ History F G)
    sound (shape.reduce prover) statement (.inl initial) budget
    (shape.reduce_bound prover statement initial budget bounded)
  have same : acceptance prover verify statement initial =
      _root_.FiatShamir.knowledgeAcceptance sigma generable (History F G ⊕ History F G)
        (shape.reduce prover) statement (.inl initial) := by
    unfold acceptance _root_.FiatShamir.knowledgeAcceptance
    rw [shape.run_eq sigma generable prover statement initial corresponds]
  simp only [same]
  exact upstream

end Run

end Shape

end ZkcSecurity.Endpoint.Sigma
