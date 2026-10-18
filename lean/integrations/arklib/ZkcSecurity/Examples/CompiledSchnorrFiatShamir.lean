module

public import ZkcExamples.Construction.SchnorrProof
public import ZkcExamples.Construction.SchnorrProofBinding
public import ZkcSecurity.Examples.StructuredSchnorrFiatShamir
public import ZkcSecurity.Oracle.Encoding
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
public import VCVio.OracleComp.SimSemantics.QueryImpl.Compose
public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation

@[expose] public section

/-! Knowledge soundness of the compiled non-interactive Schnorr verifier.

The subject is the compiler's constructed validator for `example::Proof`,
accepted by the per-compile transcript-construction check
(`SchnorrProof.accepted`). Its meaning is the ideal transcript interpretation
of the exported operations, run on the binding history, the public inputs and
the proof's two messages; the verifier accepts when the selected output is true
and the whole proof is read.

Named assumptions, beyond the checked equations:

* Random oracle. The native suite's challenge on an absorbed history is a
  uniformly random function of that history, shared by the prover and final
  verification and queried by the prover at any history (`historyOracle`).
  Canonical value and occurrence encodings are injective, so typed histories
  stand for the absorbed bytes; the suite's reduction of squeezed bytes to a
  field element is treated as exactly uniform.
* Binding. The host initializes the transcript with exactly the authorized
  public context and the policy's public inputs (`initial`); the check proves the
  policy publishes every validator data input, including the statement. The
  fixed-statement bound below does not depend on this binding; it matters for
  adaptively chosen statements, which are not covered.
* Transport. Proof bytes decode canonically to the typed messages, in order.
* Native correctness. The export reproduces the checked candidate, and native
  field, group and transcript kernels implement their mathematical meanings.

The proof routes every history injectively to an oracle key of VCVio's
Fiat–Shamir transform (`route`), shows that the routed experiment is exactly
VCVio's (`run_eq`), and applies its replay extraction.
-/

namespace ZkcSecurity.Examples.CompiledSchnorrFiatShamir
open OracleComp OracleSpec
open Zkc.Construction
open ZkcExamples.Construction
open ZkcSecurity.Oracle.Encoding (view view_cacheQuery)
open ZkcSecurity.Examples.StructuredSchnorrFiatShamir (generable)

abbrev groupDomain : String := "bls12-381.g1"
abbrev fieldDomain : String := "bls12-381.fr"

/-- The commitment's message occurrence fixed by the checked context. -/
def commitmentOrigin : Origin :=
  SchnorrProof.context.message SchnorrProof.wiring.commitmentSite SchnorrProof.context.producer
    SchnorrProof.context.validator

/-- The challenge occurrence fixed by the checked context. -/
def challengeOrigin : Origin :=
  SchnorrProof.context.query SchnorrProof.wiring.challengeSite (.draw fieldDomain)

section Routing
variable {F G : Type}

/-- The prior history and commitment of a history ending in the commitment
message and the challenge occurrence. -/
def challengeKey (history : History F G) : Option (History F G × G) :=
  match history.reverse with
  | .challenge occurrence :: .message origin (.group domain commitment) :: prior =>
      if occurrence = challengeOrigin ∧ origin = commitmentOrigin ∧ domain = groupDomain then
        some (prior.reverse, commitment)
      else none
  | _ => none

theorem challengeKey_append (prior : History F G) (commitment : G) :
    challengeKey (prior ++ [.message commitmentOrigin (.group groupDomain commitment),
      .challenge challengeOrigin]) = some (prior, commitment) := by
  simp [challengeKey]

theorem challengeKey_some {history prior : History F G} {commitment : G}
    (found : challengeKey history = some (prior, commitment)) :
    history = prior ++ [.message commitmentOrigin (.group groupDomain commitment),
      .challenge challengeOrigin] := by
  unfold challengeKey at found
  split at found
  · rename_i occurrence origin domain value rest reversed
    split_ifs at found with conditions
    obtain ⟨occurrenceEq, originEq, domainEq⟩ := conditions
    simp only [Option.some.injEq, Prod.mk.injEq] at found
    obtain ⟨priorEq, commitmentEq⟩ := found
    subst occurrenceEq originEq domainEq priorEq commitmentEq
    have := congrArg List.reverse reversed
    simpa using this
  · cases found

/-- Oracle keys of VCVio's transform: a prior history and commitment, or any
other history. -/
abbrev Key (F G : Type) := (History F G ⊕ History F G) × G

variable [AddCommGroup G]

def route (history : History F G) : Key F G :=
  match challengeKey history with
  | some (prior, commitment) => (.inl prior, commitment)
  | none => (.inr history, 0)

theorem route_injective : Function.Injective (route (F := F) (G := G)) := by
  intro first second same
  unfold route at same
  cases firstKey : challengeKey first with
  | none =>
      cases secondKey : challengeKey second with
      | none => simp_all
      | some key => obtain ⟨prior, commitment⟩ := key; simp_all
  | some key =>
      obtain ⟨prior, commitment⟩ := key
      cases secondKey : challengeKey second with
      | none => simp_all
      | some other =>
          obtain ⟨otherPrior, otherCommitment⟩ := other
          simp only [firstKey, secondKey, Prod.mk.injEq, Sum.inl.injEq] at same
          rw [challengeKey_some firstKey, challengeKey_some secondKey, same.1, same.2]

/-- The host's initial binding: the authorized application context and the
values at the checked policy's public inputs, base then statement
(`initial_binds_public`). -/
def initial (application : String) (base key : G) : History F G :=
  [.binding application (SchnorrProof.inputs base key)]

/-- Acceptance requires the selected true output and a completely read proof. -/
def accepted (result : PIR.Outcome (Option Bool) × Proof F G) : Bool :=
  match result.1, result.2 with
  | .returned (some decision), [] => decision
  | _, _ => false

end Routing

/-- The initial history binds exactly the values the checked policy publishes:
the validator's original inputs at `policy.publicInputs`, in order. -/
theorem initial_binds_public {F G : Type} [AddCommGroup G] (application : String) (base key : G)
    (challengeService : Nat) :
    ∃ values, publicValues SchnorrProof.participant.policy
        (SchnorrProof.originalValue (F := F) base key challengeService) = some values ∧
      initial application base key = [.binding application values] :=
  ⟨_, SchnorrProof.public_values base key challengeService, rfl⟩

section Experiment
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
  [SampleableType F] [SampleableType G]

omit [DecidableEq F] [SampleableType F] [SampleableType G] in
/-- For any challenge function, the original validator's transform makes one
challenge request, at the prior history followed by the received commitment
and the challenge occurrence. -/
theorem transform_experiment {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (prior : History F G) (base key : G) (handle : Nat)
    (proof : G × F) :
    transform SchnorrProof.context challenge
        (Zkc.Protocols.Schnorr.Common.experiment SchnorrProof.wiring base key handle)
        prior [.group groupDomain proof.1, .field fieldDomain proof.2] =
      challenge (prior ++ [.message commitmentOrigin (.group groupDomain proof.1),
          .challenge challengeOrigin]) >>= fun answer =>
        pure (.returned (some (decide (proof.2 • base = proof.1 + answer • key))), []) := by
  rcases proof with ⟨commitment, response⟩
  simp [Zkc.Protocols.Schnorr.Common.experiment, transform, Payload.value, Payload.ofValue,
    SchnorrProof.wiring, ZkcExamples.NativePrograms.Schnorr.wiring, commitmentOrigin,
    challengeOrigin, SchnorrProof.context_eq]

/-- Prover oracles: uniform coins and the transcript oracle on histories. -/
abbrev HistorySpec (F G : Type) := unifSpec + (History F G →ₒ F)
/-- VCVio's Fiat–Shamir oracles over routed keys. -/
abbrev KeySpec (F G : Type) := unifSpec + (Key F G →ₒ F)

/-- The transcript challenge: one oracle query on the absorbed history. -/
def historyChallenge (history : History F G) : OracleComp (HistorySpec F G) F :=
  HasQuery.query (spec := History F G →ₒ F) history

/-- The compiled verifier, with every challenge answered by the history oracle. -/
def verify (application : String) (base key : G) (proof : G × F) :
    OracleComp (HistorySpec F G) Bool :=
  (fun result => accepted (mapOutcome SchnorrProof.acceptance result.1, result.2)) <$>
    ideal SchnorrProof.context historyChallenge SchnorrProof.table SchnorrProof.participant.returned
      SchnorrProof.participant.instructions
      ((SchnorrProof.inputs base key).map .data ++ [.transcript (initial application base key)])
      [.group groupDomain proof.1, .field fieldDomain proof.2]

omit [SampleableType F] [SampleableType G] in
/-- The compiled verifier asks one challenge, at its initialized transcript
followed by the commitment, and checks the Schnorr equation. -/
theorem verify_eq (application : String) (base key : G) (proof : G × F) :
    verify application base key proof =
      historyChallenge (initial application base key ++
          [.message commitmentOrigin (.group groupDomain proof.1), .challenge challengeOrigin]) >>=
        fun answer => pure (decide (proof.2 • base = proof.1 + answer • key)) := by
  have compiled := SchnorrProof.compiled_transform (historyChallenge (F := F) (G := G)) base key 0
    (initial application base key) [.group groupDomain proof.1, .field fieldDomain proof.2]
  rw [SchnorrProof.verifier_correspondence, transform_experiment] at compiled
  have projected : verify application base key proof = accepted <$>
      ((fun result => (mapOutcome SchnorrProof.acceptance result.1, result.2)) <$>
        ideal SchnorrProof.context historyChallenge SchnorrProof.table SchnorrProof.participant.returned
          SchnorrProof.participant.instructions
          ((SchnorrProof.inputs base key).map .data ++ [.transcript (initial application base key)])
          [.group groupDomain proof.1, .field fieldDomain proof.2]) := by
    simp only [verify, Functor.map_map]
  rw [projected, compiled]
  simp [accepted]

/-- Route each history query to its oracle key; uniform coins pass through. -/
def routeQueries : QueryImpl (HistorySpec F G) (OracleComp (KeySpec F G)) :=
  (fun n => (liftM (unifSpec.query n) : OracleComp (KeySpec F G) (Fin (n + 1)))) +
    (fun history => (liftM ((Key F G →ₒ F).query (route history)) : OracleComp (KeySpec F G) F))

omit [Field F] [DecidableEq F] [Module F G] [DecidableEq G] [SampleableType F]
  [SampleableType G] in
theorem routeQueries_inl (n : ℕ) :
    routeQueries (F := F) (G := G) (.inl n) =
      (liftM (unifSpec.query n) : OracleComp (KeySpec F G) (Fin (n + 1))) := rfl

omit [Field F] [DecidableEq F] [Module F G] [DecidableEq G] [SampleableType F]
  [SampleableType G] in
theorem routeQueries_inr (history : History F G) :
    routeQueries (.inr history) =
      (liftM ((Key F G →ₒ F).query (route history)) : OracleComp (KeySpec F G) F) := rfl

/-- A prover with uniform coins and the transcript oracle on every history. -/
abbrev Prover (F G : Type) := G → History F G → OracleComp (HistorySpec F G) (G × F)

/-- The same prover, querying VCVio's oracle through the routing. -/
def reduce (prover : Prover F G) :
    _root_.FiatShamir.KnowledgeProver G G F F (History F G ⊕ History F G) :=
  fun key message => simulateQ routeQueries (prover key (message.elim id id))

omit [Field F] [DecidableEq F] [Module F G] [DecidableEq G] [SampleableType F]
  [SampleableType G] in
theorem route_challenge {history : History F G} {key : Key F G}
    (routed : route history = key) :
    simulateQ routeQueries (historyChallenge history) =
      (liftM ((Key F G →ₒ F).query key) : OracleComp (KeySpec F G) F) := by
  subst routed
  unfold historyChallenge routeQueries
  exact QueryImpl.simulateQ_add_liftM_query_right _ _ history

/-- Routed, the compiled verifier is VCVio's Fiat–Shamir verifier for the
Schnorr Sigma protocol, with the initialized transcript as the context message. -/
theorem route_verify (application : String) (base key : G) (proof : G × F) :
    simulateQ routeQueries (verify application base key proof) =
      (_root_.FiatShamir (m := OracleComp (KeySpec F G)) (_root_.Schnorr.sigma F G base)
        (generable base) (History F G ⊕ History F G)).verify key
        (.inl (initial application base key)) proof := by
  rw [verify_eq]
  rcases proof with ⟨commitment, response⟩
  have routed : route (initial application base key ++
      [.message commitmentOrigin (.group groupDomain commitment), .challenge challengeOrigin]) =
        ((.inl (initial application base key), commitment) : Key F G) := by
    simp [route, challengeKey_append]
  simp only [simulateQ_bind, route_challenge routed, simulateQ_pure]
  simp [_root_.FiatShamir, _root_.Schnorr.sigma, HasQuery.query, map_eq_bind_pure_comp]

/-- The transcript oracle's cache, on histories. -/
abbrev Cache (F G : Type) := (History F G →ₒ F).QueryCache

def forwardUniform :
    QueryImpl unifSpec (StateT (Cache F G) (OracleComp (_root_.FiatShamir.Fork.wrappedSpec F))) :=
  fun n => StateT.lift (_root_.FiatShamir.Fork.wrappedUniformQuery F n)

/-- One lazily sampled oracle on histories: a new history receives a fresh
uniform challenge, a repeated one its recorded answer. -/
def historyOracle :
    QueryImpl (History F G →ₒ F)
      (StateT (Cache F G) (OracleComp (_root_.FiatShamir.Fork.wrappedSpec F))) :=
  QueryImpl.withCaching (fun _ => _root_.FiatShamir.Fork.wrappedChallengeQuery F)

/-- The prover sees the statement and initialized transcript; its coins and
oracle queries precede final verification in one initially empty cache. -/
def run (prover : Prover F G) (application : String) (base key : G) :
    OracleComp (_root_.FiatShamir.Fork.wrappedSpec F) Bool :=
  StateT.run' (simulateQ (forwardUniform (F := F) (G := G) + historyOracle (F := F) (G := G)) (do
    let proof ← prover key (initial application base key)
    verify application base key proof)) (∅ : Cache F G)

/-- The experiment is exactly VCVio's Fiat–Shamir verification run for the
routed prover: the routed cache restricted to histories is the history cache. -/
theorem run_eq (prover : Prover F G) (application : String) (base key : G) :
    run prover application base key =
      _root_.FiatShamir.knowledgeVerifyRun (_root_.Schnorr.sigma F G base) (generable base)
        (History F G ⊕ History F G) (reduce prover) key (.inl (initial application base key)) := by
  unfold run _root_.FiatShamir.knowledgeVerifyRun
  have routed : (do
      let proof ← reduce prover key (.inl (initial application base key))
      (_root_.FiatShamir (_root_.Schnorr.sigma F G base) (generable base)
        (History F G ⊕ History F G)).verify key (.inl (initial application base key)) proof) =
      simulateQ routeQueries (do
        let proof ← prover key (initial application base key)
        verify application base key proof) := by
    simp only [simulateQ_bind, reduce, Sum.elim_inl, id, route_verify]
  rw [routed, ← QueryImpl.simulateQ_compose]
  symm
  have projected := run'_simulateQ_eq_of_query_map_eq
    ((_root_.FiatShamir.Fork.unifForward (History F G ⊕ History F G) G F +
      _root_.FiatShamir.Fork.roImpl (History F G ⊕ History F G) G F) ∘ₛ routeQueries)
    (forwardUniform (F := F) (G := G) + historyOracle (F := F) (G := G))
    (fun state : _root_.FiatShamir.Fork.SimState (History F G ⊕ History F G) G F =>
      view route state.1) ?step
    (do
      let proof ← prover key (initial application base key)
      verify application base key proof) (∅, [])
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
        cases hit : cache (route history) with
        | some answer =>
            have viewed : view route cache history = some answer := hit
            rw [_root_.FiatShamir.Fork.roImpl_run_some _ _ _ _ _ hit, QueryImpl.add_apply_inr,
              historyOracle, QueryImpl.withCaching_run_some _ viewed]
            simp
        | none =>
            have viewed : view route cache history = none := hit
            rw [_root_.FiatShamir.Fork.roImpl_run_none _ _ _ _ hit, QueryImpl.add_apply_inr,
              historyOracle, QueryImpl.withCaching_run_none _ viewed]
            simp [map_eq_bind_pure_comp, view_cacheQuery route route_injective]

omit [Field F] [DecidableEq F] [Module F G] [DecidableEq G] [SampleableType F]
  [SampleableType G] in
/-- Routing issues exactly one Fiat–Shamir oracle query per history query and no
other oracle query. -/
theorem reduce_bound (prover : Prover F G) (key : G) (message : History F G) (budget : Nat)
    (bounded : IsQueryBoundP (prover key message) (· matches .inr _) budget) :
    _root_.FiatShamir.nmaHashQueryBound (M := History F G ⊕ History F G)
      (reduce prover key (.inl message)) budget := by
  unfold _root_.FiatShamir.nmaHashQueryBound reduce
  refine IsQueryBoundP.simulateQ_of_step bounded ?_ ?_
  · intro query oracle
    cases query with
    | inl n => cases oracle
    | inr history =>
        change IsQueryBoundP (liftM ((KeySpec F G).query (.inr (route history))) :
          OracleComp (KeySpec F G) F) _ 1
        simp
  · intro query notOracle
    cases query with
    | inl n =>
        change IsQueryBoundP (liftM ((KeySpec F G).query (.inl n)) :
          OracleComp (KeySpec F G) (Fin (n + 1))) _ 0
        simp
    | inr history => exact absurd rfl notOracle

local instance : ∀ t, MeasurableSpace ((_root_.FiatShamir.Fork.wrappedSpec F).Range t) :=
  fun _ => ⊤
local instance : ∀ t, DiscreteMeasurableSpace ((_root_.FiatShamir.Fork.wrappedSpec F).Range t) :=
  fun _ => inferInstance
noncomputable local instance : IsUniformMeasureSpec (_root_.FiatShamir.Fork.wrappedSpec F) :=
  IsUniformMeasureSpec.ofFiniteNonempty _

/-- Probability that the compiled verifier accepts the prover's proof. -/
noncomputable def acceptance (prover : Prover F G) (application : String) (base key : G) :
    ENNReal :=
  Pr{let result ← run prover application base key}[result = true]

variable [Fintype F] [Inhabited F]

/-- Knowledge soundness of the compiled non-interactive Schnorr verifier under
the named assumptions above, for every prover with the transcript oracle on all
histories. `budget` bounds the prover's oracle queries, including repeated
histories; final verification adds one. The extractor runs VCVio's replay
reduction on the routed prover, and the conclusion is the authored relation
retained by the Proof Entry's own export (`SchnorrProofBinding.Relation`, equal
to the Interactive import's by `relation_iff_interactive`). Subtraction is
truncated in `ENNReal`. -/
theorem knowledge_soundness (prover : Prover F G) (application : String) (base key : G)
    (budget : Nat)
    (bounded : IsQueryBoundP (prover key (initial application base key)) (· matches .inr _) budget) :
    let accepting := acceptance prover application base key
    accepting * (accepting / (budget + 1 : ENNReal) - _root_.FiatShamir.challengeSpaceInv F) ≤
      Pr{let witness ← _root_.FiatShamir.knowledgeExtractor (_root_.Schnorr.sigma F G base)
          (generable base) (History F G ⊕ History F G) (reduce prover)
          (.inl (initial application base key)) budget key}[
        ZkcExamples.Construction.SchnorrProofBinding.Relation base key witness] := by
  have upstream := _root_.FiatShamir.knowledgeExtractor_success (_root_.Schnorr.sigma F G base)
    (generable base) (History F G ⊕ History F G) (_root_.Schnorr.sigma_speciallySound F G base)
    (reduce prover) key (.inl (initial application base key)) budget
    (reduce_bound prover key _ budget bounded)
  have same : acceptance prover application base key =
      _root_.FiatShamir.knowledgeAcceptance (_root_.Schnorr.sigma F G base) (generable base)
        (History F G ⊕ History F G) (reduce prover) key (.inl (initial application base key)) := by
    unfold acceptance _root_.FiatShamir.knowledgeAcceptance
    rw [run_eq]
  simp only [same]
  simpa only [ZkcExamples.Construction.SchnorrProofBinding.relation_eq] using upstream

end Experiment

end ZkcSecurity.Examples.CompiledSchnorrFiatShamir
