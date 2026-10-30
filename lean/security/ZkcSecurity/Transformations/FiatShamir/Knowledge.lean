module

public import ZkcSecurity.Transformations.FiatShamir.Transcript
public import ZkcSecurity.Transformations.FiatShamir.Replay
public import ZkcSecurity.Mathematics.Oracle.Encoding
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
public import VCVio.OracleComp.SimSemantics.QueryImpl.Compose

@[expose] public section

open scoped ZkcSecurity.VCVio.UniformChallenge

/-! Sigma correspondence and special soundness justify the fixed oracle and
replay experiments. Operational clients import the lower interfaces directly. -/

set_option autoImplicit false

namespace ZkcSecurity.Endpoint.Sigma
open OracleComp OracleSpec
open Zkc.Construction
open ZkcSecurity.Oracle.Encoding (view view_cacheQuery)

namespace Shape
variable {F G Commit Resp : Type} [DecidableEq F] [DecidableEq G] (shape : Shape F G Commit Resp)

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

set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
namespace ZkcSecurity.Endpoint.Extraction
open OracleComp OracleSpec

section Replay
variable {F Commit Resp Wit M : Type} [DecidableEq M] [DecidableEq Commit]
  [DecidableEq F] [SampleableType F] [SampleableType Wit]

/-- Operational compatibility requires no special-soundness assumption. -/
theorem replay_eq {Stmt PrvState : Type} {relation : Stmt → Wit → Bool}
    (sigma : SigmaProtocol Stmt Wit Commit PrvState F Resp relation)
    (generable : GenerableRelation Stmt Wit relation)
    (prover : _root_.FiatShamir.KnowledgeProver Stmt Commit F Resp M)
    (statement : Stmt) (message : M) (queries : Nat) :
    replay (fun cache commitment response => match cache (message, commitment) with
      | some challenge => sigma.verify statement commitment challenge response
      | none => false) sigma.extract (prover statement) message queries =
      _root_.FiatShamir.knowledgeExtractor sigma generable M prover message queries statement := by
  have trace : runTrace (fun cache commitment response => match cache (message, commitment) with
      | some challenge => sigma.verify statement commitment challenge response
      | none => false) (prover statement) message =
      _root_.FiatShamir.Fork.runTrace sigma generable M
        (_root_.FiatShamir.proverWithFinalQuery sigma generable M prover message) statement := by
    simp only [runTrace, _root_.FiatShamir.Fork.runTrace, _root_.FiatShamir.proverWithFinalQuery,
      simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, monad_norm]
    apply bind_congr
    intro first
    apply bind_congr
    intro second
    cases second.2.1 (message, first.1.1) <;> rfl
  have branch : recoverFork (M := M) sigma.extract =
      _root_.FiatShamir.nmaForkExtractBranch (M := M) sigma := by
    funext pair
    cases pair with
    | none => rfl
    | some pair =>
      rcases pair with ⟨⟨⟨m₁, c₁, s₁⟩, a₁, r₁, l₁, v₁⟩, ⟨⟨m₂, c₂, s₂⟩, a₂, r₂, l₂, v₂⟩⟩
      simp only [recoverFork, _root_.FiatShamir.nmaForkExtractBranch, _root_.FiatShamir.Fork.Trace.target, dite_eq_ite]
      by_cases same : c₁ = c₂
      · simp only [same, ite_true]
        cases r₁ (m₁, c₁) <;> cases r₂ (m₂, c₂) <;> rfl
      · simp only [same, ite_false]
  unfold replay _root_.FiatShamir.knowledgeExtractor _root_.FiatShamir.nmaReduction
    _root_.FiatShamir.nmaForkExtract
  rw [trace, branch]

end Replay
end ZkcSecurity.Endpoint.Extraction
