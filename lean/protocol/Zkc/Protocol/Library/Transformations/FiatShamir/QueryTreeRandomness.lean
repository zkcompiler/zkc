module

public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.EvalDist.IndepProduct
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.OracleComp.SimSemantics.Append.Core
public import ToMathlib.Control.Monad.Fold

@[expose] public section

/-!
# Moving private sampling outside an adaptive oracle computation

Finite oracle replies let us sample the private continuations of every response branch before
interaction. Only the continuation selected by the actual oracle reply is executed. This is
an information-theoretic construction, with no efficiency claim or explicit tree enumeration.
The interpreter theorem allows arbitrary stochastic stateful handlers, including cached and
logged random oracles. Private draws remain independent at each occurrence.
-/

set_option autoImplicit false

namespace ZkcSecurity.FiatShamir.QueryTree
open OracleComp OracleSpec MeasureTheory

/-- Observing one sampled continuation ignores the other independent, lossless choices. -/
theorem finiteChoices_coordinate {Choice α β : Type} [Fintype Choice] [MeasurableSpace β]
    (choices : Choice → ProbComp α) (selected : Choice) (next : α → ProbComp β) :
    𝒟[do let values ← Fintype.mPi choices; next (values selected)] =
      𝒟[choices selected >>= next] := by
  let : MeasurableSpace α := ⊤
  have marginal : (Function.eval selected <$> Fintype.mPi choices) =ᵈ choices selected :=
    EvalDistEq.of_evalDist_eq (by
      rw [evalDist_map _ (measurable_pi_apply selected)]
      exact evalDist_map_eval_mPi choices (fun _ ↦ by simp) selected)
  simpa only [bind_map_left, Function.eval] using (marginal.bind_left next).evalDist_eq

/-- An exact outer mixture of deterministic oracle programs for interleaved private draws.
At an oracle node, independently prepare a private continuation for every possible reply. -/
noncomputable def privateMixture {Key Reply α : Type} [Fintype Reply]
    (program : OracleComp (unifSpec + (Key →ₒ Reply)) α) :
    ProbComp (OracleComp (Key →ₒ Reply) α) :=
  OracleComp.construct (C := fun _ ↦ ProbComp (OracleComp (Key →ₒ Reply) α))
    (fun value ↦ pure (pure value))
    (fun call _ rest ↦ match call with
      | .inl bound => (ProbComp.uniformFin bound) >>= rest
      | .inr key => (fun continuations ↦
          liftM ((Key →ₒ Reply).query key) >>= continuations) <$> Fintype.mPi rest)
    program

@[simp] theorem privateMixture_pure {Key Reply α : Type} [Fintype Reply] (value : α) :
    privateMixture (pure value : OracleComp (unifSpec + (Key →ₒ Reply)) α) =
      pure (pure value) := rfl

@[simp] theorem privateMixture_uniform_bind {Key Reply α : Type} [Fintype Reply]
    (bound : ℕ) (next : Fin (bound + 1) → OracleComp (unifSpec + (Key →ₒ Reply)) α) :
    privateMixture (liftM ((unifSpec + (Key →ₒ Reply)).query (.inl bound)) >>= next) =
      ProbComp.uniformFin bound >>= fun reply ↦ privateMixture (next reply) := rfl

@[simp] theorem privateMixture_oracle_bind {Key Reply α : Type} [Fintype Reply]
    (key : Key) (next : Reply → OracleComp (unifSpec + (Key →ₒ Reply)) α) :
    privateMixture (liftM ((unifSpec + (Key →ₒ Reply)).query (.inr key)) >>= next) =
      (fun continuations ↦ liftM ((Key →ₒ Reply).query key) >>= continuations) <$>
        Fintype.mPi (fun reply ↦ privateMixture (next reply)) := rfl

/-- Exact outer-mixture conversion for every adaptive program and every stateful stochastic
oracle interpreter. The final state is preserved jointly with the result. -/
theorem privateMixture_stateful {Key Reply α State : Type} [Fintype Reply]
    [MeasurableSpace (α × State)]
    (impl : QueryImpl (Key →ₒ Reply) (StateT State ProbComp))
    (program : OracleComp (unifSpec + (Key →ₒ Reply)) α) (state : State) :
    𝒟[(simulateQ (unifSpec.passthrough + impl) program).run state] =
      𝒟[do let fixed ← privateMixture program; (simulateQ impl fixed).run state] := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind call next ih =>
      cases call with
      | inl bound =>
          simp only [privateMixture_uniform_bind, bind_assoc]
          change 𝒟[ProbComp.uniformFin bound >>= fun reply ↦
            (simulateQ (unifSpec.passthrough + impl) (next reply)).run state] = _
          apply evalDist_bind_congr
          intro reply
          exact ih reply state
      | inr key =>
          simp only [privateMixture_oracle_bind, bind_map_left, simulateQ_bind,
            simulateQ_spec_query, StateT.run_bind]
          rw [OracleComp.evalDist_bind_bind_swap]
          apply evalDist_bind_congr
          intro result
          exact (ih result.1 result.2).trans
            (finiteChoices_coordinate (fun reply ↦ privateMixture (next reply)) result.1
              (fun fixed ↦ (simulateQ impl fixed).run result.2)).symm

/-- The outer mixture needs finite replies, without exposing a chosen enumeration in its API. -/
noncomputable def privatePrograms {Key Reply α : Type} [Finite Reply]
    (program : OracleComp (unifSpec + (Key →ₒ Reply)) α) :
    ProbComp (OracleComp (Key →ₒ Reply) α) :=
  letI : Fintype Reply := Fintype.ofFinite Reply
  privateMixture program

/-- Enumeration-hidden form of the exact stateful private-randomness conversion. -/
theorem privatePrograms_stateful {Key Reply α State : Type} [Finite Reply]
    [MeasurableSpace (α × State)]
    (impl : QueryImpl (Key →ₒ Reply) (StateT State ProbComp))
    (program : OracleComp (unifSpec + (Key →ₒ Reply)) α) (state : State) :
    𝒟[(simulateQ (unifSpec.passthrough + impl) program).run state] =
      𝒟[do let fixed ← privatePrograms program; (simulateQ impl fixed).run state] := by
  let : Fintype Reply := Fintype.ofFinite Reply
  exact privateMixture_stateful impl program state

/-- Moving private choices outside a program preserves every structural budget on its
oracle queries. Private draws are free in this budget, and every possible reply branch is
still covered. The conclusion holds for every fixed program in the mixture's support. -/
theorem privateMixture_queryBound {Key Reply α B : Type} [Fintype Reply]
    (program : OracleComp (unifSpec + (Key →ₒ Reply)) α)
    (canQuery : Key → B → Prop) (cost : Key → B → B) {budget : B}
    (bounded : IsQueryBound program budget
      (Sum.elim (fun _ _ ↦ True) canQuery) (Sum.elim (fun _ remaining ↦ remaining) cost))
    {fixed : OracleComp (Key →ₒ Reply) α}
    (sampled : fixed ∈ support (privateMixture program)) :
    IsQueryBound fixed budget canQuery cost := by
  induction program using OracleComp.inductionOn generalizing budget fixed with
  | pure value =>
      simp only [privateMixture_pure, mem_support_pure_iff] at sampled
      subst fixed
      exact isQueryBound_pure _ _ _ _
  | query_bind call next ih =>
      rcases (isQueryBound_query_bind_iff _ _ _ _ _).mp bounded with ⟨allowed, rest⟩
      cases call with
      | inl bound =>
          rw [privateMixture_uniform_bind, mem_support_bind_iff] at sampled
          obtain ⟨reply, _, member⟩ := sampled
          exact ih reply (rest reply) member
      | inr key =>
          rw [privateMixture_oracle_bind] at sampled
          rw [support_map] at sampled
          obtain ⟨continuations, member, rfl⟩ := sampled
          refine (isQueryBound_query_bind_iff _ _ _ _ _).mpr ⟨allowed, ?_⟩
          intro reply
          exact ih reply (rest reply) (mem_support_mPi _ _ member reply)

/-- Enumeration-hidden budget transport for arbitrary finite oracle replies. -/
theorem privatePrograms_queryBound {Key Reply α B : Type} [Finite Reply]
    (program : OracleComp (unifSpec + (Key →ₒ Reply)) α)
    (canQuery : Key → B → Prop) (cost : Key → B → B) {budget : B}
    (bounded : IsQueryBound program budget
      (Sum.elim (fun _ _ ↦ True) canQuery) (Sum.elim (fun _ remaining ↦ remaining) cost))
    {fixed : OracleComp (Key →ₒ Reply) α}
    (sampled : fixed ∈ support (privatePrograms program)) :
    IsQueryBound fixed budget canQuery cost := by
  let : Fintype Reply := Fintype.ofFinite Reply
  exact privateMixture_queryBound program canQuery cost bounded sampled

end ZkcSecurity.FiatShamir.QueryTree
