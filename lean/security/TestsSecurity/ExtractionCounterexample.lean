import ZkcSecurity.Endpoint.Extraction
import Mathlib.Data.ZMod.Basic
open OracleComp OracleSpec ZkcSecurity.Endpoint.Extraction

/-! A total-relation control for the actual generic replay implementation.
This is an operational fixture, not a generated compiled Subject. The bounds
use the same native event probabilities as the endpoint. -/

set_option autoImplicit false
set_option maxRecDepth 2048
namespace TestsSecurity.ExtractionCounterexample

abbrev F := ZMod 7
instance : Fact (Nat.Prime 7) := ⟨by decide⟩

def prover (_ : Unit) :
    OracleComp (unifSpec + (Unit × Unit →ₒ F)) (Unit × F) :=
  pure ((), 0)

def verify (_ : (Unit × Unit →ₒ F).QueryCache)
    (_ : Unit) (_ : F) : Bool := true

def main := runTrace verify prover ()

theorem no_queries :
    IsQueryBoundP (prover ()) (· matches .inr _) 0 := by trivial

theorem trace_zero (t : FiatShamir.Fork.Trace Unit F F Unit)
    (h : t ∈ support main) : t.forgery.2.2 = 0 := by
  simp only [main, runTrace, prover, simulateQ_bind, simulateQ_pure,
    StateT.run_bind, StateT.run_pure, monad_norm] at h
  simp only [mem_support_bind_iff, mem_support_pure_iff] at h
  rcases h with ⟨a, _, rfl⟩
  rfl

theorem simulate_support_subset {α : Type} {ι : Type}
    {spec : OracleSpec ι} (impl : QueryImpl spec ProbComp)
    (oa : OracleComp spec α) :
    support (simulateQ impl oa) ⊆ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t next ih =>
    intro x hx
    simp only [simulateQ_bind, simulateQ_spec_query,
      mem_support_bind_iff] at hx
    obtain ⟨u, _, hu⟩ := hx
    exact (mem_support_bind_iff _ _ _).mpr
      ⟨u, mem_support_query t u, ih u hu⟩

def handler : QueryImpl (FiatShamir.Fork.wrappedSpec F) ProbComp :=
  QueryImpl.ofLift unifSpec ProbComp +
    uniformSampleImpl (spec := Unit →ₒ F)

def difference (c z d w : F) : ProbComp F :=
  pure ((z - w) / (c - d))

def fork := contextFork main (FiatShamir.nmaForkBudget 0) (.inr ())
  (FiatShamir.Fork.forkPoint Unit F F Unit 0)

theorem fork_zero {t₁ t₂ : FiatShamir.Fork.Trace Unit F F Unit}
    (h : some (t₁, t₂) ∈ support fork) :
    t₁.forgery.2.2 = 0 ∧ t₂.forgery.2.2 = 0 := by
  obtain ⟨path, s, located, second, _, _, _, _, _, h₁, h₂⟩ :=
    contextFork_success main (FiatShamir.nmaForkBudget 0) (.inr ())
      (FiatShamir.Fork.forkPoint Unit F F Unit 0) h
  have output_zero (p : PFunctor.FreeM.Path main) :
      (PFunctor.FreeM.output main p).forgery.2.2 = 0 := by
    apply trace_zero
    rw [PFunctor.FreeM.support_eq_range_output]
    exact ⟨p, rfl⟩
  exact ⟨h₁ ▸ output_zero path, h₂ ▸ output_zero second.path⟩

theorem fallback_prob (y : F) :
    Pr{let x ← (simulateQ handler
      (liftComp ($ᵗ F) (FiatShamir.Fork.wrappedSpec F)))}[x = y] =
      1 / 7 := by
  rw [handler, QueryImpl.simulateQ_add_liftComp_left,
    simulateQ_ofLift_eq_self]
  rw [SampleableType.prEvent_uniformSample_eq_singleton]
  norm_num [F, ZMod.card]

theorem branch_bound
    (pair : Option (FiatShamir.Fork.Trace Unit F F Unit ×
      FiatShamir.Fork.Trace Unit F F Unit))
    (zero : ∀ a b, pair = some (a,b) →
      a.forgery.2.2 = 0 ∧ b.forgery.2.2 = 0) :
    Pr{let x ← simulateQ handler (recoverFork difference pair)}[
      x = (1 : F)] ≤ 1 / 7 := by
  cases pair with
  | none => exact (fallback_prob 1).le
  | some pair =>
    rcases pair with ⟨a,b⟩
    obtain ⟨ha,hb⟩ := zero a b rfl
    simp only [recoverFork]
    split
    · cases hleft : a.roCache a.target <;>
        cases hright : b.roCache b.target
      all_goals simp only
      all_goals first
      | exact (fallback_prob 1).le
      | split
        · simp [difference, ha, hb]
        · exact (fallback_prob 1).le
    · exact (fallback_prob 1).le

theorem extraction_bound :
    Pr{let x ← replay verify difference prover () 0}[
      x = (1 : F)] ≤ 1 / 7 := by
  unfold replay
  rw [simulateQ_bind]
  apply prEvent_bind_le_of_forall_le_of_support
  intro pair hp
  apply branch_bound
  intro a b hab
  subst pair
  exact fork_zero (simulate_support_subset handler fork hp)

theorem trace_accepts (t : FiatShamir.Fork.Trace Unit F F Unit)
    (h : t ∈ support main) : t.verified = true := by
  simp only [main, runTrace, prover, simulateQ_bind, simulateQ_pure,
    StateT.run_bind, StateT.run_pure, monad_norm] at h
  simp only [mem_support_bind_iff, mem_support_pure_iff] at h
  rcases h with ⟨a, _, rfl⟩
  rfl

theorem acceptance_one :
    Pr{let t ← simulateQ handler main}[t.verified = true] = 1 :=
  prEvent_eq_one_of_forall_mem_support _ _ fun t ht =>
    trace_accepts t (simulate_support_subset handler main ht)

theorem extraction_bound_current_notation :
    Pr{let w ← replay verify difference prover () 0}[w = (1 : F)] ≤
      1 / 7 := extraction_bound

def relation (publicValue witness : F) : Bool :=
  decide (witness = publicValue)

theorem total_relation (publicValue : F) :
    ∃ w, relation publicValue w = true :=
  ⟨publicValue, by simp [relation]⟩

theorem old_search_success (publicValue : F) :
    Pr{let w ← (pure publicValue : ProbComp F)}[
      relation publicValue w = true] = 1 := by
  simp [relation]

def searchSigma (publicValue : F) :
    SigmaProtocol Unit F Unit Unit F F
      (fun _ w => relation publicValue w) where
  commit _ _ := pure ((), ())
  respond _ _ _ _ := pure 0
  verify _ _ _ _ := true
  sim _ := pure ()
  extract _ _ _ _ := pure publicValue

theorem search_special_sound (publicValue : F) :
    (searchSigma publicValue).SpeciallySound := by
  intro x pc c d z w _ _ _ recovered h
  simp only [searchSigma, mem_support_pure_iff] at h
  subst recovered
  simp [relation]

theorem requested_lower_bound :
    (1 : ENNReal) *
      (1 / (0 + 1 : ENNReal) - FiatShamir.challengeSpaceInv F) =
      6 / 7 := by
  norm_num only [FiatShamir.challengeSpaceInv, F, ZMod.card,
    one_mul, Nat.reduceAdd, div_one, Nat.cast_ofNat]
  apply (ENNReal.toReal_eq_toReal_iff'
    (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_sub_of_le]

theorem fixed_guarantee_false :
    ¬ (let accepting :=
          Pr{let t ← simulateQ handler main}[t.verified = true]
      accepting *
        (accepting / (0 + 1 : ENNReal) -
          FiatShamir.challengeSpaceInv F) ≤
        Pr{let w ← replay verify difference prover () 0}[
          relation 1 w = true]) := by
  dsimp only
  simp only [acceptance_one]
  rw [requested_lower_bound]
  intro h
  have hupper :
      Pr{let w ← replay verify difference prover () 0}[
        relation 1 w = true] ≤ 1 / 7 := by
    simpa only [relation, decide_eq_true_eq] using
      extraction_bound_current_notation
  have : (6 / 7 : ENNReal) ≤ 1 / 7 := h.trans hupper
  have realBound := ENNReal.toReal_mono
    (by norm_num : (1 / 7 : ENNReal) ≠ ⊤) this
  norm_num [ENNReal.toReal_div] at realBound

theorem difference_is_registered :
    difference =
      (fun c z d w : F =>
        pure ((Layout.scalar 0).recover c z d w)) := rfl

def trace (challenge : F) : FiatShamir.Fork.Trace Unit F F Unit :=
  ⟨((), (), 0), ∅,
    (∅ : (Unit × Unit →ₒ F).QueryCache).cacheQuery ((), ()) challenge,
    [((), ())], true⟩

theorem main_one_challenge :
    main = (do
      let c ← FiatShamir.Fork.wrappedChallengeQuery F
      pure (trace c)) := by
  rfl

def omittedChallengeTerm
    (_publicValue commitment _challenge response : F) : Bool :=
  decide (response • (1 : F) = commitment)

theorem omitted_accepts (c : F) :
    omittedChallengeTerm 1 0 c 0 = true := by
  simp [omittedChallengeTerm]

theorem fixed_generator_injective :
    Function.Injective (fun w : F => w • (1 : F)) := by
  intro a b h
  simpa only [smul_eq_mul, mul_one] using h

theorem omitted_recovers_wrong :
    ((0 - 0) / (0 - 1) : F) • (1 : F) ≠ 1 := by
  norm_num

def omittedSigma : SigmaProtocol F F F F F F
    (fun y w => decide (w • (1 : F) = y)) where
  commit _ _ := pure (0, 0)
  respond _ _ _ _ := pure 0
  verify := omittedChallengeTerm
  sim _ := pure 0
  extract := difference

theorem omitted_not_special_sound :
    ¬ omittedSigma.SpeciallySound := by
  intro sound
  have bad := sound 1 0 0 1 0 0 (by decide)
    (omitted_accepts 0) (omitted_accepts 1) 0
    (by simp [omittedSigma, difference])
  norm_num at bad

end TestsSecurity.ExtractionCounterexample

#print axioms TestsSecurity.ExtractionCounterexample.fixed_guarantee_false
#print axioms TestsSecurity.ExtractionCounterexample.fork_zero
#print axioms TestsSecurity.ExtractionCounterexample.search_special_sound
#print axioms TestsSecurity.ExtractionCounterexample.omitted_not_special_sound
#print axioms TestsSecurity.ExtractionCounterexample.main_one_challenge
