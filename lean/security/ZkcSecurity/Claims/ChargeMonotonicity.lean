module

public import ZkcSecurity.ProgramLogic.Transcript.Interface

@[expose] public section

/-! Decreasing oracle prices preserves a pathwise budget. This theorem is
separate from validator-cost transport: increasing prices cannot preserve a
validator cost bound. -/

set_option autoImplicit false
namespace ZkcSecurity.Claims
open OracleComp OracleSpec

private theorem largerCostSupport {ι α : Type} {spec : OracleSpec ι}
    (small large : CostModel spec ENNReal) (prices : ∀ key, small.queryCost key ≤ large.queryCost key)
    (computation : OracleComp spec α) :
    ∀ result ∈ support (costDist computation small),
      ∃ larger ∈ support (costDist computation large), larger.1 = result.1 ∧
        Multiplicative.toAdd result.2 ≤ Multiplicative.toAdd larger.2 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro result member
    have same : result = (value, Multiplicative.ofAdd (0 : ENNReal)) := by
      simpa [costDist, instrumentedRun] using member
    subst result
    exact ⟨_, by simp [costDist, instrumentedRun], rfl, le_rfl⟩
  | query_bind key next ih =>
    intro result member
    rw [costDist_query_bind, mem_support_bind_iff] at member
    obtain ⟨reply, _, member⟩ := member
    rw [support_map] at member
    obtain ⟨tail, member, rfl⟩ := member
    obtain ⟨larger, largerMember, same, bounded⟩ := ih reply tail member
    refine ⟨(larger.1, Multiplicative.ofAdd (large.queryCost key + Multiplicative.toAdd larger.2)), ?_, same,
      add_le_add (prices key) bounded⟩
    rw [costDist_query_bind, mem_support_bind_iff]
    refine ⟨reply, ?_, ?_⟩
    · simp
    · rw [support_map]
      exact ⟨larger, largerMember, rfl⟩

theorem worstCaseCostBound_mono_charge {ι α : Type} {spec : OracleSpec ι}
    (small large : CostModel spec ENNReal) (prices : ∀ key, small.queryCost key ≤ large.queryCost key)
    (computation : OracleComp spec α) (cost : ENNReal)
    (bounded : WorstCaseCostBound computation large cost) : WorstCaseCostBound computation small cost := by
  rw [worstCaseCostBound_iff_support_bound] at bounded ⊢
  intro result member
  obtain ⟨larger, largerMember, _, le⟩ := largerCostSupport small large prices computation result member
  exact le.trans (bounded larger largerMember)

theorem keyCharge_mono {E : Type} {small large : List E → E → ENNReal}
    (prices : ∀ history event, small history event ≤ large history event) (key : List E) :
    ZkcSecurity.FiatShamir.Typed.keyCharge small key ≤ ZkcSecurity.FiatShamir.Typed.keyCharge large key := by
  unfold ZkcSecurity.FiatShamir.Typed.keyCharge
  cases key.getLast? with
  | none => exact le_rfl
  | some event => exact prices _ event

/-- Increasing only the numerical budget preserves a validator cost bound at
the same prices. It says nothing about increasing the prices themselves. -/
theorem chargedCostBound_mono_bound {I : PIR.Signature} {E P A : Type} {Raw : E → Type}
    (absorb : ZkcSecurity.FiatShamir.Typed.Interface I E P Raw) (charge : List E → E → ENNReal) :
    ∀ (process : PIR.Process I A) (history : List E) (small large : ENNReal),
      ZkcSecurity.FiatShamir.Typed.ChargedCostBound absorb charge process history small → small ≤ large →
        ZkcSecurity.FiatShamir.Typed.ChargedCostBound absorb charge process history large
  | .done _, _, _, _, _, _ => trivial
  | .halt _, _, _, _, _, _ => trivial
  | .call operation next, history, small, large, bounded, le => by
    open ZkcSecurity.FiatShamir in
    rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ | ⟨event, decode⟩ | _
    · simp only [Typed.ChargedCostBound, absorbed] at bounded ⊢
      exact fun message value recovered => chargedCostBound_mono_bound absorb charge (next value)
        _ small large (bounded message value recovered) le
    · simp only [Typed.ChargedCostBound, absorbed] at bounded ⊢
      exact chargedCostBound_mono_bound absorb charge (next value) _ small large bounded le
    · simp only [Typed.ChargedCostBound, absorbed] at bounded ⊢
      obtain ⟨remaining, charged, rest⟩ := bounded
      exact ⟨remaining, charged.trans le, rest⟩
    · simp only [Typed.ChargedCostBound, absorbed]

end ZkcSecurity.Claims
