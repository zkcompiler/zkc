module

public import ZkcSecurity.Examples.Components.SumcheckSoundnessRoots
public import ZkcSecurity.Claims.CompiledSoundness

@[expose] public section

/-! Actual-root adaptive controls: repeated cached queries precede statement
choice; malformed tables and counts remain typed, fully public inputs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 50000
noncomputable section
namespace TestsSecurity.SumcheckAdaptiveSoundness
open Zkc.Source Zkc.Source.Structured Zkc.Construction OracleComp OracleSpec
open ZkcSecurity.FiatShamir
open ZkcSecurity.Examples.Components
open SumcheckSoundnessRoots
open ZkcSecurity.Families.Sumcheck
local instance : DecidableEq (Domain.Event carriers) := Classical.decEq _
local instance : ∀ event : Domain.Event carriers, SampleableType (Domain.Raw event) :=
  ZkcSecurity.Domains.PrimeField.rawSampleable blsModulus

abbrev origin := TwoSums.ValidatorLeftRound.queryOrigin 0

def chooseStatement (value : Scalar) : Two.Statement :=
  if value = 0 then ZkcSecurity.Examples.Generated.Components.TwoSumsABI.statement [] [] 1 1 0
  else if value = 1 then ZkcSecurity.Examples.Generated.Components.TwoSumsABI.statement [0, 0, 0, 0, 0, 0] [0] 1 1 2
  else if value = 2 then ZkcSecurity.Examples.Generated.Components.TwoSumsABI.statement [0, 0, 0, 0] [0, 0, 0, 0] 1 1 1
  else ZkcSecurity.Examples.Generated.Components.TwoSumsABI.statement [0] [0] 1 1 99

def adaptiveProver : OracleComp (HonestCompiled.Spec carriers) (Two.Statement × Domain.Proof carriers) := do
  let first ← Typed.ask (Raw := @Domain.Raw carriers) (R := Typed.ByLast Domain.Raw) [] (.challenge origin)
  let _ ← Typed.ask (Raw := @Domain.Raw carriers) (R := Typed.ByLast Domain.Raw) [] (.challenge origin)
  let value : Scalar := by
    simpa only [origin, Domain.Raw, TwoSums.ValidatorLeftRound.query_request, Request.draw] using first
  pure (chooseStatement value, [.field "bls12-381.fr" value, .field "bls12-381.fr" (1 - value)])

theorem repeated_log (table : (key : Domain.History carriers) → Typed.ByLast Domain.Raw key) :
    tableQueryLog adaptiveProver table =
      [⟨[.challenge origin], table [.challenge origin]⟩,
        ⟨[.challenge origin], table [.challenge origin]⟩] := by
  simp [adaptiveProver, Typed.ask, Typed.answer, bind_map_left, Typed.tableQueryLog_map]

theorem counted : IsTotalQueryBound adaptiveProver 2 := by
  simp [adaptiveProver, Typed.ask, Typed.answer, map_eq_bind_pure_comp, isTotalQueryBound_query_bind_iff]
  intro _
  trivial

/-- Two visits to one cache key still consume two adversary queries. -/
theorem undercount_rejected : ¬ IsTotalQueryBound adaptiveProver 1 := by
  simp [adaptiveProver, Typed.ask, Typed.answer, map_eq_bind_pure_comp, isTotalQueryBound_query_bind_iff]

example (history : Domain.History carriers) :
    SmallSumcheck.Validator.presented ([0, 0, 0, 0, 0, 0] : List Scalar) 1 99 history =
      .halt .refused := rfl

example (history : Domain.History carriers) :
    TwoSums.Validator.presented ([0] : List Scalar) [0] 1 1 99 history = .halt .refused := rfl

/-- The proved actual adaptive bound is applied to a prover that queries twice
before selecting even malformed public statements and a malicious proof. -/
example (application : String) :
    Pr{let result ← (simulateQ randomOracle
      (adaptiveProver >>= fun claimed => (fun result => (claimed.1, result)) <$>
        ZkcSecurity.Examples.Generated.TwoSums.validatorCompiled.verifier
          ZkcSecurity.Domains.PrimeField.blsScalarModel (Typed.ask (R := Typed.ByLast Domain.Raw)) claimed.1
          ((ZkcSecurity.Claims.CompiledSoundness.binding ZkcSecurity.Examples.Generated.TwoSums.validatorSubject application).encode claimed.1) claimed.2)).run' ∅}[
      ZkcSecurity.Examples.Generated.TwoSums.validatorSubject.FalseStatement result.1 ∧
      ZkcSecurity.Endpoint.Domain.CompleteAccepted result.2] ≤
        ((2 : ENNReal) + 8) / (Fintype.card Scalar : ENNReal) :=
  Two.adaptive application 2 adaptiveProver counted

example : chooseStatement 0 = ZkcSecurity.Examples.Generated.Components.TwoSumsABI.statement [] [] 1 1 0 := by
  simp [chooseStatement]
example : chooseStatement 1 = ZkcSecurity.Examples.Generated.Components.TwoSumsABI.statement [0, 0, 0, 0, 0, 0] [0] 1 1 2 := by
  simp [chooseStatement]
example : chooseStatement 2 = ZkcSecurity.Examples.Generated.Components.TwoSumsABI.statement [0, 0, 0, 0] [0, 0, 0, 0] 1 1 1 := by
  have zero : (2 : Scalar) ≠ 0 := by decide +kernel
  have one : (2 : Scalar) ≠ 1 := by decide +kernel
  simp [chooseStatement, zero, one]

example (history : Domain.History carriers) :
    Two.schedule.charge 2 history (.challenge { origin with entry := "unmapped" }) = price := by
  rw [ZkcSecurity.Claims.CompiledSoundness.charge_constant Two.schedule 2 price (Two.schedule_prices 2)]

#print axioms Two.reductionExport
#print axioms Small.reductionExport
#print axioms Two.adaptive
#print axioms Small.adaptive
#print axioms repeated_log
#print axioms undercount_rejected
end TestsSecurity.SumcheckAdaptiveSoundness
