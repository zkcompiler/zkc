module

public import ZkcSecurityExamples.EmbeddingEquality
public import ZkcSecurityExamples.EmbeddingEqualityDomains

@[expose] public section

/-! Zero error against arbitrary permitted ideal-oracle adversaries, using the
existing typed reduction engine and the actual compiled verifier equation. -/
set_option autoImplicit false
noncomputable section

namespace ZkcSecurity.Examples.EmbeddingEquality
open Zkc Zkc.Construction ZkcSecurity.FiatShamir OracleComp OracleSpec
open ZkcSecurity.Domains.KoalaBearModel (model)
open ZkcExamples.Construction.EmbeddingEqualityBinding (context)

local instance : DecidableEq Event := Classical.decEq _
local instance : (event : Event) → SampleableType (Domain.Raw event) :=
  EmbeddingEqualityDomains.rawSampleable

abbrev OracleAnswers := Typed.ByLast (@Domain.Raw model.toCarriers)
abbrev Oracle := OracleSpec.ofFn OracleAnswers

theorem verifier_safe (a b : Base) (different : a ≠ b) :
    PIR.Yields (fun value => value ≠ some true) (verifierView a b) := by
  intro u c delivery accepted
  exact different (decision_sound a b u c (Option.some.inj accepted))

def reduction : Typed.Reduction (Domain.interface (carriers := model.toCarriers) context)
    (fun _ value => value ≠ some true) (fun _ _ => 0) :=
  Endpoint.Domain.safetyReduction (Domain.interface (carriers := model.toCarriers) context) (fun value => value ≠ some true)

def certificate : Typed.ChargedCertificate (Domain.interface (carriers := model.toCarriers) context)
    (· = some true) (fun _ _ => 0) :=
  reduction.toCertificate _ (fun _ _ rejected => rejected)

theorem certificate_contains (a b : Base) (different : a ≠ b) (initial : History) :
    certificate.doomed initial (verifierView a b) := verifier_safe a b different

theorem zero_key_charge : Typed.keyCharge (fun (_ : History) (_ : Event) => 0) =
    fun _ => 0 := by
  funext key
  unfold Typed.keyCharge
  cases key.getLast? <;> rfl

/-- The adversary can query any typed history and choose any proof. Zero local
charge needs no bound on its finite oracle computation. The same lazy oracle
cache serves the adversary and the interpreted compiled validator. -/
theorem compiled_ideal_soundness (a b : Base) (different : a ≠ b) (initial : History)
    (prover : OracleComp Oracle Proof) :
    Pr{let result ← (simulateQ randomOracle
      (prover >>= verifier (Typed.ask (R := OracleAnswers)) a b initial)).run' ∅}[Endpoint.Domain.CompleteAccepted result] = 0 := by
  have proverBound : WorstCaseCostBound prover
      ⟨Typed.keyCharge (fun (_ : History) (_ : Event) => 0)⟩ 0 := by
    rw [zero_key_charge]
    exact Endpoint.Domain.zero_prover_cost prover
  have bound := Typed.soundness_charged certificate (verifierView a b) initial
    (certificate_contains a b different initial) 0
    (Endpoint.Domain.zero_validator_cost _ _ _) prover 0 proverBound
  have same : (prover >>= verifier (Typed.ask (R := OracleAnswers)) a b initial) =
      Typed.fixedExperiment (Domain.interface (carriers := model.toCarriers) context) (verifierView a b) initial prover := by
    apply congrArg (Bind.bind prover)
    funext proof
    exact compiled_verifier_eq _ _ _ _ _
  rw [same]
  apply le_antisymm _ zero_le
  exact (prEvent_mono _ _ _ (fun _ accepted => accepted.1)).trans
    (by simpa using bound)

end ZkcSecurity.Examples.EmbeddingEquality
