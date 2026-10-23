module

public import ZkcSecurity.FiatShamir.DomainReduction
public import ZkcSecurity.FiatShamir.Binding

@[expose] public section

/-! Adaptive statement choice on the same nominal history oracle. The adversary
queries first and returns the statement and proof together. Statement
determination and the actual per-history charges remain explicit obligations. -/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.DomainReduction.Compiled
open Zkc.Source Zkc.Construction OracleComp OracleSpec
variable {model : Structured.DomainModel} {art : ZkcSecurity.Endpoint.Domain.Artifacts}
variable (compiled : ZkcSecurity.Endpoint.Domain.Compiled art)
variable {I : PIR.Signature}
variable {absorb : Typed.Interface I (Domain.Event model.toCarriers)
  (Domain.Payload model.toCarriers) Domain.Raw}
variable {ReadPost : art.Statement model → Domain.History model.toCarriers → Domain.Result model.toCarriers → Prop}
variable (initial : art.Statement model → Domain.History model.toCarriers)
variable (inputs : art.Statement model → Domain.Environment model.toCarriers)
variable (presented : art.Statement model → PIR.Process I (Domain.Result model.toCarriers))

/-- Exact equality of the adaptive oracle computations, retaining the claimed
statement, actual acceptance projection, all queries and unread proof. -/
theorem adaptive_computation
    (encoded : ∀ statement, Domain.encodeValues statement = some (inputs statement))
    (bridge : ∀ statement, Bridge absorb (ReadPost statement) (initial statement)
      (Domain.participant model compiled.imported.program compiled.selection.context art.participant
        (inputs statement ++ [.transcript compiled.selection.context.suite (initial statement)]))
      (presented statement))
    (prover : OracleComp (OracleSpec.ofFn (Typed.ByLast (@Domain.Raw model.toCarriers)))
      (art.Statement model × Domain.Proof model.toCarriers)) :
    (prover >>= fun claimed => (fun result => (claimed.1, result)) <$>
      compiled.verifier model (Typed.ask (R := Typed.ByLast Domain.Raw)) claimed.1
        (initial claimed.1) claimed.2) =
      (fun result => (result.1,
        (Zkc.Transcript.mapOutcome compiled.acceptance result.2.1, result.2.2))) <$>
        Typed.experiment absorb presented initial prover := by
  simp only [Typed.experiment, map_bind]
  apply congrArg (Bind.bind prover)
  funext claimed
  rw [ZkcSecurity.Endpoint.Domain.Compiled.verifier_readExecution, encoded claimed.1]
  simp only
  rw [(bridge claimed.1).reading.run]
  simp only [Functor.map_map]

variable [DecidableEq (Domain.Event model.toCarriers)]
variable [∀ event, SampleableType (@Domain.Raw model.toCarriers event)]

/-- Adaptive charged soundness of the actual compiled verifier. No statement
is fixed before the adversary's oracle computation. Determination covers the
whole raw statement type, including malformed vectors/counts; root shape is
not an adversary restriction. Validator costs are proved for every statement. -/
theorem adaptive_soundness_charged
    (encoded : ∀ statement, Domain.encodeValues statement = some (inputs statement))
    (bridge : ∀ statement, Bridge absorb (ReadPost statement) (initial statement)
      (Domain.participant model compiled.imported.program compiled.selection.context art.participant
        (inputs statement ++ [.transcript compiled.selection.context.suite (initial statement)]))
      (presented statement))
    (determined : Typed.Determined initial)
    (falseStatement : art.Statement model → Prop)
    {Post : Domain.History model.toCarriers → Domain.Result model.toCarriers → Prop}
    {charge : Domain.History model.toCarriers → Domain.Event model.toCarriers → ENNReal}
    (reduction : Typed.Reduction absorb Post charge)
    (rejects : ∀ reached value, Post reached value → compiled.acceptance value ≠ some true)
    (member : ∀ statement, falseStatement statement →
      reduction.doomed (initial statement) (presented statement))
    (validatorCost : ENNReal)
    (validatorBound : ∀ statement,
      Typed.ChargedCostBound absorb charge (presented statement) (initial statement) validatorCost)
    (prover : OracleComp (OracleSpec.ofFn (Typed.ByLast (@Domain.Raw model.toCarriers)))
      (art.Statement model × Domain.Proof model.toCarriers))
    (proverCost : ENNReal)
    (proverBound : WorstCaseCostBound prover ⟨Typed.keyCharge charge⟩ proverCost) :
    Pr{let result ← (simulateQ randomOracle
      (prover >>= fun claimed => (fun result => (claimed.1, result)) <$>
        compiled.verifier model (Typed.ask (R := Typed.ByLast Domain.Raw)) claimed.1
          (initial claimed.1) claimed.2)).run' ∅}[
      falseStatement result.1 ∧ ZkcSecurity.Endpoint.Domain.CompleteAccepted result.2] ≤
        proverCost + validatorCost := by
  rw [adaptive_computation compiled initial inputs presented encoded bridge]
  simp only [simulateQ_map, StateT.run'_map', prEvent_map]
  apply (prEvent_mono _ _ _ (fun result accepted => ?_)).trans
    (Typed.adaptive_soundness_charged (reduction.toCertificate absorb rejects) presented initial
      determined falseStatement member validatorCost validatorBound prover proverCost proverBound)
  exact ⟨accepted.1,
    (Zkc.Transcript.accepted_mapOutcome compiled.acceptance (· = some true) result.2.1).mp accepted.2.1⟩

end ZkcSecurity.FiatShamir.DomainReduction.Compiled
