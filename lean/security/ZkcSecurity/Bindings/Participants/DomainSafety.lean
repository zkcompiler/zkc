module

public import Zkc.Construction.DomainTranscript
public import Zkc.Semantics.Yields
public import ZkcSecurity.ProgramLogic.Transcript.Reduction

@[expose] public section

/-! Zero-error reductions from all-reply safety. This is an adapter into the
existing dependent-reply reduction engine, not another probabilistic semantics.
The caller still owes membership for the actual bound compiled verifier. -/
set_option autoImplicit false

namespace ZkcSecurity.Endpoint.Domain
open Zkc.Transcript ZkcSecurity.FiatShamir.Typed OracleComp OracleSpec

variable {I : PIR.Signature} {E P A : Type} {Raw : E → Type}
  [∀ event, SampleableType (Raw event)]

/-- All-reply safety is a sufficient (stronger than probabilistic) zero-charge
invariant. In particular, received values are never restricted to honest ones. -/
def safetyReduction (absorb : Interface I E P Raw) (post : A → Prop) :
    Reduction absorb (fun _ value => post value) (fun _ _ => 0) where
  doomed _ process := PIR.Yields post process
  step history process safe := by
    cases process with
    | done => exact safe
    | halt => trivial
    | call operation next =>
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · simp only [ChargedStepTo, absorbed]
        exact fun _ value _ => safe value
      · simp only [ChargedStepTo, absorbed]
        exact safe value
      · simp only [ChargedStepTo, absorbed]
        exact (prEvent_eq_zero_of_forall_not _ _ (by
          rintro raw ⟨value, _, escaped⟩
          exact escaped (safe value))).le
      · simp only [ChargedStepTo, absorbed]

def safetyCertificate (absorb : Interface I E P Raw) (accepts : A → Prop) :
    ChargedCertificate absorb accepts (fun _ _ => 0) :=
  (safetyReduction absorb (fun value => ¬ accepts value)).toCertificate absorb
    (fun _ _ rejected => rejected)

omit [∀ event, SampleableType (Raw event)] in
theorem zero_validator_cost (absorb : Interface I E P Raw) (process : PIR.Process I A)
    (history : List E) : ChargedCostBound absorb (fun _ _ => 0) process history 0 := by
  induction process generalizing history with
  | done => trivial
  | halt => trivial
  | call operation next ih =>
    rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
      ⟨event, decode⟩ | _ <;> simp only [ChargedCostBound, absorbed]
    · exact fun _ value _ => ih value _
    · exact ih value _
    · exact ⟨0, by simp, fun value => ih value _⟩

/-- Zero local charge requires no uniform bound on the number of adversarial
queries. Every terminating OracleComp has zero cost under the zero model. -/
theorem zero_prover_cost {ι : Type} {spec : OracleSpec ι} (prover : OracleComp spec A) :
    WorstCaseCostBound prover (⟨fun _ => (0 : ENNReal)⟩) 0 := by
  induction prover using OracleComp.inductionOn with
  | pure value => simp
  | query_bind key next ih =>
    rw [worstCaseCostBound_query_bind_iff]
    intro reply result supported
    simpa using (worstCaseCostBound_iff_support_bound _ _ _).mp (ih reply) result supported

end ZkcSecurity.Endpoint.Domain
