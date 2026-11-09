module

public import ProtocolProof.Claims.Quantitative
public import ProtocolProof.Claims.Problem
public import ProtocolProof.Semantics.Access

/-!
# Fixed extraction guarantees

This profile concerns a statement fixed by public input. Acceptance and extraction use the
same environment. The request fixes the algorithm, access interface, handler, witness relation,
success function and weighted-call budget. This is not by itself a polynomial-time proof of
knowledge. In particular, pure computation has no runtime interpretation in this profile.
-/

public section

open MeasureTheory PFunctor
open scoped ENNReal

namespace ProtocolProof

/-- A fixed acceptance-to-extraction function, positive above its explicit knowledge threshold. -/
structure ExtractionGuarantee where
  threshold : ℝ≥0∞
  lower : ℝ≥0∞ → ℝ≥0∞
  monotone : Monotone lower
  probability_bound : ∀ p, p ≤ 1 → lower p ≤ 1
  positive : ∀ p, p ≤ 1 → threshold < p → 0 < lower p

/-- Extraction succeeds with at least the verifier's acceptance probability. -/
@[expose] def ExtractionGuarantee.direct : ExtractionGuarantee where
  threshold := 0
  lower := id
  monotone := monotone_id
  probability_bound _ h := h
  positive _ _ h := h

/-- Whether the guarantee has a nonempty probability range above its threshold. -/
@[expose] def ExtractionGuarantee.Informative (guarantee : ExtractionGuarantee) : Prop :=
  guarantee.threshold < 1

universe uP uE uA uB uS uW uX

variable (Public : Type uP) (Environment : Type uE) (Interface : PFunctor.{uA, uB})
  (State : Type uS) (Witness : Type uW) (Statement : Type uX)
  [∀ op, MeasurableSpace (Interface.B op)] [∀ op, Countable (Interface.B op)]
  [∀ op, MeasurableSingletonClass (Interface.B op)]
  [MeasurableSpace State] [MeasurableSpace (Option Witness)]

/-- A request-fixed extraction experiment and its mathematical success criterion. -/
structure ExtractionRequest where
  acceptance : Experiment Environment Bool
  admissible : Environment → Prop
  execution : AccessExecution Public Environment Interface State (Option Witness)
  statement : Public → Statement
  problem : PromiseProblem Statement
  witnesses : WitnessRelation problem Witness
  measurable_success : ∀ environment, MeasurableSet
    {out : Option Witness × State | ∃ witness, out.1 = some witness ∧
      witnesses.relates (statement (execution.publicInput environment)) witness}
  guarantee : Public → ExtractionGuarantee
  cost : OperationCost Interface
  budget : Public → ℝ≥0∞

variable {Public Environment Interface State Witness Statement}

namespace ExtractionRequest

variable (request : ExtractionRequest Public Environment Interface State Witness Statement)

/-- A per-environment lower-bound goal uses the actual extractor's complete execution law. -/
@[expose] noncomputable def successRequest (environment : Environment) :
    LowerRequest Unit (Option Witness × State) where
  experiment := request.execution.experiment.reindex (fun _ ↦ environment)
  admissible _ := True
  event := {out | ∃ witness, out.1 = some witness ∧
    request.witnesses.relates
      (request.statement (request.execution.publicInput environment)) witness}
  measurable_event := request.measurable_success environment
  bound _ := (request.guarantee (request.execution.publicInput environment)).lower
    (request.acceptance.run environment {true})

/-- Weighted abstract calls are bounded for all admitted environments and all possible answers. -/
@[expose] def CallsBounded : Prop := ∀ environment, request.admissible environment →
  request.cost.bound (request.execution.algorithm (request.execution.publicInput environment)) ≤
    request.budget (request.execution.publicInput environment)

/-- Extraction success and its selected resource guarantee are separate conjuncts. -/
@[expose] def Holds : Prop :=
  (∀ environment, request.admissible environment → (request.successRequest environment).Holds) ∧
    request.CallsBounded

/-- Any method proving the fixed lower requests can close the extraction claim. -/
theorem establish
    (success : ∀ environment, request.admissible environment →
      (request.successRequest environment).Holds)
    (resources : request.CallsBounded) : request.Holds := ⟨success, resources⟩

/-- Acceptance above the fixed threshold entails genuinely positive extraction success. -/
theorem positive_success (proof : request.Holds) (environment : Environment)
    (admitted : request.admissible environment)
    (above : (request.guarantee (request.execution.publicInput environment)).threshold <
      request.acceptance.run environment {true}) :
    0 < (request.successRequest environment).experiment.run ()
      (request.successRequest environment).event := by
  have := request.acceptance.normalized environment
  exact ((request.guarantee (request.execution.publicInput environment)).positive _
    prob_le_one above).trans_le (proof.1 environment admitted () trivial)

end ExtractionRequest

end ProtocolProof
