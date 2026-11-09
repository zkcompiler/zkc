module

public import Zkc.Protocol.Semantics.System
public import Zkc.Protocol.Internal.Installation

/-! Exact same-interface installation covers complete replies, reached state and event prefixes. -/

public section
open PIR MeasureTheory PFunctor

namespace ProtocolProof
variable {E : Type} {I : Signature} {S T L M : Type}
  [∀ op, MeasurableSpace (I.Reply op)]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace L] [MeasurableSpace M]

/-- Local complete operation laws and coverage of the whole initial measures.

The relation includes accumulated events. Interfaces and reply meanings agree; a different
interface or decoder requires a separate representation theorem.
-/
structure Installation (actual : System E I S L) (model : System E I T M)
    (admissible : E → Prop) (related : E → (S × List L) → (T × List M) → Prop) where
  operations : ∀ environment, admissible environment →
    KernelHandler.CouplingContract (actual.accumulatedOperations environment)
      (model.accumulatedOperations environment) (related environment)
  initial : ∀ environment, admissible environment →
    ExpectationWP.CouplingPost (actual.initialWithEvents environment)
      (model.initialWithEvents environment) (related environment)

namespace Installation

-- These measure laws are independent of the program representation and retain their exact meaning.
theorem coupling_lintegral_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (f : X → ENNReal) (g : Y → ENNReal)
    (hf : Measurable f) (hg : Measurable g)
    (h : ExpectationWP.CouplingPost μ ν (fun x y ↦ f x ≤ g y)) :
    (∫⁻ x, f x ∂μ) ≤ ∫⁻ y, g y ∂ν :=
  Internal.Installation.coupling_lintegral_le f g hf hg h

theorem coupling_lintegral_ge {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (f : X → ENNReal) (g : Y → ENNReal)
    (hf : Measurable f) (hg : Measurable g)
    (h : ExpectationWP.CouplingPost μ ν (fun x y ↦ g y ≤ f x)) :
    (∫⁻ y, g y ∂ν) ≤ ∫⁻ x, f x ∂μ :=
  Internal.Installation.coupling_lintegral_ge f g hf hg h

theorem coupling_event_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (actualEvent : Set X) (modelEvent : Set Y)
    (ha : MeasurableSet actualEvent) (hm : MeasurableSet modelEvent)
    (h : ExpectationWP.CouplingPost μ ν (fun x y ↦ x ∈ actualEvent → y ∈ modelEvent)) :
    μ actualEvent ≤ ν modelEvent :=
  Internal.Installation.coupling_event_le actualEvent modelEvent ha hm h

theorem coupling_event_ge {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (actualEvent : Set X) (modelEvent : Set Y)
    (ha : MeasurableSet actualEvent) (hm : MeasurableSet modelEvent)
    (h : ExpectationWP.CouplingPost μ ν (fun x y ↦ y ∈ modelEvent → x ∈ actualEvent)) :
    ν modelEvent ≤ μ actualEvent :=
  Internal.Installation.coupling_event_ge actualEvent modelEvent ha hm h

variable [∀ op, Countable (I.Reply op)] [∀ op, MeasurableSingletonClass (I.Reply op)]
  {A : Type} [MeasurableSpace A]
  {actual : System E I S L} {model : System E I T M}
  {admissible : E → Prop} {related : E → (S × List L) → (T × List M) → Prop}
  (installation : Installation actual model admissible related)

include installation

/-- Exact local laws and whole initial coverage preserve complete execution mass. -/
theorem mass_eq (client : E → Process I A) (environment : E)
    (henv : admissible environment) :
    (actual.experiment client).run environment Set.univ =
      (model.experiment client).run environment Set.univ := by
  change ((((Internal.backendSystem actual).experiment (fun e ↦ Internal.encode (client e))).run environment).map
    Execution.measurableEquiv.symm) Set.univ =
      ((((Internal.backendSystem model).experiment (fun e ↦ Internal.encode (client e))).run environment).map
        Execution.measurableEquiv.symm) Set.univ
  rw [Measure.map_apply Execution.measurableEquiv.symm.measurable MeasurableSet.univ,
    Measure.map_apply Execution.measurableEquiv.symm.measurable MeasurableSet.univ]
  exact Internal.Installation.mass_eq (installation.operations environment henv)
    (installation.initial environment henv) (Internal.encode (client environment))

/-- Compare complete observations of the same Process client in every admissible context.
The terminal obligation retains the full Outcome and both reached state/event pairs. -/
theorem lintegral_le (client : E → Process I A) (environment : E)
    (henv : admissible environment)
    (actualObservation : Execution S L A → ENNReal)
    (modelObservation : Execution T M A → ENNReal)
    (ha : Measurable actualObservation) (hm : Measurable modelObservation)
    (hterminal : ∀ (outcome : Outcome A) actualState modelState,
      related environment actualState modelState →
        actualObservation ⟨outcome, actualState.1, actualState.2⟩ ≤
          modelObservation ⟨outcome, modelState.1, modelState.2⟩) :
    (∫⁻ out, actualObservation out ∂(actual.experiment client).run environment) ≤
      ∫⁻ out, modelObservation out ∂(model.experiment client).run environment := by
  change (∫⁻ out, actualObservation out ∂
    ((((Internal.backendSystem actual).experiment (fun e ↦ Internal.encode (client e))).run environment).map
      Execution.measurableEquiv.symm)) ≤
    ∫⁻ out, modelObservation out ∂
      ((((Internal.backendSystem model).experiment (fun e ↦ Internal.encode (client e))).run environment).map
        Execution.measurableEquiv.symm)
  rw [lintegral_map ha Execution.measurableEquiv.symm.measurable,
    lintegral_map hm Execution.measurableEquiv.symm.measurable]
  exact Internal.Installation.lintegral_le (installation.operations environment henv)
    (installation.initial environment henv) (Internal.encode (client environment))
    (actualObservation ∘ Execution.measurableEquiv.symm)
    (modelObservation ∘ Execution.measurableEquiv.symm)
    (ha.comp Execution.measurableEquiv.symm.measurable)
    (hm.comp Execution.measurableEquiv.symm.measurable) hterminal

/-- Reverse the terminal comparison to transport an unconditional lower expectation. -/
theorem lintegral_ge (client : E → Process I A) (environment : E)
    (henv : admissible environment)
    (actualObservation : Execution S L A → ENNReal)
    (modelObservation : Execution T M A → ENNReal)
    (ha : Measurable actualObservation) (hm : Measurable modelObservation)
    (hterminal : ∀ (outcome : Outcome A) actualState modelState,
      related environment actualState modelState →
        modelObservation ⟨outcome, modelState.1, modelState.2⟩ ≤
          actualObservation ⟨outcome, actualState.1, actualState.2⟩) :
    (∫⁻ out, modelObservation out ∂(model.experiment client).run environment) ≤
      ∫⁻ out, actualObservation out ∂(actual.experiment client).run environment := by
  change (∫⁻ out, modelObservation out ∂
    ((((Internal.backendSystem model).experiment (fun e ↦ Internal.encode (client e))).run environment).map
      Execution.measurableEquiv.symm)) ≤
    ∫⁻ out, actualObservation out ∂
      ((((Internal.backendSystem actual).experiment (fun e ↦ Internal.encode (client e))).run environment).map
        Execution.measurableEquiv.symm)
  rw [lintegral_map hm Execution.measurableEquiv.symm.measurable,
    lintegral_map ha Execution.measurableEquiv.symm.measurable]
  exact Internal.Installation.lintegral_ge (installation.operations environment henv)
    (installation.initial environment henv) (Internal.encode (client environment))
    (actualObservation ∘ Execution.measurableEquiv.symm)
    (modelObservation ∘ Execution.measurableEquiv.symm)
    (ha.comp Execution.measurableEquiv.symm.measurable)
    (hm.comp Execution.measurableEquiv.symm.measurable) hterminal

/-- An actual-to-model terminal implication bounds the fixed complete execution event. -/
theorem event_le (client : E → Process I A) (environment : E)
    (henv : admissible environment)
    (actualEvent : Set (Execution S L A)) (modelEvent : Set (Execution T M A))
    (ha : MeasurableSet actualEvent) (hm : MeasurableSet modelEvent)
    (hterminal : ∀ (outcome : Outcome A) actualState modelState,
      related environment actualState modelState →
        (⟨outcome, actualState.1, actualState.2⟩ : Execution S L A) ∈ actualEvent →
          (⟨outcome, modelState.1, modelState.2⟩ : Execution T M A) ∈ modelEvent) :
    (actual.experiment client).run environment actualEvent ≤
      (model.experiment client).run environment modelEvent := by
  change ((((Internal.backendSystem actual).experiment (fun e ↦ Internal.encode (client e))).run environment).map
    Execution.measurableEquiv.symm) actualEvent ≤
      ((((Internal.backendSystem model).experiment (fun e ↦ Internal.encode (client e))).run environment).map
        Execution.measurableEquiv.symm) modelEvent
  rw [Measure.map_apply Execution.measurableEquiv.symm.measurable ha,
    Measure.map_apply Execution.measurableEquiv.symm.measurable hm]
  exact Internal.Installation.event_le (installation.operations environment henv)
    (installation.initial environment henv) (Internal.encode (client environment))
    (Execution.measurableEquiv.symm ⁻¹' actualEvent)
    (Execution.measurableEquiv.symm ⁻¹' modelEvent)
    (ha.preimage Execution.measurableEquiv.symm.measurable)
    (hm.preimage Execution.measurableEquiv.symm.measurable) hterminal

/-- The reverse implication bounds the actual event below, including all stopped outcomes. -/
theorem event_ge (client : E → Process I A) (environment : E)
    (henv : admissible environment)
    (actualEvent : Set (Execution S L A)) (modelEvent : Set (Execution T M A))
    (ha : MeasurableSet actualEvent) (hm : MeasurableSet modelEvent)
    (hterminal : ∀ (outcome : Outcome A) actualState modelState,
      related environment actualState modelState →
        (⟨outcome, modelState.1, modelState.2⟩ : Execution T M A) ∈ modelEvent →
          (⟨outcome, actualState.1, actualState.2⟩ : Execution S L A) ∈ actualEvent) :
    (model.experiment client).run environment modelEvent ≤
      (actual.experiment client).run environment actualEvent := by
  change ((((Internal.backendSystem model).experiment (fun e ↦ Internal.encode (client e))).run environment).map
    Execution.measurableEquiv.symm) modelEvent ≤
      ((((Internal.backendSystem actual).experiment (fun e ↦ Internal.encode (client e))).run environment).map
        Execution.measurableEquiv.symm) actualEvent
  rw [Measure.map_apply Execution.measurableEquiv.symm.measurable hm,
    Measure.map_apply Execution.measurableEquiv.symm.measurable ha]
  exact Internal.Installation.event_ge (installation.operations environment henv)
    (installation.initial environment henv) (Internal.encode (client environment))
    (Execution.measurableEquiv.symm ⁻¹' actualEvent)
    (Execution.measurableEquiv.symm ⁻¹' modelEvent)
    (ha.preimage Execution.measurableEquiv.symm.measurable)
    (hm.preimage Execution.measurableEquiv.symm.measurable) hterminal

/-- Close an upper expectation bound on the fixed experiment from its model bound. -/
theorem upper_bound (client : E → Process I A) (environment : E)
    (henv : admissible environment)
    (actualObservation : Execution S L A → ENNReal)
    (modelObservation : Execution T M A → ENNReal)
    (ha : Measurable actualObservation) (hm : Measurable modelObservation)
    (hterminal : ∀ (outcome : Outcome A) actualState modelState,
      related environment actualState modelState →
        actualObservation ⟨outcome, actualState.1, actualState.2⟩ ≤
          modelObservation ⟨outcome, modelState.1, modelState.2⟩)
    {bound : ENNReal}
    (hmodel : (∫⁻ out, modelObservation out ∂(model.experiment client).run environment) ≤
      bound) :
    (∫⁻ out, actualObservation out ∂(actual.experiment client).run environment) ≤ bound :=
  (installation.lintegral_le client environment henv actualObservation modelObservation
    ha hm hterminal).trans hmodel

/-- Close a lower expectation bound without conditioning away stopped executions. -/
theorem lower_bound (client : E → Process I A) (environment : E)
    (henv : admissible environment)
    (actualObservation : Execution S L A → ENNReal)
    (modelObservation : Execution T M A → ENNReal)
    (ha : Measurable actualObservation) (hm : Measurable modelObservation)
    (hterminal : ∀ (outcome : Outcome A) actualState modelState,
      related environment actualState modelState →
        modelObservation ⟨outcome, modelState.1, modelState.2⟩ ≤
          actualObservation ⟨outcome, actualState.1, actualState.2⟩)
    {bound : ENNReal}
    (hmodel : bound ≤ ∫⁻ out, modelObservation out ∂(model.experiment client).run environment) :
    bound ≤ ∫⁻ out, actualObservation out ∂(actual.experiment client).run environment :=
  hmodel.trans (installation.lintegral_ge client environment henv actualObservation
    modelObservation ha hm hterminal)

/-- Close a complete-event upper bound using the same admissible context and fixed client. -/
theorem event_upper_bound (client : E → Process I A) (environment : E)
    (henv : admissible environment)
    (actualEvent : Set (Execution S L A)) (modelEvent : Set (Execution T M A))
    (ha : MeasurableSet actualEvent) (hm : MeasurableSet modelEvent)
    (hterminal : ∀ (outcome : Outcome A) actualState modelState,
      related environment actualState modelState →
        (⟨outcome, actualState.1, actualState.2⟩ : Execution S L A) ∈ actualEvent →
          (⟨outcome, modelState.1, modelState.2⟩ : Execution T M A) ∈ modelEvent)
    {bound : ENNReal}
    (hmodel : (model.experiment client).run environment modelEvent ≤ bound) :
    (actual.experiment client).run environment actualEvent ≤ bound :=
  (installation.event_le client environment henv actualEvent modelEvent ha hm hterminal).trans
    hmodel

/-- Close an unconditional complete-event lower bound with the reverse terminal implication. -/
theorem event_lower_bound (client : E → Process I A) (environment : E)
    (henv : admissible environment)
    (actualEvent : Set (Execution S L A)) (modelEvent : Set (Execution T M A))
    (ha : MeasurableSet actualEvent) (hm : MeasurableSet modelEvent)
    (hterminal : ∀ (outcome : Outcome A) actualState modelState,
      related environment actualState modelState →
        (⟨outcome, modelState.1, modelState.2⟩ : Execution T M A) ∈ modelEvent →
          (⟨outcome, actualState.1, actualState.2⟩ : Execution S L A) ∈ actualEvent)
    {bound : ENNReal}
    (hmodel : bound ≤ (model.experiment client).run environment modelEvent) :
    bound ≤ (actual.experiment client).run environment actualEvent :=
  hmodel.trans (installation.event_ge client environment henv actualEvent modelEvent ha hm
    hterminal)

end Installation
end ProtocolProof
