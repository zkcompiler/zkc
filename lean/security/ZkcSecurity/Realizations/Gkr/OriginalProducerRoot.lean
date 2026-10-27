module

public import ZkcSecurity.Realizations.Gkr.OriginalProducerBody
public import ZkcSecurity.Realizations.Gkr.OriginalRootRegions
public import ZkcExamples.Structured.GkrProverContinuation
public import Zkc.Construction.OriginalFrameRelations
public import Zkc.Construction.OriginalExecution
public meta import Zkc.Construction.OriginalComponentReduction

@[expose] public section
/-! Complete nominal certificates for the actual authored GKR pair. Each root
uses the same all-reply occurrence process and the complete constructed view. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.OriginalCertificates
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured GkrSourceCallbacks
open ZkcExamples.Construction GkrSourceRouting HonestProducerSource
attribute [local irreducible] outputBody layerBody
attribute [local irreducible] Generated.Producer.body Generated.Validator.body
attribute [local irreducible] Original.fold invoke invokeProtocol denoteRepeatOn
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def producerInputABI : Original.InputABI :=
  ⟨Generated.Producer.inputSorts,
    [.data 0, .absent, .data 1, .data 2, .data 3, .data 4, .data 5, .absent]⟩

def ProducerReturns (inputs : Domain.Environment (uniformCarriers F G))
    (source : SourceResult (F := F) (G := G)) (actual : Domain.Result (uniformCarriers F G)) : Prop :=
  ProducerFrameReturns inputs source actual.environment ∧
    actual.values = [.transcript context.suite source.2.history]

theorem producer_source_inputs (initial outputs add mul : List F) (layers selector width handle : Nat) :
    Occurrence.participant (ringModel F G) GkrSourceViews.program 0
      (GkrSourceAdmission.inputs (G := G) initial outputs add mul layers selector width handle) =
    Occurrence.participant (ringModel F G) GkrSourceViews.program 0
      (GkrProverContinuation.inputs (G := G) initial add mul layers selector width) := by
  rw [OriginalRootRegions.root_body, OriginalRootRegions.root_body]
  rfl

/-- Full producer root. Supplied outputs are discarded by the actual source
role mask, without assuming the circuit's result or any helper success. -/
def producer (handle : Nat) (initial outputs add mul : List F) (layers selector width : Nat)
    (history : Domain.History (uniformCarriers F G)) :
    Original.Simulation
      (ProducerReturns (producerInputs initial add mul layers selector width history))
      (Original.InputLive producerInputABI
        (GkrProverContinuation.inputs (G := G) initial add mul layers selector width)
        (producerInputs initial add mul layers selector width history))
      (Original.fold (routing handle .producer)
        (Occurrence.participant (ringModel F G) GkrSourceViews.program 0
          (GkrSourceAdmission.inputs (G := G) initial outputs add mul layers selector width handle)) ⟨[], history⟩)
      (Domain.participant (ringModel F G) GkrSourceViews.program context CanonicalPair.Producer.participant
        (producerInputs initial add mul layers selector width history)) := by
  rw [producer_source_inputs, Generated.Producer.participant_eq]
  have sorts : Domain.sortsMatch Generated.Producer.inputSorts
      (producerInputs (G := G) initial add mul layers selector width history) = true := rfl
  have raw : Original.Simulation
      (ProducerReturns (producerInputs initial add mul layers selector width history))
      (fun _ frame => ArtifactBinding.Captures (producerInputs initial add mul layers selector width history) frame)
      (Original.fold (routing handle .producer)
        (Occurrence.participant (ringModel F G) GkrSourceViews.program 0
          (GkrProverContinuation.inputs (G := G) initial add mul layers selector width)) ⟨[], history⟩)
      (Generated.Producer.view (ringModel F G) GkrSourceViews.program context
        (producerInputs initial add mul layers selector width history)) := by
    unfold Generated.Producer.view Domain.View.participant
    refine .checkpoint _ (by simp [ArtifactBinding.Captures]) ?_
    simp only [sorts, ↓reduceIte]
    have assembled := (producerBody handle initial add mul layers selector width history).bind
      (returnRelation := ProducerReturns (producerInputs initial add mul layers selector width history))
      (nextLive := fun _ frame => ArtifactBinding.Captures (producerInputs initial add mul layers selector width history) frame)
      (sourceNext := fun result => .done result)
      (targetNext := fun frame =>
        match Domain.read frame Generated.Producer.returned with
        | some values => if Domain.sortsMatch Generated.Producer.outputSorts values then
            .done ⟨values, frame⟩ else .halt .refused
        | none => .halt .refused)
      (fun _ _ retained => retained) (by
        intro original final related
        apply Classical.choice
        obtain ⟨empty, outputPoint, outputHistory, point, history, rfl, rfl⟩ := related
        refine ⟨?_⟩
        simp only [Generated.Producer.returned, Domain.read, producerInputs, List.cons_append,
          List.nil_append, List.mapM_cons, List.mapM_nil, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Bind.bind, Option.bind, Option.pure_def]
        exact .done ⟨⟨empty, outputPoint, outputHistory, point, history, rfl, rfl⟩, rfl⟩)
    simp only [PIR.Process.bind_done] at assembled
    convert assembled using 1
    congr 1
    funext frame
    cases Domain.read frame Generated.Producer.returned <;> rfl
  apply raw.mapRelations (fun _ _ related => related)
  intro process frame retained
  apply Original.inputLive_of_captures producerInputABI _ _ frame process sorts _ _ retained
  · intro reference present
    simp [producerInputABI] at present
    simp only [producerInputs, List.length_cons, List.length_nil]
    omega
  · simp [producerInputABI, GkrProverContinuation.inputs, producerInputs,
      Original.ValuesHolds, Original.ComponentHolds, Domain.Value.decode, Domain.Payload.value, scalarDomain]

/-- Execution uses the existing full nominal handler. The target projection
retains every physical frame, event, proof buffer and shared provider state. -/
theorem producer_run (handle : Nat) (initial outputs add mul : List F)
    (layers selector width : Nat) (history : Domain.History (uniformCarriers F G))
    {m : Type → Type} [Monad m] [LawfulMonad m] {S : Type}
    (oracle : Domain.Oracle m (uniformCarriers F G) S)
    (services : Domain.LocalServices m (uniformCarriers F G) S)
    (state : Domain.RuntimeState (uniformCarriers F G) S) :
    Domain.run .producer oracle
      (Domain.participant (ringModel F G) GkrSourceViews.program context CanonicalPair.Producer.participant
        (producerInputs initial add mul layers selector width history)) state services =
      (do let execution ← Domain.run .producer oracle
            (producer handle initial outputs add mul layers selector width history).paired state services
          pure (Original.mapExecution Prod.snd execution)) :=
  (producer handle initial outputs add mul layers selector width history).runM
    (Domain.handler .producer oracle services) state


end ZkcSecurity.Realizations.Gkr.OriginalCertificates
