module

public import ZkcSecurity.Realizations.Gkr.OriginalValidatorBody
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

def validatorInputABI (handle : Nat) : Original.InputABI :=
  ⟨Generated.Validator.inputSorts,
    [.data 0, .data 1, .data 2, .data 3, .data 4, .data 5, .data 6, .capability handle]⟩

def ValidatorReturns (inputs : Domain.Environment (uniformCarriers F G))
    (source : SourceResult (F := F) (G := G)) (actual : Domain.Result (uniformCarriers F G)) : Prop :=
  ValidatorFrameReturns inputs source actual.environment ∧
    ∃ value, source.1 = .cons (some value) .nil ∧
      actual.values = [.data (.boolean value), .transcript context.suite source.2.history]

/-- Full validator root for every raw typed statement, with no shape, output,
acceptance or helper-success premise. -/
def validator (handle : Nat) (initial outputs add mul : List F) (layers selector width : Nat)
    (history : Domain.History (uniformCarriers F G)) :
    Original.Simulation
      (ValidatorReturns (validatorInputs initial outputs add mul layers selector width history))
      (Original.InputLive (validatorInputABI handle)
        (GkrSourceAdmission.inputs (G := G) initial outputs add mul layers selector width handle)
        (validatorInputs initial outputs add mul layers selector width history))
      (Original.fold (routing handle .validator)
        (Occurrence.participant (ringModel F G) GkrSourceViews.program 1
          (GkrSourceAdmission.inputs (G := G) initial outputs add mul layers selector width handle)) ⟨[], history⟩)
      (Domain.participant (ringModel F G) GkrSourceViews.program context CanonicalPair.Validator.participant
        (validatorInputs initial outputs add mul layers selector width history)) := by
  rw [Generated.Validator.participant_eq]
  have sorts : Domain.sortsMatch Generated.Validator.inputSorts
      (validatorInputs (G := G) initial outputs add mul layers selector width history) = true := rfl
  have raw : Original.Simulation
      (ValidatorReturns (validatorInputs initial outputs add mul layers selector width history))
      (fun _ frame => ArtifactBinding.Captures (validatorInputs initial outputs add mul layers selector width history) frame)
      (Original.fold (routing handle .validator)
        (Occurrence.participant (ringModel F G) GkrSourceViews.program 1
          (GkrSourceAdmission.inputs (G := G) initial outputs add mul layers selector width handle)) ⟨[], history⟩)
      (Generated.Validator.view (ringModel F G) GkrSourceViews.program context
        (validatorInputs initial outputs add mul layers selector width history)) := by
    unfold Generated.Validator.view Domain.View.participant
    refine .checkpoint _ (by simp [ArtifactBinding.Captures]) ?_
    simp only [sorts, ↓reduceIte]
    have assembled := (validatorBody handle initial outputs add mul layers selector width history).bind
      (returnRelation := ValidatorReturns (validatorInputs initial outputs add mul layers selector width history))
      (nextLive := fun _ frame => ArtifactBinding.Captures (validatorInputs initial outputs add mul layers selector width history) frame)
      (sourceNext := fun result => .done result)
      (targetNext := fun frame =>
        match Domain.read frame Generated.Validator.returned with
        | some values => if Domain.sortsMatch Generated.Validator.outputSorts values then
            .done ⟨values, frame⟩ else .halt .refused
        | none => .halt .refused)
      (fun _ _ retained => retained) (by
        intro original final related
        apply Classical.choice
        obtain ⟨captured, point, claim, history, value, rfl, size, retained, rfl⟩ := related
        refine ⟨?_⟩
        simp (disch := omega) only [Generated.Validator.returned, Domain.read, List.mapM_cons,
          List.mapM_nil, List.getElem?_append_right, size, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Bind.bind, Option.bind, Option.pure_def]
        exact .done ⟨⟨captured, point, claim, history, value, rfl, size, retained, rfl⟩,
          value, rfl, rfl⟩)
    simp only [PIR.Process.bind_done] at assembled
    convert assembled using 1
    congr 1
    funext frame
    cases Domain.read frame Generated.Validator.returned <;> rfl
  apply raw.mapRelations (fun _ _ related => related)
  intro process frame retained
  apply Original.inputLive_of_captures (validatorInputABI handle) _ _ frame process sorts _ _ retained
  · intro reference present
    simp [validatorInputABI] at present
    simp only [validatorInputs, List.length_cons, List.length_nil]
    omega
  · simp [validatorInputABI, GkrSourceAdmission.inputs, validatorInputs,
      Original.ValuesHolds, Original.ComponentHolds, Domain.Value.decode, Domain.Payload.value, scalarDomain]

/-- Arbitrary proof buffers include missing packets and unread suffixes. The
same validator certificate is used for every raw statement and every reply. -/
theorem validator_run (handle : Nat) (initial outputs add mul : List F)
    (layers selector width : Nat) (history : Domain.History (uniformCarriers F G))
    {m : Type → Type} [Monad m] [LawfulMonad m] {S : Type}
    (oracle : Domain.Oracle m (uniformCarriers F G) S)
    (services : Domain.LocalServices m (uniformCarriers F G) S)
    (state : Domain.RuntimeState (uniformCarriers F G) S) :
    Domain.run .validator oracle
      (Domain.participant (ringModel F G) GkrSourceViews.program context CanonicalPair.Validator.participant
        (validatorInputs initial outputs add mul layers selector width history)) state services =
      (do let execution ← Domain.run .validator oracle
            (validator handle initial outputs add mul layers selector width history).paired state services
          pure (Original.mapExecution Prod.snd execution)) :=
  (validator handle initial outputs add mul layers selector width history).runM
    (Domain.handler .validator oracle services) state



end ZkcSecurity.Realizations.Gkr.OriginalCertificates
