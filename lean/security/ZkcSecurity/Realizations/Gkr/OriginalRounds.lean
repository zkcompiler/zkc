module

public import ZkcExamples.Construction.GkrOriginalRounds
public import ZkcSecurity.Realizations.Gkr.Generated.Producer
public import ZkcSecurity.Realizations.Gkr.Generated.Validator
public import ZkcSecurity.Realizations.Gkr.HonestProducerSource

@[expose] public section
/-! The two qualified s9 callbacks and repeats of the actual exported pair.
The shared core template retains every optional source coordinate and stop. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.OriginalRounds
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured GkrRoundsNormalForms
open ZkcExamples.Construction GkrSourceRouting GkrOriginalRounds
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def validatorOffset : Side → Nat | .left => 50 | .right => 57
def validatorInitial : Side → List Nat | .left => [48, 49, 43] | .right => [55, 56, 52]
def validatorCompiled : Side → Domain.View.Block (uniformCarriers F G)
  | .left => Generated.Validator.bodyStep37BodyStep3Body (ringModel F G) GkrSourceViews.program context
  | .right => Generated.Validator.bodyStep37BodyStep6Body (ringModel F G) GkrSourceViews.program context
def validatorLoop : Side → Domain.View.Block (uniformCarriers F G)
  | .left => Generated.Validator.bodyStep37BodyStep3 (ringModel F G) GkrSourceViews.program context
  | .right => Generated.Validator.bodyStep37BodyStep6 (ringModel F G) GkrSourceViews.program context

theorem validator_body (side : Side) :
    validatorCompiled (F := F) (G := G) side =
      validatorBody (ringModel F G) side (validatorOffset side) 40 := by
  cases side <;> kernel_rfl

theorem validator_loop (side : Side) :
    validatorLoop (F := F) (G := G) side = Domain.View.loop 4
      [(validatorOffset side) + 32, (validatorOffset side) + 36, (validatorOffset side) + 31] 6 (validatorInitial side)
      [.data (.vector scalarDomain), .data (.field scalarDomain), .transcript context.suite]
      (validatorBody (ringModel F G) side (validatorOffset side) 40) := by
  cases side <;> kernel_rfl

def validator (side : Side) (handle layer index : Nat)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = validatorOffset side)
    (layerRead : captured[40]? = some (.data (.index layer)))
    (point : List F) (claim : F) (history : Domain.History (uniformCarriers F G))
    (routes : Routes .validator side handle layer index) :
    Original.Simulation
      (Original.IterationReturns (ValidatorReturns layer) (GkrOriginalCoefficient.outer layer)
        (qualifyProtocolSite (roundContext side).applicationPrefix "s9") index
        [(validatorOffset side) + 32, (validatorOffset side) + 36, (validatorOffset side) + 31] [.data (.vector scalarDomain), .data (.field scalarDomain), .transcript context.suite])
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (Original.fold (routing handle .validator)
        (roundBody.denote
          (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
            HonestProducerSource.observedHelpers 1 [] (roundContext side) Occurrence.iterations)
          ((.cons (some index) ((verifierState (some point) (some claim)).append (.cons (some handle) .nil))) :
            Values (Component (assignment F G)) (.index :: (roundState ++ roundCaptures))).get)
        ⟨roundFrames side layer index, history⟩)
      (validatorCompiled side (captured ++ .data (.index index) :: validatorCarried point claim history)) := by
  rw [HonestProducerSource.round_callback, validator_body]
  exact validatorCallback side handle (validatorOffset side) 40 layer index captured size layerRead
    point claim history routes

def validatorRepeat (side : Side) (handle layer : Nat)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = validatorOffset side)
    (layerRead : captured[40]? = some (.data (.index layer)))
    (point : List F) (claim : F) (history : Domain.History (uniformCarriers F G)) (count : Nat)
    (countRead : captured[6]? = some (.data (.index count)))
    (initialRead : Domain.read captured (validatorInitial side) = some (validatorCarried point claim history))
    (routes : ∀ index, Routes .validator side handle layer index) :
    Original.Simulation
      (fun original final => ∃ next, ValidatorReturns layer original next ∧ final = captured ++ next)
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (Original.fold (routing handle .validator)
        (denoteRepeatOn roundSpec (roundContext side) 1 (some count) (verifierState (some point) (some claim))
          (.cons (some handle) .nil)
          (fun args => roundBody.denote
            (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
              HonestProducerSource.observedHelpers 1 [] (roundContext side) Occurrence.iterations) args.get)
          Occurrence.iterations "s9") ⟨GkrOriginalCoefficient.outer layer, history⟩)
      (validatorLoop side captured) := by
  rw [validator_loop]
  apply Original.Simulation.occurrenceRepeat (routing handle .validator) roundSpec (roundContext side) 1
    (captures := .cons (some handle) .nil)
    (sourceBody := fun args => roundBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
        HonestProducerSource.observedHelpers 1 [] (roundContext side) Occurrence.iterations) args.get)
    (site := "s9") (relation := ValidatorReturns layer)
  · cases side <;> rfl
  · intro original frame related
    obtain ⟨point, claim, history, rfl, rfl⟩ := related
    cases side <;> exact ⟨point, claim, history, rfl, rfl⟩
  · intro value state frame index related
    apply Classical.choice
    obtain ⟨point, claim, history, pair, rfl⟩ := related
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj pair
    refine ⟨?_⟩
    rw [HonestProducerSource.round_callback]
    rw [verifierState_masked (roundContext side) 1 (by cases side <;> rfl)]
    exact validatorCallback side handle (validatorOffset side) 40 layer index captured size layerRead
      point claim history (routes index)
  · intro original frame related
    obtain ⟨point, claim, history, rfl, rfl⟩ := related
    rfl
  · exact countRead
  · exact initialRead
  · rfl
  · cases side <;> exact ⟨point, claim, history, rfl, rfl⟩

def producerOffset : Side → Nat | .left => 21 | .right => 28
def producerInitial : Side → List Nat | .left => [16, 17, 18, 19, 20, 12] | .right => [21, 22, 23, 24, 27, 26]
def producerCompiled : Side → Domain.View.Block (uniformCarriers F G)
  | .left => Generated.Producer.bodyStep2BodyStep5Body (ringModel F G) GkrSourceViews.program context
  | .right => Generated.Producer.bodyStep2BodyStep7Body (ringModel F G) GkrSourceViews.program context
def producerLoop : Side → Domain.View.Block (uniformCarriers F G)
  | .left => Generated.Producer.bodyStep2BodyStep5 (ringModel F G) GkrSourceViews.program context
  | .right => Generated.Producer.bodyStep2BodyStep7 (ringModel F G) GkrSourceViews.program context

theorem producer_body (side : Side) :
    producerCompiled (F := F) (G := G) side =
      producerBody (ringModel F G) side (producerOffset side) 10 := by
  cases side <;> kernel_rfl

theorem producer_loop (side : Side) :
    producerLoop (F := F) (G := G) side = Domain.View.loop 4
      [(producerOffset side) + 31, (producerOffset side) + 32, (producerOffset side) + 33, (producerOffset side) + 34, (producerOffset side) + 35, (producerOffset side) + 30] 5 (producerInitial side)
      [.data (.vector scalarDomain), .data (.vector scalarDomain), .data (.vector scalarDomain), .data (.vector scalarDomain), .data (.vector scalarDomain), .transcript context.suite]
      (producerBody (ringModel F G) side (producerOffset side) 10) := by
  cases side <;> kernel_rfl

def producer (side : Side) (handle layer index : Nat)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = producerOffset side)
    (layerRead : captured[10]? = some (.data (.index layer)))
    (add mul left right point : List F) (history : Domain.History (uniformCarriers F G))
    (routes : Routes .producer side handle layer index) :
    Original.Simulation
      (Original.IterationReturns (ProducerReturns layer) (GkrOriginalCoefficient.outer layer)
        (qualifyProtocolSite (roundContext side).applicationPrefix "s9") index
        [(producerOffset side) + 31, (producerOffset side) + 32, (producerOffset side) + 33, (producerOffset side) + 34, (producerOffset side) + 35, (producerOffset side) + 30] [.data (.vector scalarDomain), .data (.vector scalarDomain), .data (.vector scalarDomain), .data (.vector scalarDomain), .data (.vector scalarDomain), .transcript context.suite])
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (Original.fold (routing handle .producer)
        (roundBody.denote
          (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
            HonestProducerSource.observedHelpers 0 [] (roundContext side) Occurrence.iterations)
          ((.cons (some index) ((proverState (some add) (some mul) (some left) (some right) (some point)).append (.cons (none) .nil))) :
            Values (Component (assignment F G)) (.index :: (roundState ++ roundCaptures))).get)
        ⟨roundFrames side layer index, history⟩)
      (producerCompiled side (captured ++ .data (.index index) :: producerCarried add mul left right point history)) := by
  rw [HonestProducerSource.round_callback, producer_body]
  exact producerCallback side handle (producerOffset side) 10 layer index captured size layerRead
    add mul left right point history routes

def producerRepeat (side : Side) (handle layer : Nat)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = producerOffset side)
    (layerRead : captured[10]? = some (.data (.index layer)))
    (add mul left right point : List F) (history : Domain.History (uniformCarriers F G)) (count : Nat)
    (countRead : captured[5]? = some (.data (.index count)))
    (initialRead : Domain.read captured (producerInitial side) = some (producerCarried add mul left right point history))
    (routes : ∀ index, Routes .producer side handle layer index) :
    Original.Simulation
      (fun original final => ∃ next, ProducerReturns layer original next ∧ final = captured ++ next)
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (Original.fold (routing handle .producer)
        (denoteRepeatOn roundSpec (roundContext side) 0 (some count) (proverState (some add) (some mul) (some left) (some right) (some point))
          (.cons (none) .nil)
          (fun args => roundBody.denote
            (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
              HonestProducerSource.observedHelpers 0 [] (roundContext side) Occurrence.iterations) args.get)
          Occurrence.iterations "s9") ⟨GkrOriginalCoefficient.outer layer, history⟩)
      (producerLoop side captured) := by
  rw [producer_loop]
  apply Original.Simulation.occurrenceRepeat (routing handle .producer) roundSpec (roundContext side) 0
    (captures := .cons (none) .nil)
    (sourceBody := fun args => roundBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
        HonestProducerSource.observedHelpers 0 [] (roundContext side) Occurrence.iterations) args.get)
    (site := "s9") (relation := ProducerReturns layer)
  · cases side <;> rfl
  · intro original frame related
    obtain ⟨add, mul, left, right, point, history, rfl, rfl⟩ := related
    cases side <;> exact ⟨add, mul, left, right, point, history, rfl, rfl⟩
  · intro value state frame index related
    apply Classical.choice
    obtain ⟨add, mul, left, right, point, history, pair, rfl⟩ := related
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj pair
    refine ⟨?_⟩
    rw [HonestProducerSource.round_callback]
    rw [proverState_masked (roundContext side) 0 (by cases side <;> rfl)]
    exact producerCallback side handle (producerOffset side) 10 layer index captured size layerRead
      add mul left right point history (routes index)
  · intro original frame related
    obtain ⟨add, mul, left, right, point, history, rfl, rfl⟩ := related
    rfl
  · exact countRead
  · exact initialRead
  · rfl
  · cases side <;> exact ⟨add, mul, left, right, point, history, rfl, rfl⟩

end ZkcSecurity.Realizations.Gkr.OriginalRounds
