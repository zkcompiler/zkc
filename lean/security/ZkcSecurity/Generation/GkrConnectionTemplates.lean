module

@[expose] public section

/-! GKR library installation schemas. Physical fields are holes filled from
recursive checked source/artifact descriptors. The two assembly strategies are
shared tactics; loop and root wrappers use the generic full simulation rules.
These proposals acquire authority only after independent kernel checking. -/
namespace ZkcSecurity.Generation.GkrConnectionTemplates

def originalOutput : String :=
  r###"open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured GkrSourceCallbacks
open ZkcExamples.Construction GkrSourceRouting GkrOriginalOutput
open ZkcSecurity.Realizations.Gkr.OriginalOutput
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

theorem producer_body :
    $PRODUCER_OUTPUT_BODY (ringModel F G) GkrSourceViews.program context =
      body (ringModel F G) $PRODUCER_OUTPUT_OFFSET := by kernel_rfl

theorem validator_body :
    $VALIDATOR_OUTPUT_BODY (ringModel F G) GkrSourceViews.program context =
      body (ringModel F G) $VALIDATOR_OUTPUT_OFFSET := by kernel_rfl

/-- Both actual physical layouts instantiate the same checked template. -/
def producer (handle index : Nat)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = $PRODUCER_OUTPUT_OFFSET)
    (point : List F) (history : Domain.History (uniformCarriers F G))
    (routes : Routes .producer handle index) :
    Certificate .producer handle $PRODUCER_OUTPUT_OFFSET index captured point history
      ($PRODUCER_OUTPUT_BODY (ringModel F G) GkrSourceViews.program context) := by
  rw [producer_body]
  exact observedCallback .producer handle $PRODUCER_OUTPUT_OFFSET index captured size point history routes

def validator (handle index : Nat)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = $VALIDATOR_OUTPUT_OFFSET)
    (point : List F) (history : Domain.History (uniformCarriers F G))
    (routes : Routes .validator handle index) :
    Certificate .validator handle $VALIDATOR_OUTPUT_OFFSET index captured point history
      ($VALIDATOR_OUTPUT_BODY (ringModel F G) GkrSourceViews.program context) := by
  rw [validator_body]
  exact observedCallback .validator handle $VALIDATOR_OUTPUT_OFFSET index captured size point history routes

theorem producer_repeat_body :
    $PRODUCER_OUTPUT_LOOP (ringModel F G) GkrSourceViews.program context =
      Domain.View.loop $PRODUCER_OUTPUT_MAXIMUM $PRODUCER_OUTPUT_YIELDS $PRODUCER_OUTPUT_COUNT $PRODUCER_OUTPUT_INITIAL
        [.data (.vector scalarDomain), .transcript context.suite] (body (ringModel F G) $PRODUCER_OUTPUT_OFFSET) := by
  kernel_rfl

theorem validator_repeat_body :
    $VALIDATOR_OUTPUT_LOOP (ringModel F G) GkrSourceViews.program context =
      Domain.View.loop $VALIDATOR_OUTPUT_MAXIMUM $VALIDATOR_OUTPUT_YIELDS $VALIDATOR_OUTPUT_COUNT $VALIDATOR_OUTPUT_INITIAL
        [.data (.vector scalarDomain), .transcript context.suite] (body (ringModel F G) $VALIDATOR_OUTPUT_OFFSET) := by
  kernel_rfl

def producerRepeat (handle : Nat)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = $PRODUCER_OUTPUT_OFFSET)
    (point : List F) (history : Domain.History (uniformCarriers F G)) (count : Nat)
    (countRead : captured[$PRODUCER_OUTPUT_COUNT]? = some (.data (.index count)))
    (initialRead : Domain.read captured $PRODUCER_OUTPUT_INITIAL = some (carried point history))
    (routes : ∀ index, Routes .producer handle index) :
    RepeatCertificate .producer handle captured point history count
      ($PRODUCER_OUTPUT_LOOP (ringModel F G) GkrSourceViews.program context) := by
  rw [producer_repeat_body]
  exact outputRepeat .producer handle $PRODUCER_OUTPUT_OFFSET captured size point history count $PRODUCER_OUTPUT_COUNT $PRODUCER_OUTPUT_INITIAL
    countRead initialRead routes

def validatorRepeat (handle : Nat)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = $VALIDATOR_OUTPUT_OFFSET)
    (point : List F) (history : Domain.History (uniformCarriers F G)) (count : Nat)
    (countRead : captured[$VALIDATOR_OUTPUT_COUNT]? = some (.data (.index count)))
    (initialRead : Domain.read captured $VALIDATOR_OUTPUT_INITIAL = some (carried point history))
    (routes : ∀ index, Routes .validator handle index) :
    RepeatCertificate .validator handle captured point history count
      ($VALIDATOR_OUTPUT_LOOP (ringModel F G) GkrSourceViews.program context) := by
  rw [validator_repeat_body]
  exact outputRepeat .validator handle $VALIDATOR_OUTPUT_OFFSET captured size point history count $VALIDATOR_OUTPUT_COUNT $VALIDATOR_OUTPUT_INITIAL
    countRead initialRead routes
"###

def originalRounds : String :=
  r###"open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured GkrRoundsNormalForms
open ZkcExamples.Construction GkrSourceRouting GkrOriginalRounds
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def validatorOffset : Side → Nat | .left => $VALIDATOR_LEFT_OFFSET | .right => $VALIDATOR_RIGHT_OFFSET
def validatorCount : Side → Nat | .left => $VALIDATOR_LEFT_COUNT | .right => $VALIDATOR_RIGHT_COUNT
def validatorInitial : Side → List Nat | .left => $VALIDATOR_LEFT_INITIAL | .right => $VALIDATOR_RIGHT_INITIAL
def validatorYielded : Side → List Nat | .left => $VALIDATOR_LEFT_YIELDS | .right => $VALIDATOR_RIGHT_YIELDS
theorem validator_yielded (side : Side) : validatorYielded side = $VALIDATOR_RELATIVE_YIELDS := by
  cases side <;> rfl

def validatorCompiled : Side → Domain.View.Block (uniformCarriers F G)
  | .left => $VALIDATOR_LEFT_BODY (ringModel F G) GkrSourceViews.program context
  | .right => $VALIDATOR_RIGHT_BODY (ringModel F G) GkrSourceViews.program context
def validatorLoop : Side → Domain.View.Block (uniformCarriers F G)
  | .left => $VALIDATOR_LEFT_LOOP (ringModel F G) GkrSourceViews.program context
  | .right => $VALIDATOR_RIGHT_LOOP (ringModel F G) GkrSourceViews.program context

theorem validator_body (side : Side) :
    validatorCompiled (F := F) (G := G) side =
      validatorBody (ringModel F G) side (validatorOffset side) $VALIDATOR_LAYER_OFFSET := by
  cases side <;> kernel_rfl

theorem validator_loop (side : Side) :
    validatorLoop (F := F) (G := G) side = Domain.View.loop $VALIDATOR_LEFT_MAXIMUM
      (validatorYielded side) (validatorCount side) (validatorInitial side)
      [.data (.vector scalarDomain), .data (.field scalarDomain), .transcript context.suite]
      (validatorBody (ringModel F G) side (validatorOffset side) $VALIDATOR_LAYER_OFFSET) := by
  cases side <;> kernel_rfl

def validator (side : Side) (handle layer index : Nat)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = validatorOffset side)
    (layerRead : captured[$VALIDATOR_LAYER_OFFSET]? = some (.data (.index layer)))
    (point : List F) (claim : F) (history : Domain.History (uniformCarriers F G))
    (routes : Routes .validator side handle layer index) :
    Original.Simulation
      (Original.IterationReturns (ValidatorReturns layer) (GkrOriginalCoefficient.outer layer)
        (qualifyProtocolSite (roundContext side).applicationPrefix "s9") index
        (validatorYielded side) [.data (.vector scalarDomain), .data (.field scalarDomain), .transcript context.suite])
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (Original.fold (routing handle .validator)
        (roundBody.denote
          (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
            HonestProducerSource.observedHelpers 1 [] (roundContext side) Occurrence.iterations)
          ((.cons (some index) ((verifierState (some point) (some claim)).append (.cons (some handle) .nil))) :
            Values (Component (assignment F G)) (.index :: (roundState ++ roundCaptures))).get)
        ⟨roundFrames side layer index, history⟩)
      (validatorCompiled side (captured ++ .data (.index index) :: validatorCarried point claim history)) := by
  rw [HonestProducerSource.round_callback, validator_body, validator_yielded]
  exact validatorCallback side handle (validatorOffset side) $VALIDATOR_LAYER_OFFSET layer index captured size layerRead
    point claim history routes

def validatorRepeat (side : Side) (handle layer : Nat)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = validatorOffset side)
    (layerRead : captured[$VALIDATOR_LAYER_OFFSET]? = some (.data (.index layer)))
    (point : List F) (claim : F) (history : Domain.History (uniformCarriers F G)) (count : Nat)
    (countRead : captured[(validatorCount side)]? = some (.data (.index count)))
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
  rw [validator_loop, validator_yielded]
  derive_gkr_repeat (Original.Simulation.occurrenceRepeat (routing handle .validator) roundSpec (roundContext side) 1
    (captures := .cons (some handle) .nil)
    (sourceBody := fun args => roundBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
        HonestProducerSource.observedHelpers 1 [] (roundContext side) Occurrence.iterations) args.get)
    (site := "s9") (relation := ValidatorReturns layer))
    gkr_destruct ⟨point, claim, history, rfl, rfl⟩
    gkr_callback_destruct ⟨point, claim, history, pair, rfl⟩
    gkr_returning ⟨point, claim, history, rfl, rfl⟩
    gkr_initial_returning ⟨point, claim, history, rfl, rfl⟩
    gkr_splitting (cases side)
    gkr_normalizing (
      rw [HonestProducerSource.round_callback]
      rw [verifierState_masked (roundContext side) 1 (by cases side <;> rfl)])
    gkr_callback (validatorCallback side handle (validatorOffset side) $VALIDATOR_LAYER_OFFSET layer index captured size layerRead
      point claim history (routes index))
    gkr_count_read countRead gkr_initial_read initialRead

def producerOffset : Side → Nat | .left => $PRODUCER_LEFT_OFFSET | .right => $PRODUCER_RIGHT_OFFSET
def producerCount : Side → Nat | .left => $PRODUCER_LEFT_COUNT | .right => $PRODUCER_RIGHT_COUNT
def producerInitial : Side → List Nat | .left => $PRODUCER_LEFT_INITIAL | .right => $PRODUCER_RIGHT_INITIAL
def producerYielded : Side → List Nat | .left => $PRODUCER_LEFT_YIELDS | .right => $PRODUCER_RIGHT_YIELDS
theorem producer_yielded (side : Side) : producerYielded side = $PRODUCER_RELATIVE_YIELDS := by
  cases side <;> rfl

def producerCompiled : Side → Domain.View.Block (uniformCarriers F G)
  | .left => $PRODUCER_LEFT_BODY (ringModel F G) GkrSourceViews.program context
  | .right => $PRODUCER_RIGHT_BODY (ringModel F G) GkrSourceViews.program context
def producerLoop : Side → Domain.View.Block (uniformCarriers F G)
  | .left => $PRODUCER_LEFT_LOOP (ringModel F G) GkrSourceViews.program context
  | .right => $PRODUCER_RIGHT_LOOP (ringModel F G) GkrSourceViews.program context

theorem producer_body (side : Side) :
    producerCompiled (F := F) (G := G) side =
      producerBody (ringModel F G) side (producerOffset side) $PRODUCER_LAYER_OFFSET := by
  cases side <;> kernel_rfl

theorem producer_loop (side : Side) :
    producerLoop (F := F) (G := G) side = Domain.View.loop $PRODUCER_LEFT_MAXIMUM
      (producerYielded side) (producerCount side) (producerInitial side)
      [.data (.vector scalarDomain), .data (.vector scalarDomain), .data (.vector scalarDomain), .data (.vector scalarDomain), .data (.vector scalarDomain), .transcript context.suite]
      (producerBody (ringModel F G) side (producerOffset side) $PRODUCER_LAYER_OFFSET) := by
  cases side <;> kernel_rfl

def producer (side : Side) (handle layer index : Nat)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = producerOffset side)
    (layerRead : captured[$PRODUCER_LAYER_OFFSET]? = some (.data (.index layer)))
    (add mul left right point : List F) (history : Domain.History (uniformCarriers F G))
    (routes : Routes .producer side handle layer index) :
    Original.Simulation
      (Original.IterationReturns (ProducerReturns layer) (GkrOriginalCoefficient.outer layer)
        (qualifyProtocolSite (roundContext side).applicationPrefix "s9") index
        (producerYielded side) [.data (.vector scalarDomain), .data (.vector scalarDomain), .data (.vector scalarDomain), .data (.vector scalarDomain), .data (.vector scalarDomain), .transcript context.suite])
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (Original.fold (routing handle .producer)
        (roundBody.denote
          (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
            HonestProducerSource.observedHelpers 0 [] (roundContext side) Occurrence.iterations)
          ((.cons (some index) ((proverState (some add) (some mul) (some left) (some right) (some point)).append (.cons (none) .nil))) :
            Values (Component (assignment F G)) (.index :: (roundState ++ roundCaptures))).get)
        ⟨roundFrames side layer index, history⟩)
      (producerCompiled side (captured ++ .data (.index index) :: producerCarried add mul left right point history)) := by
  rw [HonestProducerSource.round_callback, producer_body, producer_yielded]
  exact producerCallback side handle (producerOffset side) $PRODUCER_LAYER_OFFSET layer index captured size layerRead
    add mul left right point history routes

def producerRepeat (side : Side) (handle layer : Nat)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = producerOffset side)
    (layerRead : captured[$PRODUCER_LAYER_OFFSET]? = some (.data (.index layer)))
    (add mul left right point : List F) (history : Domain.History (uniformCarriers F G)) (count : Nat)
    (countRead : captured[(producerCount side)]? = some (.data (.index count)))
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
  rw [producer_loop, producer_yielded]
  derive_gkr_repeat (Original.Simulation.occurrenceRepeat (routing handle .producer) roundSpec (roundContext side) 0
    (captures := .cons (none) .nil)
    (sourceBody := fun args => roundBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
        HonestProducerSource.observedHelpers 0 [] (roundContext side) Occurrence.iterations) args.get)
    (site := "s9") (relation := ProducerReturns layer))
    gkr_destruct ⟨add, mul, left, right, point, history, rfl, rfl⟩
    gkr_callback_destruct ⟨add, mul, left, right, point, history, pair, rfl⟩
    gkr_returning ⟨add, mul, left, right, point, history, rfl, rfl⟩
    gkr_initial_returning ⟨add, mul, left, right, point, history, rfl, rfl⟩
    gkr_splitting (cases side)
    gkr_normalizing (
      rw [HonestProducerSource.round_callback]
      rw [proverState_masked (roundContext side) 0 (by cases side <;> rfl)])
    gkr_callback (producerCallback side handle (producerOffset side) $PRODUCER_LAYER_OFFSET layer index captured size layerRead
      add mul left right point history (routes index))
    gkr_count_read countRead gkr_initial_read initialRead"###

def originalCoefficient : String :=
  r###"open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured GkrSourceCallbacks
open ZkcExamples.Construction GkrSourceRouting GkrOriginalCoefficient
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

theorem validator_body :
    $VALIDATOR_COEFFICIENT_BODY (ringModel F G) GkrSourceViews.program context =
      validatorBody (ringModel F G) $VALIDATOR_COEFFICIENT_OFFSET $VALIDATOR_LAYER_OFFSET := by kernel_rfl

abbrev ValidatorCertificate (handle layer index : Nat)
    (captured : Domain.Environment (uniformCarriers F G))
    (coefficients : List F) (history : Domain.History (uniformCarriers F G))
    (compiled : Domain.View.Block (uniformCarriers F G)) :=
    Original.Simulation
      (Original.IterationReturns (ValidatorReturns layer) (outer layer) "s91" index
        $VALIDATOR_COEFFICIENT_YIELDS [.data (.vector scalarDomain), .transcript context.suite])
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (Original.fold (routing handle .validator)
        (coefficientBody.denote
          (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
            HonestProducerSource.observedHelpers 1 [] {} Occurrence.iterations)
          ((Values.cons (some index) ((verifierCoefficientState (some coefficients)).append
            (.cons none .nil))) :
            Values (Component (assignment F G)) (.index :: (coefficientState ++ coefficientCaptures))).get)
        ⟨frames layer index, history⟩)
      (compiled (captured ++ .data (.index index) :: carried coefficients history))

def validator (handle layer index : Nat)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = $VALIDATOR_COEFFICIENT_OFFSET)
    (layerRead : captured[$VALIDATOR_LAYER_OFFSET]? = some (.data (.index layer)))
    (coefficients : List F) (history : Domain.History (uniformCarriers F G))
    (routes : Routes .validator handle layer index) :
    ValidatorCertificate handle layer index captured coefficients history
      ($VALIDATOR_COEFFICIENT_BODY (ringModel F G) GkrSourceViews.program context) := by
  unfold ValidatorCertificate
  rw [HonestProducerSource.coefficient_callback, validator_body]
  exact validatorCallback handle $VALIDATOR_COEFFICIENT_OFFSET $VALIDATOR_LAYER_OFFSET layer index captured size layerRead coefficients history routes

abbrev ValidatorRepeatCertificate (handle layer : Nat)
    (captured : Domain.Environment (uniformCarriers F G))
    (coefficients : List F) (history : Domain.History (uniformCarriers F G))
    (count : Nat) (compiled : Domain.View.Block (uniformCarriers F G)) :=
    Original.Simulation
      (fun original final => ∃ next, ValidatorReturns layer original next ∧ final = captured ++ next)
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (Original.fold (routing handle .validator)
        (denoteRepeatOn coefficientSpec {} 1 (some count) (verifierCoefficientState (some coefficients))
          (.cons none .nil)
          (fun args => coefficientBody.denote
            (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
              HonestProducerSource.observedHelpers 1 [] {} Occurrence.iterations) args.get)
          Occurrence.iterations "s91") ⟨outer layer, history⟩)
      (compiled captured)

theorem validator_repeat_body :
    $VALIDATOR_COEFFICIENT_LOOP (ringModel F G) GkrSourceViews.program context =
      Domain.View.loop $VALIDATOR_COEFFICIENT_MAXIMUM $VALIDATOR_COEFFICIENT_YIELDS $VALIDATOR_COEFFICIENT_COUNT $VALIDATOR_COEFFICIENT_INITIAL
        [.data (.vector scalarDomain), .transcript context.suite]
        (validatorBody (ringModel F G) $VALIDATOR_COEFFICIENT_OFFSET $VALIDATOR_LAYER_OFFSET) := by kernel_rfl

def validatorRepeat (handle layer : Nat)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = $VALIDATOR_COEFFICIENT_OFFSET)
    (layerRead : captured[$VALIDATOR_LAYER_OFFSET]? = some (.data (.index layer)))
    (coefficients : List F) (history : Domain.History (uniformCarriers F G)) (count : Nat)
    (countRead : captured[$VALIDATOR_COEFFICIENT_COUNT]? = some (.data (.index count)))
    (initialRead : Domain.read captured $VALIDATOR_COEFFICIENT_INITIAL = some (carried coefficients history))
    (routes : ∀ index, Routes .validator handle layer index) :
    ValidatorRepeatCertificate handle layer captured coefficients history count
      ($VALIDATOR_COEFFICIENT_LOOP (ringModel F G) GkrSourceViews.program context) := by
  unfold ValidatorRepeatCertificate
  rw [validator_repeat_body]
  derive_gkr_repeat (Original.Simulation.occurrenceRepeat (routing handle .validator) coefficientSpec {} 1
    (captures := .cons none .nil)
    (sourceBody := fun args => coefficientBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
        HonestProducerSource.observedHelpers 1 [] {} Occurrence.iterations) args.get)
    (site := "s91") (relation := ValidatorReturns layer))
    gkr_destruct ⟨next, history, rfl, rfl⟩
    gkr_callback_destruct ⟨next, history, pair, rfl⟩
    gkr_returning ⟨next, history, rfl, rfl⟩
    gkr_initial_returning ⟨coefficients, history, rfl, rfl⟩
    gkr_splitting (skip)
    gkr_normalizing (rw [HonestProducerSource.coefficient_callback])
    gkr_callback (validatorCallback handle $VALIDATOR_COEFFICIENT_OFFSET $VALIDATOR_LAYER_OFFSET layer index captured size layerRead next history (routes index))
    gkr_count_read countRead gkr_initial_read initialRead


theorem producer_body :
    $PRODUCER_COEFFICIENT_BODY (ringModel F G) GkrSourceViews.program context =
      producerBody (ringModel F G) $PRODUCER_COEFFICIENT_OFFSET $PRODUCER_LAYER_OFFSET $PRODUCER_LINE := by kernel_rfl

abbrev ProducerCertificate (handle layer index : Nat)
    (captured : Domain.Environment (uniformCarriers F G))
    (line : List F) (history : Domain.History (uniformCarriers F G))
    (compiled : Domain.View.Block (uniformCarriers F G)) :=
    Original.Simulation
      (Original.IterationReturns (ProducerReturns layer) (outer layer) "s91" index
        $PRODUCER_COEFFICIENT_YIELDS [.transcript context.suite])
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (Original.fold (routing handle .producer)
        (coefficientBody.denote
          (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
            HonestProducerSource.observedHelpers 0 [] {} Occurrence.iterations)
          ((Values.cons (some index) (proverCoefficientState.append (.cons (some line) .nil))) :
            Values (Component (assignment F G)) (.index :: (coefficientState ++ coefficientCaptures))).get)
        ⟨frames layer index, history⟩)
      (compiled (captured ++ [.data (.index index), .transcript context.suite history]))

def producer (handle layer index : Nat)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = $PRODUCER_COEFFICIENT_OFFSET)
    (layerRead : captured[$PRODUCER_LAYER_OFFSET]? = some (.data (.index layer))) (line : List F)
    (lineRead : captured[$PRODUCER_LINE]? = some (.data (.vector scalarDomain line)))
    (history : Domain.History (uniformCarriers F G))
    (routes : Routes .producer handle layer index) :
    ProducerCertificate handle layer index captured line history
      ($PRODUCER_COEFFICIENT_BODY (ringModel F G) GkrSourceViews.program context) := by
  unfold ProducerCertificate
  rw [HonestProducerSource.coefficient_callback, producer_body]
  exact producerCallback handle $PRODUCER_COEFFICIENT_OFFSET $PRODUCER_LAYER_OFFSET $PRODUCER_LINE layer index captured size layerRead line lineRead history routes

abbrev ProducerRepeatCertificate (handle layer : Nat)
    (captured : Domain.Environment (uniformCarriers F G))
    (line : List F) (history : Domain.History (uniformCarriers F G))
    (count : Nat) (compiled : Domain.View.Block (uniformCarriers F G)) :=
    Original.Simulation
      (fun original final => ∃ next, ProducerReturns layer original next ∧ final = captured ++ next)
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (Original.fold (routing handle .producer)
        (denoteRepeatOn coefficientSpec {} 0 (some count) proverCoefficientState
          (.cons (some line) .nil)
          (fun args => coefficientBody.denote
            (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
              HonestProducerSource.observedHelpers 0 [] {} Occurrence.iterations) args.get)
          Occurrence.iterations "s91") ⟨outer layer, history⟩)
      (compiled captured)

theorem producer_repeat_body :
    $PRODUCER_COEFFICIENT_LOOP (ringModel F G) GkrSourceViews.program context =
      Domain.View.loop $PRODUCER_COEFFICIENT_MAXIMUM $PRODUCER_COEFFICIENT_YIELDS $PRODUCER_COEFFICIENT_COUNT $PRODUCER_COEFFICIENT_INITIAL [.transcript context.suite]
        (producerBody (ringModel F G) $PRODUCER_COEFFICIENT_OFFSET $PRODUCER_LAYER_OFFSET $PRODUCER_LINE) := by kernel_rfl

def producerRepeat (handle layer : Nat)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = $PRODUCER_COEFFICIENT_OFFSET)
    (layerRead : captured[$PRODUCER_LAYER_OFFSET]? = some (.data (.index layer))) (line : List F)
    (lineRead : captured[$PRODUCER_LINE]? = some (.data (.vector scalarDomain line)))
    (history : Domain.History (uniformCarriers F G)) (count : Nat)
    (countRead : captured[$PRODUCER_COEFFICIENT_COUNT]? = some (.data (.index count)))
    (initialRead : Domain.read captured $PRODUCER_COEFFICIENT_INITIAL = some [.transcript context.suite history])
    (routes : ∀ index, Routes .producer handle layer index) :
    ProducerRepeatCertificate handle layer captured line history count
      ($PRODUCER_COEFFICIENT_LOOP (ringModel F G) GkrSourceViews.program context) := by
  unfold ProducerRepeatCertificate
  rw [producer_repeat_body]
  derive_gkr_repeat (Original.Simulation.occurrenceRepeat (routing handle .producer) coefficientSpec {} 0
    (captures := .cons (some line) .nil)
    (sourceBody := fun args => coefficientBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
        HonestProducerSource.observedHelpers 0 [] {} Occurrence.iterations) args.get)
    (site := "s91") (relation := ProducerReturns layer))
    gkr_destruct ⟨history, rfl, rfl⟩
    gkr_callback_destruct ⟨history, pair, rfl⟩
    gkr_returning ⟨history, rfl, rfl⟩
    gkr_initial_returning ⟨history, rfl, rfl⟩
    gkr_splitting (skip)
    gkr_normalizing (rw [HonestProducerSource.coefficient_callback])
    gkr_callback (producerCallback handle $PRODUCER_COEFFICIENT_OFFSET $PRODUCER_LAYER_OFFSET $PRODUCER_LINE layer index captured size layerRead line lineRead history (routes index))
    gkr_count_read countRead gkr_initial_read initialRead"###

def originalValidatorLayer : String :=
  r###"open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured GkrSourceCallbacks GkrRoundsNormalForms
open ZkcExamples.Construction GkrSourceRouting HonestProducerSource
attribute [local irreducible] coefficientBody
attribute [local irreducible] Original.receive Original.send Original.query
attribute [local irreducible] Original.fold invoke invokeProtocol denoteRepeatOn
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def validatorCarried (point : List F) (claim : F) (history : Domain.History (uniformCarriers F G)) :
    Domain.Environment (uniformCarriers F G) :=
  [.data (.vector scalarDomain point), .data (.field scalarDomain claim), .transcript context.suite history]

def ValidatorReturns
    (source : Values (Component (assignment F G)) layerState × Original.State (uniformCarriers F G))
    (frame : Domain.Environment (uniformCarriers F G)) : Prop :=
  ∃ point claim history, source = (verifierLayerState (some point) (some claim), ⟨[], history⟩) ∧
    frame = validatorCarried (F := F) (G := G) point claim history

def validator (handle layer : Nat) (captured : Domain.Environment (uniformCarriers F G))
    (size : captured.length = $OFFSET) (initial add mul : List F) (layers selector width : Nat)
    (_inputRead : captured[$INPUT]? = some (.data (.vector scalarDomain initial)))
    (addRead : captured[$ADD]? = some (.data (.vector scalarDomain add)))
    (mulRead : captured[$MUL]? = some (.data (.vector scalarDomain mul)))
    (_layersRead : captured[$LAYERS]? = some (.data (.index layers)))
    (selectorRead : captured[$SELECTOR]? = some (.data (.index selector)))
    (widthRead : captured[$WIDTH]? = some (.data (.index width)))
    (point : List F) (claim : F) (history : Domain.History (uniformCarriers F G)) :
    Original.Simulation
      (Original.IterationReturns (ValidatorReturns (F := F) (G := G)) [] $SITE layer $YIELDS
        [.data (.vector scalarDomain), .data (.field scalarDomain), .transcript context.suite])
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (Original.fold (routing handle .validator)
        (layerBody.denote
          (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
            observedHelpers 1 beforeRoot {} Occurrence.iterations)
          ((.cons (some layer) ((verifierLayerState (some point) (some claim)).append
            (.cons (some initial) (.cons (some add) (.cons (some mul) (.cons (some layers)
              (.cons (some selector) (.cons (some width) (.cons (some handle) .nil))))))))) :
            Values (Component (assignment F G)) (.index :: (layerState ++ layerCaptures))).get)
        ⟨[⟨$SITE, layer⟩], history⟩)
      ($LAYER_BODY (ringModel F G) GkrSourceViews.program context
        (captured ++ .data (.index layer) :: validatorCarried (F := F) (G := G) point claim history)) := by
  apply Classical.choice
  obtain ⟨replacement, profile⟩ := Original.Routing.draw_profile (line_draw handle layer .validator)
  constructor
  unfold layerBody
  have roundsLeft := OriginalRegions.validator_rounds (F := F) (G := G) .left
  have roundsRight := OriginalRegions.validator_rounds (F := F) (G := G) .right
  dsimp only [roundContext, GkrVerifier.leftContext, ProtocolContext.enter] at roundsLeft
  dsimp only [roundContext, GkrVerifier.rightContext, ProtocolContext.enter] at roundsRight
  simp only [GkrSourceBodies.roundsSignature, qualify_root] at roundsLeft roundsRight
  have lineReceive := GkrOriginalLine.validator_receive (F := F) (G := G) handle layer
  have lineQuery := GkrOriginalLine.validator_query (F := F) (G := G) handle layer
  have lineSend := GkrOriginalLine.validator_send (F := F) (G := G) handle layer
  dsimp only [GkrOriginalLine.frames, GkrOriginalLine.constantSite,
    GkrOriginalLine.challengeSite, GkrOriginalLine.deliverySite, scalarDomain] at lineReceive lineQuery lineSend
  have suite : context.suite = "merlin3.bls12-381.fr64be/0" := rfl
  have compiledConstant := GkrOriginalLine.compiled_constant layer
  have compiledDraw := GkrOriginalLine.compiled_draw layer
  have compiledDelivery := GkrOriginalLine.compiled_delivery layer
  dsimp only [template12] at compiledConstant
  dsimp only [template14] at compiledDraw
  dsimp only [template15] at compiledDelivery
  unfold_component_bodies [$LAYER_BODY]
  derive_gkr_layer $LAYER_BODY
    using [GkrOriginalHelpers.continuation (F := F) (G := G),
      OriginalRounds.validatorRepeat (F := F) (G := G) .left handle layer,
      OriginalRounds.validatorRepeat (F := F) (G := G) .right handle layer,
      OriginalCoefficient.validatorRepeat (F := F) (G := G) handle layer]
    gkr_relations [GkrOriginalRounds.ValidatorReturns, GkrOriginalCoefficient.ValidatorReturns]
    gkr_effects [lineQuery, lineReceive, lineSend]
    gkr_presentation OriginalRegions.validatorRounds
    gkr_carried_law validatorCarried gkr_round_carried GkrOriginalRounds.validatorCarried
    gkr_initial_law OriginalRounds.validatorInitial gkr_offset_law OriginalRounds.validatorOffset gkr_count_law OriginalRounds.validatorCount
    gkr_reads [size, _inputRead, addRead, mulRead, _layersRead, selectorRead, widthRead]
    gkr_finishing (
      unfold Original.IterationReturns ValidatorReturns
      refine ⟨rfl, _, ?_, rfl, _, _, _, rfl, rfl⟩
      simp (disch := omega) only [Domain.read, validatorCarried, List.mapM_cons,
        List.mapM_nil, List.getElem?_append_right, size, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Bind.bind, Option.bind, Option.pure_def]
      rfl)


def validatorRepeat (handle : Nat) (captured : Domain.Environment (uniformCarriers F G))
    (size : captured.length = $OFFSET) (initial add mul : List F) (layers selector width : Nat)
    (_inputRead : captured[$INPUT]? = some (.data (.vector scalarDomain initial)))
    (addRead : captured[$ADD]? = some (.data (.vector scalarDomain add)))
    (mulRead : captured[$MUL]? = some (.data (.vector scalarDomain mul)))
    (_layersRead : captured[$LAYERS]? = some (.data (.index layers)))
    (selectorRead : captured[$SELECTOR]? = some (.data (.index selector)))
    (widthRead : captured[$WIDTH]? = some (.data (.index width)))
    (countRead : captured[$COUNT]? = some (.data (.index layers)))
    (point : List F) (claim : F) (history : Domain.History (uniformCarriers F G))
    (initialRead : Domain.read captured $INITIAL = some (validatorCarried point claim history)) :
    Original.Simulation
      (fun original final => ∃ next, ValidatorReturns original next ∧ final = captured ++ next)
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (Original.fold (routing handle .validator)
        (denoteRepeatOn layerSpec {} 1 (some layers) (verifierLayerState (some point) (some claim))
          (.cons (some initial) (.cons (some add) (.cons (some mul) (.cons (some layers)
        (.cons (some selector) (.cons (some width) (.cons (some handle) .nil)))))))
          (fun args => layerBody.denote
            (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
              observedHelpers 1 beforeRoot {} Occurrence.iterations) args.get) Occurrence.iterations $SITE) ⟨[], history⟩)
      ($VALIDATOR_LAYER_LOOP (ringModel F G) GkrSourceViews.program context captured) := by
  change Original.Simulation _ _ _
    (Domain.View.loop $MAXIMUM $YIELDS $COUNT $INITIAL [.data (.vector scalarDomain), .data (.field scalarDomain), .transcript context.suite]
      ($LAYER_BODY (ringModel F G) GkrSourceViews.program context) captured)
  derive_gkr_repeat (Original.Simulation.occurrenceRepeat (routing handle .validator) layerSpec {} 1
    (captures := (.cons (some initial) (.cons (some add) (.cons (some mul) (.cons (some layers)
        (.cons (some selector) (.cons (some width) (.cons (some handle) .nil))))))))
    (sourceBody := (fun args => layerBody.denote
            (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
              observedHelpers 1 beforeRoot {} Occurrence.iterations) args.get)) (site := $SITE) (relation := ValidatorReturns))
    gkr_destruct ⟨point, claim, history, rfl, rfl⟩
    gkr_callback_destruct ⟨point, claim, history, pair, rfl⟩
    gkr_returning ⟨point, claim, history, rfl, rfl⟩
    gkr_initial_returning ⟨point, claim, history, rfl, rfl⟩
    gkr_splitting (skip)
    gkr_normalizing (rw [verifierLayerState_masked {} 1 rfl])
    gkr_callback (validator handle index captured size initial add mul layers selector width
      _inputRead addRead mulRead _layersRead selectorRead widthRead point claim history)
    gkr_count_read countRead gkr_initial_read initialRead"###

def originalProducerLayer : String :=
  r###"open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured GkrSourceCallbacks GkrRoundsNormalForms
open ZkcExamples.Construction GkrSourceRouting HonestProducerSource
attribute [local irreducible] coefficientBody
attribute [local irreducible] Original.receive Original.send Original.query
attribute [local irreducible] Original.fold invoke invokeProtocol denoteRepeatOn
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def producerCarried (point : List F) (history : Domain.History (uniformCarriers F G)) :
    Domain.Environment (uniformCarriers F G) :=
  [.data (.vector scalarDomain point), .transcript context.suite history]

def ProducerReturns
    (source : Values (Component (assignment F G)) layerState × Original.State (uniformCarriers F G))
    (frame : Domain.Environment (uniformCarriers F G)) : Prop :=
  ∃ point history, source = (proverLayerState (some point), ⟨[], history⟩) ∧
    frame = producerCarried (F := F) (G := G) point history


def producer (handle layer : Nat) (captured : Domain.Environment (uniformCarriers F G))
    (size : captured.length = $OFFSET) (initial add mul : List F) (layers selector width : Nat)
    (inputRead : captured[$INPUT]? = some (.data (.vector scalarDomain initial)))
    (addRead : captured[$ADD]? = some (.data (.vector scalarDomain add)))
    (mulRead : captured[$MUL]? = some (.data (.vector scalarDomain mul)))
    (layersRead : captured[$LAYERS]? = some (.data (.index layers)))
    (selectorRead : captured[$SELECTOR]? = some (.data (.index selector)))
    (widthRead : captured[$WIDTH]? = some (.data (.index width)))
    (point : List F) (history : Domain.History (uniformCarriers F G)) :
    Original.Simulation
      (Original.IterationReturns (ProducerReturns (F := F) (G := G)) [] $SITE layer $YIELDS
        [.data (.vector scalarDomain), .transcript context.suite])
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (Original.fold (routing handle .producer)
        (layerBody.denote
          (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
            observedHelpers 0 beforeRoot {} Occurrence.iterations)
          ((.cons (some layer) ((proverLayerState (some point)).append
            (.cons (some initial) (.cons (some add) (.cons (some mul) (.cons (some layers)
              (.cons (some selector) (.cons (some width) (.cons none .nil))))))))) :
            Values (Component (assignment F G)) (.index :: (layerState ++ layerCaptures))).get)
        ⟨[⟨$SITE, layer⟩], history⟩)
      ($LAYER_BODY (ringModel F G) GkrSourceViews.program context
        (captured ++ .data (.index layer) :: producerCarried (F := F) (G := G) point history)) := by
  apply Classical.choice
  obtain ⟨replacement, profile⟩ := Original.Routing.draw_profile (line_draw handle layer .producer)
  constructor
  unfold layerBody
  have roundsLeft := OriginalRegions.producer_rounds (F := F) (G := G) .left
  have roundsRight := OriginalRegions.producer_rounds (F := F) (G := G) .right
  dsimp only [roundContext, GkrVerifier.leftContext, ProtocolContext.enter] at roundsLeft
  dsimp only [roundContext, GkrVerifier.rightContext, ProtocolContext.enter] at roundsRight
  simp only [GkrSourceBodies.roundsSignature, qualify_root] at roundsLeft roundsRight
  have lineSend := GkrOriginalLine.producer_send (F := F) (G := G) handle layer
  have lineReceive := GkrOriginalLine.producer_receive (F := F) (G := G) handle layer
  dsimp only [GkrOriginalLine.frames, GkrOriginalLine.constantSite,
    GkrOriginalLine.challengeSite, GkrOriginalLine.deliverySite, scalarDomain] at lineSend lineReceive
  have suite : context.suite = "merlin3.bls12-381.fr64be/0" := rfl
  have compiledConstant := GkrOriginalLine.compiled_constant layer
  have compiledDraw := GkrOriginalLine.compiled_draw layer
  have compiledDelivery := GkrOriginalLine.compiled_delivery layer
  dsimp only [template12] at compiledConstant
  dsimp only [template14] at compiledDraw
  dsimp only [template15] at compiledDelivery
  unfold_component_bodies [$LAYER_BODY]
  derive_gkr_layer $LAYER_BODY
    using [GkrOriginalHelpers.continuation (F := F) (G := G),
      OriginalRounds.producerRepeat (F := F) (G := G) .left handle layer,
      OriginalRounds.producerRepeat (F := F) (G := G) .right handle layer,
      OriginalCoefficient.producerRepeat (F := F) (G := G) handle layer]
    gkr_relations [GkrOriginalRounds.ProducerReturns, GkrOriginalCoefficient.ProducerReturns]
    gkr_effects [lineSend, lineReceive]
    gkr_presentation roundsPresentation
    gkr_carried_law producerCarried gkr_round_carried GkrOriginalRounds.producerCarried
    gkr_initial_law OriginalRounds.producerInitial gkr_offset_law OriginalRounds.producerOffset gkr_count_law OriginalRounds.producerCount
    gkr_reads [size, inputRead, addRead, mulRead, layersRead, selectorRead, widthRead]
    gkr_finishing (
      unfold Original.IterationReturns ProducerReturns
      refine ⟨rfl, _, ?_, rfl, _, _, rfl, rfl⟩
      simp (disch := omega) only [Domain.read, producerCarried, List.mapM_cons,
        List.mapM_nil, List.getElem?_append_right, size, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Bind.bind, Option.bind, Option.pure_def]
      rfl)


def producerRepeat (handle : Nat) (captured : Domain.Environment (uniformCarriers F G))
    (size : captured.length = $OFFSET) (initial add mul : List F) (layers selector width : Nat)
    (inputRead : captured[$INPUT]? = some (.data (.vector scalarDomain initial)))
    (addRead : captured[$ADD]? = some (.data (.vector scalarDomain add)))
    (mulRead : captured[$MUL]? = some (.data (.vector scalarDomain mul)))
    (layersRead : captured[$LAYERS]? = some (.data (.index layers)))
    (selectorRead : captured[$SELECTOR]? = some (.data (.index selector)))
    (widthRead : captured[$WIDTH]? = some (.data (.index width)))
    (countRead : captured[$COUNT]? = some (.data (.index layers)))
    (point : List F) (history : Domain.History (uniformCarriers F G))
    (initialRead : Domain.read captured $INITIAL = some (producerCarried point history)) :
    Original.Simulation
      (fun original final => ∃ next, ProducerReturns original next ∧ final = captured ++ next)
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (Original.fold (routing handle .producer)
        (denoteRepeatOn layerSpec {} 0 (some layers) (proverLayerState (some point))
          (.cons (some initial) (.cons (some add) (.cons (some mul) (.cons (some layers)
        (.cons (some selector) (.cons (some width) (.cons none .nil)))))))
          (fun args => layerBody.denote
            (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
              observedHelpers 0 beforeRoot {} Occurrence.iterations) args.get) Occurrence.iterations $SITE) ⟨[], history⟩)
      ($PRODUCER_LAYER_LOOP (ringModel F G) GkrSourceViews.program context captured) := by
  change Original.Simulation _ _ _
    (Domain.View.loop $MAXIMUM $YIELDS $COUNT $INITIAL [.data (.vector scalarDomain), .transcript context.suite]
      ($LAYER_BODY (ringModel F G) GkrSourceViews.program context) captured)
  derive_gkr_repeat (Original.Simulation.occurrenceRepeat (routing handle .producer) layerSpec {} 0
    (captures := (.cons (some initial) (.cons (some add) (.cons (some mul) (.cons (some layers)
        (.cons (some selector) (.cons (some width) (.cons none .nil))))))))
    (sourceBody := (fun args => layerBody.denote
            (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
              observedHelpers 0 beforeRoot {} Occurrence.iterations) args.get)) (site := $SITE) (relation := ProducerReturns))
    gkr_destruct ⟨point, history, rfl, rfl⟩
    gkr_callback_destruct ⟨point, history, pair, rfl⟩
    gkr_returning ⟨point, history, rfl, rfl⟩
    gkr_initial_returning ⟨point, history, rfl, rfl⟩
    gkr_splitting (skip)
    gkr_normalizing (rw [proverLayerState_masked {} 0 rfl])
    gkr_callback (producer handle index captured size initial add mul layers selector width
      inputRead addRead mulRead layersRead selectorRead widthRead point history)
    gkr_count_read countRead gkr_initial_read initialRead"###

def originalCertificateFrames : String :=
  r###"open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured GkrSourceCallbacks
open ZkcExamples.Construction GkrSourceRouting HonestProducerSource
attribute [local irreducible] outputBody layerBody
attribute [local irreducible] Original.fold invoke invokeProtocol denoteRepeatOn
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def producerInputs (initial add mul : List F) (layers selector width : Nat)
    (history : Domain.History (uniformCarriers F G)) : Domain.Environment (uniformCarriers F G) :=
  $PRODUCER_INPUT_VALUES

def validatorInputs (initial outputs add mul : List F) (layers selector width : Nat)
    (history : Domain.History (uniformCarriers F G)) : Domain.Environment (uniformCarriers F G) :=
  $VALIDATOR_INPUT_VALUES

abbrev SourceResult := Values (Component (assignment F G)) [.boolean] × Original.State (uniformCarriers F G)
"###

def originalValidatorBody : String :=
  r###"open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured GkrSourceCallbacks
open ZkcExamples.Construction GkrSourceRouting HonestProducerSource
attribute [local irreducible] outputBody layerBody
attribute [local irreducible] Original.fold invoke invokeProtocol denoteRepeatOn
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The validator's complete return frame retains the full pre-layer capture,
its exact arity, final point and claim, shared history, and Boolean return. -/
def ValidatorFrameReturns (inputs : Domain.Environment (uniformCarriers F G))
    (source : SourceResult (F := F) (G := G)) (frame : Domain.Environment (uniformCarriers F G)) : Prop :=
  ∃ captured point claim history value,
    source = (.cons (some value) .nil, ⟨[], history⟩) ∧
    captured.length = $VALIDATOR_LAYER_OFFSET ∧ ArtifactBinding.Captures inputs captured ∧
    frame = captured ++ [.data (.vector scalarDomain point), .data (.field scalarDomain claim),
      .transcript context.suite history, .data (.boolean value)]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem validatorFrameReturns {inputs frame : Domain.Environment (uniformCarriers F G)}
    (point : List F) (claim : F) (history : Domain.History (uniformCarriers F G)) (value : Bool)
    (size : (frame.take $VALIDATOR_LAYER_OFFSET).length = $VALIDATOR_LAYER_OFFSET)
    (retained : ArtifactBinding.Captures inputs (frame.take $VALIDATOR_LAYER_OFFSET))
    (shape : frame = frame.take $VALIDATOR_LAYER_OFFSET ++ [.data (.vector scalarDomain point),
      .data (.field scalarDomain claim), .transcript context.suite history, .data (.boolean value)]) :
    ValidatorFrameReturns inputs (.cons (some value) .nil, ⟨[], history⟩) frame :=
  ⟨frame.take $VALIDATOR_LAYER_OFFSET, point, claim, history, value, rfl, size, retained, shape⟩

def validatorBody (handle : Nat) (initial outputs add mul : List F) (layers selector width : Nat)
    (history : Domain.History (uniformCarriers F G)) :
    Original.Simulation
      (ValidatorFrameReturns (validatorInputs initial outputs add mul layers selector width history))
      (fun _ frame => ArtifactBinding.Captures (validatorInputs initial outputs add mul layers selector width history) frame)
      (Original.fold (routing handle .validator)
        (Occurrence.participant (ringModel F G) GkrSourceViews.program 1
          (GkrSourceAdmission.inputs (G := G) initial outputs add mul layers selector width handle)) ⟨[], history⟩)
      ($ROOT_BODY (ringModel F G) GkrSourceViews.program context
        (validatorInputs initial outputs add mul layers selector width history)) := by
  rw [OriginalRootRegions.root_body]
  have masked : maskValues 1 (({} : ProtocolContext).mapScopes GkrSourceViews.gkrDefinition.inputScopes)
      (GkrSourceAdmission.inputs (G := G) initial outputs add mul layers selector width handle) =
      GkrSourceAdmission.inputs (G := G) initial outputs add mul layers selector width handle := by rfl
  rw [masked]
  clear masked
  unfold gkrBody
  have input := OriginalRootRegions.validator_input (F := F) (G := G)
  dsimp only [ProtocolContext.enter] at input
  simp only [GkrSourceBodies.sourceProtocol80Signature, qualify_root] at input
  unfold_component_bodies [$ROOT_BODY]
  derive_gkr_body $ROOT_BODY
    using [GkrOriginalHelpers.continuation (F := F) (G := G),
      OriginalOutput.validatorRepeat (F := F) (G := G) handle,
      OriginalLayer.validatorRepeat (F := F) (G := G) handle]
    gkr_relations [GkrOriginalOutput.Returns, OriginalLayer.ValidatorReturns]
    gkr_input_law input
    gkr_inputs validatorInputs gkr_source_inputs GkrSourceAdmission.inputs
    gkr_carried_law OriginalLayer.validatorCarried
    gkr_finishing (
      rename_i point claim finalHistory value
      change ValidatorFrameReturns _ (.cons (some value) .nil, ⟨[], finalHistory⟩) _
      refine validatorFrameReturns point claim finalHistory value ?_ ?_ ?_
      all_goals simp [validatorInputs, ArtifactBinding.Captures, Original.encodeHelperResult,
        Domain.encodeValues, Domain.Value.encode, Domain.Payload.ofValue, Ty.isService,
        GkrOriginalOutput.carried, OriginalLayer.validatorCarried, List.append_assoc])
"###

def originalProducerBody : String :=
  r###"open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured GkrSourceCallbacks
open ZkcExamples.Construction GkrSourceRouting HonestProducerSource
attribute [local irreducible] outputBody layerBody
attribute [local irreducible] Original.fold invoke invokeProtocol denoteRepeatOn
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Every physical slot of the completed producer frame is fixed, including
both nested-loop results and histories; the original optional return is absent. -/
def ProducerFrameReturns (inputs : Domain.Environment (uniformCarriers F G))
    (source : SourceResult (F := F) (G := G)) (frame : Domain.Environment (uniformCarriers F G)) : Prop :=
  ∃ empty outputPoint outputHistory point history,
    source = (.cons none .nil, ⟨[], history⟩) ∧
    frame = inputs ++ $PRODUCER_PRELUDE ++ [.data (.vector scalarDomain empty), .data (.vector scalarDomain outputPoint),
      .transcript context.suite outputHistory, .data (.vector scalarDomain point), .transcript context.suite history]

def producerBody (handle : Nat) (initial add mul : List F) (layers selector width : Nat)
    (history : Domain.History (uniformCarriers F G)) :
    Original.Simulation
      (ProducerFrameReturns (producerInputs initial add mul layers selector width history))
      (fun _ frame => ArtifactBinding.Captures (producerInputs initial add mul layers selector width history) frame)
      (Original.fold (routing handle .producer)
        (Occurrence.participant (ringModel F G) GkrSourceViews.program 0
          (GkrProverContinuation.inputs (G := G) initial add mul layers selector width)) ⟨[], history⟩)
      ($ROOT_BODY (ringModel F G) GkrSourceViews.program context
        (producerInputs initial add mul layers selector width history)) := by
  rw [OriginalRootRegions.root_body]
  have masked : maskValues 0 (({} : ProtocolContext).mapScopes GkrSourceViews.gkrDefinition.inputScopes)
      (GkrProverContinuation.inputs (G := G) initial add mul layers selector width) =
      GkrProverContinuation.inputs (G := G) initial add mul layers selector width := by rfl
  rw [masked]
  have expansion : gkrBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
        observedHelpers 0 beforeRoot {} Occurrence.iterations)
      (GkrProverContinuation.inputs (G := G) initial add mul layers selector width).get = ?_ := by
    derive_process
    all_goals exact Region.Derivation.identity _ _ _
  rw [expansion]
  clear expansion masked
  unfold_component_bodies [$ROOT_BODY]
  derive_gkr_body $ROOT_BODY
    using [GkrOriginalHelpers.continuation (F := F) (G := G),
      OriginalOutput.producerRepeat (F := F) (G := G) handle,
      OriginalLayer.producerRepeat (F := F) (G := G) handle]
    gkr_relations [GkrOriginalOutput.Returns, OriginalLayer.ProducerReturns]
    gkr_input_law OriginalRegions.output_table
    gkr_inputs producerInputs gkr_source_inputs GkrProverContinuation.inputs
    gkr_carried_law OriginalLayer.producerCarried
    gkr_finishing (
      unfold ProducerFrameReturns
      rename_i empty outputPoint outputHistory point finalHistory
      refine ⟨empty, outputPoint, outputHistory, point, finalHistory, ?_, ?_⟩
      · simp
      · simp only [producerInputs, Original.encodeHelperResult, Domain.encodeValues,
          Domain.Value.encode, Domain.Payload.ofValue, Ty.isService, GkrOriginalOutput.carried,
          OriginalLayer.producerCarried, List.append_assoc, List.cons_append, List.nil_append]
        rfl)
"###

def originalValidatorRoot : String :=
  r###"open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured GkrSourceCallbacks
open ZkcExamples.Construction GkrSourceRouting HonestProducerSource
attribute [local irreducible] outputBody layerBody
attribute [local irreducible] Original.fold invoke invokeProtocol denoteRepeatOn
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def validatorInputABI (handle : Nat) : Original.InputABI :=
  ⟨$VALIDATOR_VIEW.inputSorts,
    $VALIDATOR_INPUT_ABI⟩

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
  rw [$VALIDATOR_VIEW.participant_eq]
  refine Original.Simulation.participant (validatorInputABI handle)
    (GkrSourceAdmission.inputs (G := G) initial outputs add mul layers selector width handle)
    (validatorInputs initial outputs add mul layers selector width history) _ _ _ _ _ _ rfl ?_ ?_
    (validatorBody handle initial outputs add mul layers selector width history) ?_
  · intro reference present
    simp [validatorInputABI] at present
    simp only [validatorInputs, List.length_cons, List.length_nil]
    omega
  · simp [validatorInputABI, GkrSourceAdmission.inputs, validatorInputs,
      Original.ValuesHolds, Original.ComponentHolds, Domain.Value.decode, Domain.Payload.value, scalarDomain]
  · intro original final related
    obtain ⟨captured, point, claim, history, value, rfl, size, retained, rfl⟩ := related
    refine ⟨[.data (.boolean value), .transcript context.suite history], ?_, rfl, ?_⟩
    ·
      simp (disch := omega) only [$VALIDATOR_VIEW.returned, Domain.read, List.mapM_cons,
        List.mapM_nil, List.getElem?_append_right, size, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Bind.bind, Option.bind, Option.pure_def]
    · exact ⟨⟨captured, point, claim, history, value, rfl, size, retained, rfl⟩, value, rfl, rfl⟩

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
"###

def originalProducerRoot : String :=
  r###"open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured GkrSourceCallbacks
open ZkcExamples.Construction GkrSourceRouting HonestProducerSource
attribute [local irreducible] outputBody layerBody
attribute [local irreducible] Original.fold invoke invokeProtocol denoteRepeatOn
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def producerInputABI : Original.InputABI :=
  ⟨$PRODUCER_VIEW.inputSorts,
    $PRODUCER_INPUT_ABI⟩

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
  rw [producer_source_inputs, $PRODUCER_VIEW.participant_eq]
  refine Original.Simulation.participant producerInputABI
    (GkrProverContinuation.inputs (G := G) initial add mul layers selector width)
    (producerInputs initial add mul layers selector width history) _ _ _ _ _ _ rfl ?_ ?_
    (producerBody handle initial add mul layers selector width history) ?_
  · intro reference present
    simp [producerInputABI] at present
    simp only [producerInputs, List.length_cons, List.length_nil]
    omega
  · simp [producerInputABI, GkrProverContinuation.inputs, producerInputs,
      Original.ValuesHolds, Original.ComponentHolds, Domain.Value.decode, Domain.Payload.value, scalarDomain]
  · intro original final related
    obtain ⟨empty, outputPoint, outputHistory, point, history, rfl, rfl⟩ := related
    refine ⟨[.transcript context.suite history], ?_, rfl, ?_⟩
    ·
      simp only [$PRODUCER_VIEW.returned, Domain.read, producerInputs, List.cons_append,
        List.nil_append, List.append_assoc, List.mapM_cons, List.mapM_nil, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Bind.bind, Option.bind, Option.pure_def]
    · exact ⟨⟨empty, outputPoint, outputHistory, point, history, rfl, rfl⟩, rfl⟩

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
"###

end ZkcSecurity.Generation.GkrConnectionTemplates
