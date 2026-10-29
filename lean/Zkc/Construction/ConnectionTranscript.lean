module

public import Zkc.Construction.ConnectionObservations
public import Zkc.Construction.OriginalFrameRelations

@[expose] public section

/-! Exact message/transcript composition for either participant. The local
rules retain every checkpoint and every typed provider reply. They cover
nominal payload types, including vectors and groups, without field-specific
protocol instances. -/
set_option autoImplicit false
noncomputable section
namespace Zkc.Construction.Original
open Zkc.Source Zkc.Source.Structured
variable {carriers : Carriers}

/-- Extending an SSA frame preserves every established read from its prefix. -/
theorem read_append {environment : Domain.Environment carriers} {reference : Nat}
    {value : Domain.Value carriers} (read : environment[reference]? = some value)
    (suffix : Domain.Environment carriers) : (environment ++ suffix)[reference]? = some value := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp read).1]
  exact read

/-- A producer's actual send precedes the public observation. A stopped send
never reaches the observation or fabricates the appended history. -/
def Simulation.observedSendProducer (routing : Routing) (state : State carriers)
    (ty : Ty) (site : String) (receiver : Nat) (value : carriers.Value ty)
    (origin : Origin) (mode : routing.mode = .producer)
    (route : routing.message state.frames site routing.context.producer receiver = some origin)
    (payload : Domain.Payload carriers) (encoded : Domain.Payload.ofValue ty value = some payload)
    (template : Template) (stateRef valueRef pathRef : Nat) (environment : Domain.Environment carriers)
    (path : List Nat)
    (readState : environment[stateRef]? = some (.transcript routing.context.suite state.history))
    (readValue : environment[valueRef]? = some (.data payload))
    (readPath : environment[pathRef]? = some (.indices path))
    (resolved : Domain.templateOrigin routing.context template path = some origin)
    (message : origin.request = none) :
    Simulation (fun source target =>
      source = ((), { state with history := state.history ++ [.message origin payload] }) ∧
      target = environment ++ [.transcript routing.context.suite (state.history ++ [.message origin payload])])
      (fun _ frame => ArtifactBinding.Captures environment frame)
      (send routing state ty site receiver value)
      (Domain.View.sequence
        (Domain.View.send site site (routing.context.role receiver) valueRef [])
        (Domain.View.observe routing.context routing.context.suite template stateRef valueRef pathRef
          [.transcript routing.context.suite]) environment) := by
  simp only [send, mode, route, encoded]
  apply Simulation.checkpoint environment (by simp [ArtifactBinding.Captures])
  rw [Domain.View.send_eq site (routing.context.role receiver) valueRef environment payload readValue]
  change Simulation _ _ (.call _ (fun _ => Original.record state origin payload))
    (.call _ (fun _ => .call (.checkpoint environment) (fun _ => _)))
  apply Simulation.call
  intro reply
  apply Simulation.checkpoint environment (by simp [ArtifactBinding.Captures])
  exact (Simulation.record state origin payload routing.context template stateRef valueRef pathRef
    environment path readState readValue readPath resolved message).mapRelations
      (fun _ _ returned => returned) (fun _ frame same => by rw [same]; simp [ArtifactBinding.Captures])

/-- The validator's original challenge-delivery send is an observation, not a
second network message. The same payload and source route fix its transcript. -/
def Simulation.observedSendValidator (routing : Routing) (state : State carriers)
    (ty : Ty) (site : String) (receiver : Nat) (value : carriers.Value ty)
    (origin : Origin) (mode : routing.mode = .validator)
    (route : routing.message state.frames site routing.context.validator receiver = some origin)
    (payload : Domain.Payload carriers) (encoded : Domain.Payload.ofValue ty value = some payload)
    (template : Template) (stateRef valueRef pathRef : Nat) (environment : Domain.Environment carriers)
    (path : List Nat)
    (readState : environment[stateRef]? = some (.transcript routing.context.suite state.history))
    (readValue : environment[valueRef]? = some (.data payload))
    (readPath : environment[pathRef]? = some (.indices path))
    (resolved : Domain.templateOrigin routing.context template path = some origin)
    (message : origin.request = none) :
    Simulation (fun source target =>
      source = ((), { state with history := state.history ++ [.message origin payload] }) ∧
      target = environment ++ [.transcript routing.context.suite (state.history ++ [.message origin payload])])
      (fun _ frame => frame = environment)
      (send routing state ty site receiver value)
      (Domain.View.observe routing.context routing.context.suite template stateRef valueRef pathRef
        [.transcript routing.context.suite] environment) := by
  simpa only [send, mode, route, encoded] using
    Simulation.record state origin payload routing.context template stateRef valueRef pathRef
      environment path readState readValue readPath resolved message

/-- Every nominal receive returns the entire decoded payload and its newly
appended transcript. There is no relation that keeps only acceptance. -/
def ObservedReceived (context : Context) (ty : Ty) (state : State carriers)
    (origin : Origin) (environment : Domain.Environment carriers)
    (source : carriers.Value ty × State carriers) (target : Domain.Environment carriers) : Prop :=
  ∃ payload, Domain.Payload.ofValue ty source.1 = some payload ∧
    source.2 = { state with history := state.history ++ [.message origin payload] } ∧
    target = environment ++ [.data payload,
      .transcript context.suite (state.history ++ [.message origin payload])]

/-- Generic verifier receive followed by observation, with arbitrary nominal
peer replies. The receive and observation checkpoints retain the input prefix. -/
def Simulation.observedReceive (routing : Routing) (state : State carriers)
    (ty : Ty) (data : ty.isHandle = false) (site : String) (sender : Nat)
    (origin : Origin) (mode : routing.mode = .validator)
    (route : routing.message state.frames site sender routing.context.validator = some origin)
    (template : Template) (stateRef pathRef : Nat) (environment : Domain.Environment carriers)
    (path : List Nat)
    (readState : environment[stateRef]? = some (.transcript routing.context.suite state.history))
    (readPath : environment[pathRef]? = some (.indices path))
    (resolved : Domain.templateOrigin routing.context template path = some origin)
    (message : origin.request = none) :
    Simulation (ObservedReceived routing.context ty state origin environment)
      (fun _ frame => ArtifactBinding.Captures environment frame)
      (receive routing state ty site sender)
      (Domain.View.sequence
        (Domain.View.receive site site (routing.context.role sender) ty [.data ty])
        (Domain.View.observe routing.context routing.context.suite template stateRef environment.length pathRef
          [.transcript routing.context.suite]) environment) := by
  simp only [receive, mode, route]
  apply Simulation.checkpoint environment (by simp [ArtifactBinding.Captures])
  rw [Domain.View.receive_eq site (routing.context.role sender) ty environment (by simp [Domain.dataType, data])]
  apply Simulation.call
  intro value
  apply Classical.choice
  obtain ⟨physical, encoded⟩ := Domain.Value.encode_exists (carriers := carriers)
    (by simp [Domain.dataType, data]) value
  obtain ⟨payload, payloadEq, physicalEq⟩ : ∃ payload,
      Domain.Payload.ofValue ty value = some payload ∧ physical = .data payload := by
    unfold Domain.Value.encode at encoded
    cases found : Domain.Payload.ofValue ty value with
    | none => simp [found] at encoded
    | some payload => exact ⟨payload, rfl, (Option.some.inj (by simpa [found] using encoded)).symm⟩
  subst physical
  refine ⟨?_⟩
  simp only [payloadEq, encoded, Domain.View.append,
    show Domain.sortsMatch [.data ty] [.data payload] = true from by
      simp [Domain.sortsMatch, Domain.Value.encode_sort encoded], ↓reduceIte, PIR.Process.bind]
  refine .checkpoint _ (ArtifactBinding.captures_append environment [.data payload]) ?_
  have observed := Simulation.record state origin payload routing.context template stateRef environment.length pathRef
    (environment ++ [.data payload]) path (read_append readState _) (by simp) (read_append readPath _) resolved message
  have mapped := observed.bind
    (returnRelation := ObservedReceived routing.context ty state origin environment)
    (nextLive := fun _ frame => ArtifactBinding.Captures environment frame)
    (sourceNext := fun source => .done (value, source.2)) (targetNext := fun frame => .done frame)
    (fun _ frame same => by rw [same]; exact ArtifactBinding.captures_append _ _)
    (by
      intro source target returned
      obtain ⟨same, appended⟩ := returned
      rw [same]
      exact .done ⟨payload, payloadEq, rfl, by simpa only [List.append_assoc, List.cons_append, List.nil_append] using appended⟩)
  simpa only [PIR.Process.bind_done] using mapped

/-- One generic scope/history update supplies the next connection frame. -/
theorem ObservedReceived.frame {model : DomainModel} {scope : NormalForm.Scope}
    {binders : NormalForm.Binders model scope} {layout : ConnectionFrame.Layout scope}
    {context : Context} {ty : Ty} {state : State model.toCarriers} {origin : Origin}
    {environment target : Domain.Environment model.toCarriers}
    {source : model.Value ty × State model.toCarriers}
    (returned : ObservedReceived context ty state origin environment source target)
    (related : ConnectionFrame.Holds model binders state.history layout environment) :
    ConnectionFrame.Holds model (.cons source.1 binders) source.2.history
      ((layout.map ConnectionFrame.Cell.retireHistory).map
        (ConnectionFrame.Cell.rename (target := .value ty :: scope) .there) ++
          [.data (.present (.var .here)), .history context.suite]) target := by
  obtain ⟨payload, encoded, final, appended⟩ := returned
  rw [final, appended]
  exact ((related.retireHistory _).rename (target := .value ty :: scope) .there
    (fun _ => rfl)).append (.cons ⟨source.1, rfl, by simp [Domain.Value.encode, encoded]⟩ (.cons rfl .nil))

/-- A delivered challenge retains both its query event and its subsequent
message observation. The two transcript cells denote different reached states. -/
def Delivered (context : Context) (field : String) (state : State carriers)
    (draw message : Origin) (environment : Domain.Environment carriers)
    (source : carriers.Field field × State carriers) (target : Domain.Environment carriers) : Prop :=
  source.2 = { state with history := state.history ++
    [.challenge draw, .message message (.field field source.1)] } ∧
  target = environment ++ [.data (.field field source.1),
    .transcript context.suite (state.history ++ [.challenge draw]),
    .transcript context.suite (state.history ++ [.challenge draw, .message message (.field field source.1)])]

/-- The producer's original delivery receive aligns with a query followed by
observation. The proof preserves an arbitrary prior history and every typed
oracle reply; it does not assume that the provider succeeds. -/
def Simulation.deliveredChallenge (routing : Routing) (state : State carriers)
    (site field : String) (sender : Nat) (draw message : Origin)
    (mode : routing.mode = .producer)
    (route : routing.delivery state.frames site field sender = some (draw, message))
    (request : draw.request = some (.draw field))
    (queryTemplate messageTemplate : Template) (stateRef pathRef : Nat)
    (environment : Domain.Environment carriers) (path : List Nat)
    (readState : environment[stateRef]? = some (.transcript routing.context.suite state.history))
    (readPath : environment[pathRef]? = some (.indices path))
    (queryOrigin : Domain.queryOrigin routing.context routing.context.suite field queryTemplate path = some draw)
    (messageOrigin : Domain.templateOrigin routing.context messageTemplate path = some message)
    (messageRequest : message.request = none) :
    Simulation (Delivered routing.context field state draw message environment)
      (fun _ frame => ArtifactBinding.Captures environment frame)
      (receive routing state (.field field) site sender)
      (Domain.View.sequence
        (Domain.View.challenge routing.context routing.context.suite field queryTemplate stateRef pathRef
          [.data (.field field), .transcript routing.context.suite])
        (Domain.View.observe routing.context routing.context.suite messageTemplate (environment.length + 1)
          environment.length pathRef [.transcript routing.context.suite]) environment) := by
  simp only [receive, mode, route]
  apply Simulation.checkpoint environment (by simp [ArtifactBinding.Captures])
  apply (Simulation.queryField state draw field request routing.context routing.context.suite
    queryTemplate stateRef pathRef environment path readState readPath queryOrigin).bind
  · intro process frame same
    rw [same]
    simp [ArtifactBinding.Captures]
  · intro source target returned
    obtain ⟨final, appended⟩ := returned
    rcases source with ⟨value, reached⟩
    simp only at final appended
    subst reached target
    refine .checkpoint _ (ArtifactBinding.captures_append environment _) ?_
    have observed := Simulation.record
      ({ state with history := state.history ++ [.challenge draw] }) message (.field field value)
      routing.context messageTemplate (environment.length + 1) environment.length pathRef
      (environment ++ [.data (.field field value),
        .transcript routing.context.suite (state.history ++ [.challenge draw])]) path
      (by simp) (by simp) (read_append readPath _) messageOrigin messageRequest
    have mapped := observed.bind
      (returnRelation := Delivered routing.context field state draw message environment)
      (nextLive := fun _ frame => ArtifactBinding.Captures environment frame)
      (sourceNext := fun source => .done (value, source.2)) (targetNext := fun frame => .done frame)
      (fun _ frame same => by rw [same]; exact ArtifactBinding.captures_append _ _)
      (by
        intro source target returned
        obtain ⟨same, appended⟩ := returned
        rw [same]
        exact .done ⟨by simp [List.append_assoc], by
          simpa only [List.append_assoc, List.cons_append, List.nil_append] using appended⟩)
    simpa only [PIR.Process.bind_done] using mapped

end Zkc.Construction.Original
