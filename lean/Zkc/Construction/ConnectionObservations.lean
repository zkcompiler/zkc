module

public import Zkc.Construction.ConnectionActions
public import Zkc.Construction.OriginalEffects

@[expose] public section

/-! The structural connection for transcript observations and public queries.
The source's reached history, nominal payload, origin and dependent reply are
retained. No distribution, independence, or cryptographic premise is used.
-/
set_option autoImplicit false
noncomputable section
namespace Zkc.Construction.Original
open Zkc.Source Zkc.Source.Structured
variable {carriers : Carriers}

/-- Recording a source message and executing its constructed observation
advance exactly the same history and append one physical transcript cell. -/
def Simulation.record (state : State carriers) (origin : Origin)
    (payload : Domain.Payload carriers) (context : Context) (template : Template)
    (stateRef valueRef pathRef : Nat) (environment : Domain.Environment carriers) (path : List Nat)
    (readState : environment[stateRef]? = some (.transcript context.suite state.history))
    (readValue : environment[valueRef]? = some (.data payload))
    (readPath : environment[pathRef]? = some (.indices path))
    (resolved : Domain.templateOrigin context template path = some origin)
    (message : origin.request = none) :
    Simulation (fun source target =>
      source = ((), { state with history := state.history ++ [.message origin payload] }) ∧
      target = environment ++ [.transcript context.suite (state.history ++ [.message origin payload])])
      (fun _ frame => frame = environment)
      (record state origin payload)
      (Domain.View.observe context context.suite template stateRef valueRef pathRef
        [.transcript context.suite] environment) := by
  rw [Domain.View.observe_eq context template stateRef valueRef pathRef environment
    state.history payload path origin readState readValue readPath resolved message]
  apply Simulation.call
  intro reply
  simp only [Domain.View.append, Domain.sortsMatch, List.map_cons, Domain.Value.sort,
    List.map_nil, beq_self_eq_true, ↓reduceIte]
  exact .done ⟨rfl, rfl⟩

/-- A public query fixes both the dependent reply carrier and the current
history. Every oracle reply advances the source and target by the same event. -/
def Simulation.queryField (state : State carriers) (origin : Origin) (field : String)
    (request : origin.request = some (.draw field)) (context : Context) (suite : String)
    (template : Template) (stateRef pathRef : Nat) (environment : Domain.Environment carriers)
    (path : List Nat)
    (readState : environment[stateRef]? = some (.transcript suite state.history))
    (readPath : environment[pathRef]? = some (.indices path))
    (resolved : Domain.queryOrigin context suite field template path = some origin) :
    Simulation (fun source target =>
      source.2 = { state with history := state.history ++ [.challenge origin] } ∧
      target = environment ++ [.data (.field field source.1),
        .transcript suite (state.history ++ [.challenge origin])])
      (fun _ frame => frame = environment)
      (queryField state origin field)
      (Domain.View.challenge context suite field template stateRef pathRef
        [.data (.field field), .transcript suite] environment) := by
  rw [queryField_eq state origin field request,
    Domain.View.challenge_eq context suite field template stateRef pathRef environment
      state.history path origin readState readPath resolved request]
  apply Simulation.call
  intro reply
  simp only [Domain.View.append, Domain.sortsMatch, List.map_cons, Domain.Value.sort,
    List.map_nil, beq_self_eq_true, ↓reduceIte]
  exact .done ⟨rfl, rfl⟩

/-- Private sampling retains the source history. It is a local-service
operation at its own nominal port, never a public challenge or observation. -/
def Simulation.localQuery (routing : Routing) (state : State carriers)
    (site field : String) (handle : Nat) (port : ServicePort) (origin : Origin)
    (localMode : routing.mode = .producer ∨
      (routing.mode = .validator ∧ routing.draw state.frames site field handle = none))
    (route : routing.local state.frames site field handle = some (port, origin))
    (request : origin.request = some (.draw field))
    (template : Template) (coordinates : List Nat) (environment : Domain.Environment carriers)
    (path : List Nat)
    (readPath : Domain.localCoordinates environment coordinates = some path)
    (contract : port.contract = "random." ++ field ++ "/0")
    (resolved : Domain.localOrigin routing.context port (.draw field) template path = some origin) :
    Simulation (fun source target => source.2 = state ∧
      target = environment ++ [.data (.field field source.1)])
      (fun _ frame => frame = environment)
      (query routing state site field handle)
      (Domain.View.localService routing.context port (.draw field) template coordinates []
        [.data (.field field)] environment) := by
  have source : query routing state site field handle =
      .call (.localService port origin) (fun reply =>
        .done (fieldReply origin field request reply, state)) := by
    rcases localMode with producer | ⟨validator, notPublic⟩
    · exact private_query_producer routing state site field handle port origin producer route request
    · exact private_query_validator routing state site field handle port origin validator notPublic route request
  rw [source]
  unfold Domain.View.localService
  dsimp only [Request.draw]
  simp only [readPath, contract, and_self, ↓reduceIte]
  change Domain.localOrigin routing.context port
    { method := "draw", operands := [], sort := .field field } template path = some origin at resolved
  change origin.request = some
    { method := "draw", operands := [], sort := .field field } at request
  rw [resolved]
  simp only [request, ↓reduceDIte]
  apply Simulation.call
  intro reply
  simp only [Domain.View.append, Domain.sortsMatch, List.map_cons, Domain.Value.sort,
    List.map_nil, beq_self_eq_true, ↓reduceIte]
  exact .done ⟨rfl, rfl⟩

/-- Scope weakening and history advancement are separate: an old transcript
cell is retired before the new one is made available to the next operation. -/
theorem observation_frame {model : DomainModel} {scope : NormalForm.Scope}
    {binders : NormalForm.Binders model scope} {history : Domain.History model.toCarriers}
    {layout : ConnectionFrame.Layout scope} {environment : Domain.Environment model.toCarriers}
    (related : ConnectionFrame.Holds model binders history layout environment)
    (suite : String) (event : Domain.Event model.toCarriers) :
    ConnectionFrame.Holds model binders (history ++ [event])
      (layout.map ConnectionFrame.Cell.retireHistory ++ [.history suite])
      (environment ++ [.transcript suite (history ++ [event])]) :=
  (related.retireHistory _).append (.cons rfl .nil)

/-- The query result is a nominal field value even when two source domains
happen to share a host carrier. Coordinates and older data retain their values. -/
theorem query_frame {model : DomainModel} {scope : NormalForm.Scope}
    {binders : NormalForm.Binders model scope} {history : Domain.History model.toCarriers}
    {layout : ConnectionFrame.Layout scope} {environment : Domain.Environment model.toCarriers}
    (related : ConnectionFrame.Holds model binders history layout environment)
    (suite field : String) (origin : Origin) (value : model.Field field) :
    ConnectionFrame.Holds model (.cons value binders) (history ++ [.challenge origin])
      ((layout.map ConnectionFrame.Cell.retireHistory).map
          (ConnectionFrame.Cell.rename (target := .value (.field field) :: scope) .there) ++
        [.data (.present (.var .here)), .history suite])
      (environment ++ [.data (.field field value),
        .transcript suite (history ++ [.challenge origin])]) :=
  ((related.retireHistory _).rename (target := .value (.field field) :: scope) .there
    (fun _ => rfl)).append (.cons ⟨value, rfl, rfl⟩ (.cons rfl .nil))

end Zkc.Construction.Original
