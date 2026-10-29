module

public import Zkc.Construction.Uniform.LoopedSourceProcess
public import Zkc.Construction.OriginalABI
public import Zkc.Source.Structured.CommonAdapter

@[expose] public section

/-! A source-owned routing witness and its scalar observation theorem. The
witness inspects only reached source effects and iteration boundaries. It
contains no constructed instructions or assumed process equality. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
namespace Zkc.Construction.Uniform.OccurrenceSourceProcess
open Zkc.Source Zkc.Source.Structured
open LoopedSourceProcess
variable {F G A B : Type}

/-- Every reached scalar action resolves against the admitted source, with its
actual occurrence stack. Both entry and exit stacks are part of the witness. -/
inductive Routed (routing : Original.Routing) : Original.Frames → Original.Frames →
    PIR.Process (Occurrence.signature (uniformCarriers F G)) A → Type where
  | done (frames : Original.Frames) (value : A) : Routed routing frames frames (.done value)
  | halt (frames final : Original.Frames) (reason : PIR.Stop) :
      Routed routing frames final (.halt reason)
  | enter (frames final : Original.Frames) (frame : Occurrence.Frame)
      {next : Unit → PIR.Process (Occurrence.signature (uniformCarriers F G)) A}
      (tail : Routed routing (frames ++ [frame]) final (next ())) :
      Routed routing frames final (.call (.enter frame) next)
  | leave (frames final : Original.Frames) (frame : Occurrence.Frame)
      {next : Unit → PIR.Process (Occurrence.signature (uniformCarriers F G)) A}
      (last : frames.getLast? = some frame)
      (tail : Routed routing frames.dropLast final (next ())) :
      Routed routing frames final (.call (.leave frame) next)
  | receive (frames final : Original.Frames) (site field : String) (sender : Nat) (origin : Origin)
      {next : F → PIR.Process (Occurrence.signature (uniformCarriers F G)) A}
      (route : routing.message frames site sender routing.context.validator = some origin)
      (key : Origin.withoutCoordinates origin = routing.context.message site sender routing.context.validator)
      (tail : ∀ reply, Routed routing frames final (next reply)) :
      Routed routing frames final (.call (.action (.receive (.field field) site sender)) next)
  | send (frames final : Original.Frames) (site field : String) (receiver : Nat) (value : F)
      (origin : Origin)
      {next : Unit → PIR.Process (Occurrence.signature (uniformCarriers F G)) A}
      (route : routing.message frames site routing.context.validator receiver = some origin)
      (key : Origin.withoutCoordinates origin = routing.context.message site routing.context.validator receiver)
      (tail : Routed routing frames final (next ())) :
      Routed routing frames final (.call (.action (.send (ty := .field field) site receiver value)) next)
  | query (frames final : Original.Frames) (site field : String) (handle : Nat) (origin : Origin)
      {next : F → PIR.Process (Occurrence.signature (uniformCarriers F G)) A}
      (route : routing.draw frames site field handle = some origin)
      (key : Origin.withoutCoordinates origin = routing.context.query site (.draw field))
      (request : origin.request = some (.draw field))
      (tail : ∀ reply, Routed routing frames final (next reply)) :
      Routed routing frames final (.call (.action (.query site field (.cons handle .nil))) next)

 noncomputable def Routed.bind {routing : Original.Routing} {frames middle final : Original.Frames}
    {source : PIR.Process (Occurrence.signature (uniformCarriers F G)) A}
    {next : A → PIR.Process (Occurrence.signature (uniformCarriers F G)) B}
    (head : Routed routing frames middle source)
    (tail : ∀ value, Routed routing middle final (next value)) :
    Routed routing frames final (source.bind next) := by
  induction head with
  | done => exact tail _
  | halt => exact .halt _ _ _
  | enter frames final frame head ih => exact .enter _ _ _ (ih tail)
  | leave frames final frame last head ih => exact .leave _ _ _ last (ih tail)
  | receive frames final site field sender origin route key head ih =>
      exact .receive _ _ _ _ _ _ route key (fun reply => ih reply tail)
  | send frames final site field receiver value origin route key head ih =>
      exact .send _ _ _ _ _ _ _ route key (ih tail)
  | query frames final site field handle origin route key request head ih =>
      exact .query _ _ _ _ _ _ route key request (fun reply => ih reply tail)

 noncomputable def Routed.finite {routing : Original.Routing} {frames : Original.Frames} {Item : Type}
    (step : A → Item → PIR.Process (Occurrence.signature (uniformCarriers F G)) A)
    (law : ∀ state item, Routed routing frames frames (step state item))
    (items : List Item) (initial : A) :
    Routed routing frames frames (Finite.fold step items initial) := by
  induction items generalizing initial with
  | nil => exact .done _ _
  | cons item rest ih => exact (law _ _).bind fun next => ih next

/-- Route one retained operation and its reply-dependent source continuation.
The callback meanings remain the actual region denotations. -/
noncomputable def Routed.letOp {dialect : Dialect} {routing : Original.Routing}
    {frames middle final : Original.Frames}
    (meaning : RegionMeaning dialect (Occurrence.signature (uniformCarriers F G)))
    {inputs outputs : List dialect.Ty} (operation : dialect.Op)
    (arguments : Operands inputs (dialect.arguments operation))
    (callbacks : Regions dialect (dialect.regions operation))
    (next : Region dialect (dialect.results operation ++ inputs) outputs)
    (environment : Environment meaning.Value inputs)
    (head : Routed routing frames middle
      (meaning.operation operation (arguments.eval environment) (callbacks.denote meaning)))
    (tail : ∀ values, Routed routing middle final
      (next.denote meaning (environment.prepend values))) :
    Routed routing frames final
      ((Region.letOp operation arguments callbacks next).denote meaning environment) :=
  head.bind tail

/-- A checked pure operation needs only its actual continuation value. -/
noncomputable def Routed.pureLet {dialect : Dialect} {routing : Original.Routing}
    {frames final : Original.Frames}
    (meaning : RegionMeaning dialect (Occurrence.signature (uniformCarriers F G)))
    {inputs outputs : List dialect.Ty} (operation : dialect.Op)
    (arguments : Operands inputs (dialect.arguments operation))
    (callbacks : Regions dialect (dialect.regions operation))
    (next : Region dialect (dialect.results operation ++ inputs) outputs)
    (environment : Environment meaning.Value inputs)
    (values : Values meaning.Value (dialect.results operation))
    (pure : meaning.operation operation (arguments.eval environment) (callbacks.denote meaning) =
      .done values)
    (tail : Routed routing frames final (next.denote meaning (environment.prepend values))) :
    Routed routing frames final
      ((Region.letOp operation arguments callbacks next).denote meaning environment) := by
  rw [Region.denote, pure]
  exact tail

noncomputable def Routed.closed {routing : Original.Routing} (frames : Original.Frames)
    (process : PIR.Process closedInterface A) :
    Routed routing frames frames (process.interpret (closedLift (I := Occurrence.signature (uniformCarriers F G)))) := by
  induction process with
  | done value => exact .done _ _
  | halt reason => exact .halt _ _ _
  | call operation next ih => cases operation

noncomputable def Routed.within {routing : Original.Routing} {frames : Original.Frames}
    (site : String) (index : Nat)
    {process : PIR.Process (Occurrence.signature (uniformCarriers F G)) A}
    (body : Routed routing (frames ++ [⟨site, index⟩]) (frames ++ [⟨site, index⟩]) process) :
    Routed routing frames frames (Occurrence.iterations.within site index process) := by
  simp only [IterationObservations.within_eq, Occurrence.iterations,
    IterationObservations.enter, IterationObservations.leave, PIR.Process.bind]
  apply Routed.enter
  apply body.bind
  intro value
  apply Routed.leave _ _ _ (by simp)
  simpa using Routed.done (F := F) (G := G) (routing := routing) frames value

noncomputable def Routed.owned {routing : Original.Routing} (frames : Original.Frames)
    {inputs outputs : List Ty} (self owner : Nat)
    (work : Values (assignment F G) inputs →
      PIR.Process (Occurrence.signature (uniformCarriers F G)) (Values (assignment F G) outputs))
    (law : ∀ arguments, Routed routing frames frames (work arguments))
    (arguments : Values (Component (assignment F G)) inputs) :
    Routed routing frames frames (Participant.owned self owner work arguments) := by
  unfold Participant.owned
  split
  · cases RoleFamily.sequence arguments with
    | none => exact .halt _ _ _
    | some values => exact (law values).bind fun output => .done _ _
  · exact .done _ _

/-- A local guard has no externally answered effect, for either participant
and every optional Boolean component. Its stopped branches remain stopped. -/
noncomputable def Routed.guard {routing : Original.Routing} (frames : Original.Frames)
    (self owner : Nat) (condition : Option Bool) :
    Routed routing frames frames
      ((Participant.guard (services := services) (Value := (uniformCarriers F G).Value)
        self owner condition).interpret Occurrence.actions) := by
  unfold Participant.guard
  split
  · cases condition with
    | none => exact .halt _ _ _
    | some value => cases value <;> first | exact .halt _ _ _ | exact .done _ _
  · exact .done _ _

/-- A retained repeat checks its bound and masks before entering each actual
source coordinate. Callback routing covers every carried tuple. -/
noncomputable def Routed.repeat {routing : Original.Routing} (frames : Original.Frames)
    (spec : RepeatSpec) (context : ProtocolContext) (self : Nat) (site : String)
    (count : Option Nat)
    (state : Values (Component (uniformCarriers F G).Value) spec.state)
    (captures : Values (Component (uniformCarriers F G).Value) spec.captures)
    (body : RegionFunction (Component (uniformCarriers F G).Value)
      (Occurrence.signature (uniformCarriers F G))
      (.index :: (spec.state ++ spec.captures), spec.state))
    (law : ∀ index arguments,
      Routed routing (frames ++ [⟨qualifyProtocolSite context.applicationPrefix site, index⟩])
        (frames ++ [⟨qualifyProtocolSite context.applicationPrefix site, index⟩])
        (body (.cons (some index) arguments))) :
    Routed routing frames frames
      (denoteRepeatOn spec context self count state captures body Occurrence.iterations site) := by
  cases count with
  | none =>
      simp only [denoteRepeatOn]
      split <;> first | exact .halt _ _ _ | exact .done _ _
  | some count =>
      simp only [denoteRepeatOn]
      split
      · split
        · apply Routed.finite
          intro state index
          unfold Repeat.stepOn
          exact (Routed.within _ _ (law index _)).bind fun _ => .done _ _
        · exact .halt _ _ _
      · exact .done _ _

/-- The capture tuple is immutable throughout a retained repeat. Routing may
use its actual service capability while still covering every carried state. -/
noncomputable def Routed.repeatCaptured {routing : Original.Routing} (frames : Original.Frames)
    (spec : RepeatSpec) (context : ProtocolContext) (self : Nat) (site : String)
    (count : Option Nat)
    (state : Values (Component (uniformCarriers F G).Value) spec.state)
    (captures : Values (Component (uniformCarriers F G).Value) spec.captures)
    (body : RegionFunction (Component (uniformCarriers F G).Value)
      (Occurrence.signature (uniformCarriers F G))
      (.index :: (spec.state ++ spec.captures), spec.state))
    (law : ∀ index carried,
      Routed routing (frames ++ [⟨qualifyProtocolSite context.applicationPrefix site, index⟩])
        (frames ++ [⟨qualifyProtocolSite context.applicationPrefix site, index⟩])
        (body (.cons (some index)
          ((maskValues self (context.mapScopes spec.stateScopes) carried).append captures)))) :
    Routed routing frames frames
      (denoteRepeatOn spec context self count state captures body Occurrence.iterations site) := by
  cases count with
  | none =>
      simp only [denoteRepeatOn]
      split <;> first | exact .halt _ _ _ | exact .done _ _
  | some count =>
      simp only [denoteRepeatOn]
      split
      · split
        · apply Routed.finite
          intro state index
          unfold Repeat.stepOn
          exact (Routed.within _ _ (law index state)).bind fun _ => .done _ _
        · exact .halt _ _ _
      · exact .done _ _

 theorem history_append (first second : Domain.History (uniformCarriers F G)) :
    history (first ++ second) = history first ++ history second := List.map_append ..

theorem fold_call (routing : Original.Routing)
    (op : (Occurrence.signature (uniformCarriers F G)).Op)
    (next : (Occurrence.signature (uniformCarriers F G)).Reply op →
      PIR.Process (Occurrence.signature (uniformCarriers F G)) A)
    (state : Original.State (uniformCarriers F G)) :
    Original.fold routing (.call op next) state =
      (Original.operations routing op state).bind fun result =>
        Original.fold routing (next result.1) result.2 := rfl

attribute [local irreducible] Original.fold

/-- The scalar projection retains the full source result and exact projected
suffix. Nominal occurrence data stays in the independent structural witness. -/
noncomputable def Routed.simulation {routing : Original.Routing}
    (mode : routing.mode = .validator)
    (replacement : Replacement)
    (profileEq : routing.context.profile = .fiatShamir replacement)
    {frames final : Original.Frames}
    {source : PIR.Process (Occurrence.signature (uniformCarriers F G)) A}
    (law : Routed routing frames final source) (suffix : Domain.History (uniformCarriers F G)) :
    Original.Simulation
      (fun scalar actual => scalar.1 = actual.1 ∧ actual.2.frames = final ∧
        scalar.2 = history actual.2.history)
      (fun _ _ => True)
      (SourceProcess.sourceView routing.context
        ((source.interpret Occurrence.erase).interpret CommonAdapter.project) (history suffix))
      ((Original.fold routing source ⟨frames, suffix⟩).interpret operations) := by
  induction law generalizing suffix with
  | done => unfold Original.fold; exact .done ⟨rfl, rfl, rfl⟩
  | halt => unfold Original.fold; exact .halt _
  | enter frames final frame tail ih =>
      simpa only [fold_call, Original.operations,
        PIR.Process.bind, PIR.Process.interpret, Occurrence.erase] using ih suffix
  | leave frames final frame last tail ih =>
      simpa only [fold_call, Original.operations,
        last, ↓reduceIte, PIR.Process.bind, PIR.Process.interpret, Occurrence.erase] using ih suffix
  | receive frames final site field sender origin route key tail ih =>
      rw [fold_call]
      simp only [Original.operations, profileEq]
      simp only [Original.receive, mode, route]
      simp only [PIR.Process.bind, PIR.Process.interpret, Occurrence.erase, CommonAdapter.project]
      simp only [SourceProcess.sourceView, SourceProcess.receive, operations]
      apply Original.Simulation.call
      intro reply
      simp only [Domain.Payload.ofValue, Ty.isService, ↓reduceDIte, Original.record, PIR.Process.bind, PIR.Process.interpret,
        operations, event, key]
      rw [key]
      apply Original.Simulation.call
      intro ignored
      have current := ih reply (suffix ++ [.message origin (.field field reply)])
      rw [history_append] at current
      simpa only [history, List.map_cons, List.map_nil, event, key] using current
  | send frames final site field receiver value origin route key tail ih =>
      simp only [fold_call, Original.operations, profileEq,
        Original.send, mode, route, Domain.Payload.ofValue, Ty.isService, ↓reduceDIte, Original.record,
        PIR.Process.bind, PIR.Process.interpret, Occurrence.erase, CommonAdapter.project,
        SourceProcess.sourceView, SourceProcess.send, Payload.ofValue,
        DomainAdapter.embedPayload, operations, event, key]
      rw [key]
      apply Original.Simulation.call
      intro ignored
      have current := ih (suffix ++ [.message origin (.field field value)])
      rw [history_append] at current
      simpa only [history, List.map_cons, List.map_nil, event, key] using current
  | query frames final site field handle origin route key request tail ih =>
      rcases origin with ⟨entry, events, actualRequest⟩
      change actualRequest = some (.draw field) at request
      subst actualRequest
      simp only [fold_call, Original.operations,
        Original.query, mode, route, Original.queryField, ↓reduceDIte,
        PIR.Process.bind, PIR.Process.interpret, Occurrence.erase, CommonAdapter.project,
        SourceProcess.sourceView, SourceProcess.query, operations, key]
      have entryKey := congrArg Origin.entry key
      have eventKey := congrArg Origin.event key
      dsimp only [Origin.withoutCoordinates, Context.query, Origin.query] at entryKey eventKey
      subst entry
      simp only [Origin.withoutCoordinates, eventKey, Context.query, Origin.query,
        Domain.Raw, Request.draw, eq_mpr_eq_cast, cast_eq]
      rw [eventKey]
      apply Original.Simulation.call
      intro reply
      have current := ih reply (suffix ++ [.challenge ⟨routing.context.entry, events, some (.draw field)⟩])
      rw [history_append] at current
      simp only [history, List.map_cons, List.map_nil, event] at current
      rw [key] at current
      exact current

section UniformErasure
variable [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-- The generic erasure law is instantiated before inspecting a large source.
Both equalities are consumed as proofs, rather than by reducing source bodies. -/
theorem scalar_participant (program : Program) (self : Nat)
    (inputs : Values (Component (assignment F G)) program.payload.entry.inputs) :
    ((Occurrence.participant (ringModel F G) program self inputs).interpret Occurrence.erase).interpret
      CommonAdapter.project =
      (program.participant F G self inputs).interpret CommonAdapter.project :=
  congrArg (fun process => process.interpret CommonAdapter.project)
    ((Occurrence.participant_erase (ringModel F G) program self inputs).trans
      (Program.participant_eq_participantOn (F := F) (G := G) program self inputs).symm)
end UniformErasure

end Zkc.Construction.Uniform.OccurrenceSourceProcess
