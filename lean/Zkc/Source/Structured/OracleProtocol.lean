module

public import Zkc.Source.Structured.ProtocolAlgebra
public import Zkc.Source.Structured.ProtocolCalculation
public import Zkc.Source.Structured.OracleExecution
public import Zkc.Source.Structured.OracleProtocolAdmission

@[expose] public section

/-! The Oracle instance of the shared protocol algebra. Source execution remains
`Region.denote`; application and repeat wrappers expose reached structural boundaries to
the state handler. These internal effects are separate from public transcript actions. -/

set_option autoImplicit false
namespace Zkc.Source.Structured

inductive OracleProtocolAction (carriers : Carriers) where
  | ordinary (action : (participantInterfaceOn carriers).Op)
  | oracle (request : OracleRequest carriers)
  | demand (request : OracleDataDemand)
  | application (signature : ProtocolSignature) (site : String)
  | iteration (site : String) (index : Nat)
  | leave
  | mark (sourceSite observedSite : String)

abbrev oracleProtocolInterface (carriers : Carriers) : PIR.Signature where
  Op := OracleProtocolAction carriers
  Reply
    | .ordinary action => (participantInterfaceOn carriers).Reply action
    | .oracle request => (oracleInterface carriers).Reply request
    | .demand request => (oracleDataDemandInterface carriers).Reply request
    | .application .. | .iteration .. | .leave | .mark .. => Unit

namespace OracleProtocol
variable (model : DomainModel)

abbrev Interface := oracleProtocolInterface model.toCarriers

def actions : PIR.OperationInterpretation (participantInterfaceOn model.toCarriers)
    (Interface model) := fun action ↦ .call (.ordinary action) .done

def demand : OracleDataDemandInterpretation model.toCarriers (Interface model) :=
  fun request ↦ .call (.demand request) .done

def enter {A : Type} (action : (Interface model).Op)
    (process : PIR.Process (Interface model) A) : PIR.Process (Interface model) A :=
  (PIR.Process.call action (fun _ ↦ .done ())).bind fun _ ↦
    process.bind fun value ↦ .call .leave (fun _ ↦ .done value)

def owned (self owner : Nat)
    (ordinary : Evaluation.ComponentTablesOn model.toCarriers (Interface model))
    (helper : Helper)
    (args : Values (Component (ProtocolValue model.toCarriers)) helper.inputs) :
    PIR.Process (Interface model) (Values (Component (ProtocolValue model.toCarriers)) helper.outputs) :=
  if owner = self then
    match RoleFamily.sequence args with
    | none => .halt .incomplete
    | some _ =>
      (ProtocolValue.materializeComponents (demand model) self args).bind fun values ↦
        (Participant.owned self owner (invoke ordinary.closed helper) values).bind fun results ↦
          .done (ProtocolValue.embedComponents results)
  else .done (Values.absent _ helper.outputs)

def exchange (context : ProtocolContext) (self sender receiver : Nat) (site : String)
    {type : Ty} (value : Component (ProtocolValue model.toCarriers) type) :
    PIR.Process (Interface model) (Component (ProtocolValue model.toCarriers) type) :=
  let site := qualifyProtocolSite context.applicationPrefix site
  if context.roles sender = self then
    match value with
    | none => .halt .incomplete
    | some value =>
      (value.materializeWith (demand model) self).bind fun concrete ↦
        ((Participant.exchange (services := services) self (context.roles sender)
          (context.roles receiver) site (some concrete)).interpret (actions model)).bind
            (fun result ↦ .done (result.map (ProtocolValue.ofConcrete type)))
  else
    ((Participant.exchange (services := services) self (context.roles sender)
      (context.roles receiver) site (none : Option (model.Value type))).interpret
        (actions model)).bind (fun result ↦ .done (result.map (ProtocolValue.ofConcrete type)))

def algebra (self : Nat)
    (ordinary : Evaluation.ComponentTablesOn model.toCarriers (Interface model))
    (helpers : ProtocolCalculation.Tables model.toCarriers (Interface model)) :
    ProtocolAlgebra (ProtocolValue model.toCarriers) (Interface model) where
  index := ProtocolValue.ofConcrete .index
  count := ProtocolValue.toConcrete
  application := fun _ signature site process ↦ enter model (.application signature site) process
  iteration := fun _ site index process ↦ enter model (.iteration site index) process
  action context _ op args := match op, args with
    | .oracle operation location, args =>
      .call (.oracle ⟨operation, location, self, context.roles, args⟩) .done
    | .calculate op _, args =>
      ProtocolCalculation.operation model (demand model) self ordinary helpers op args
    | .localCall helper _ owner _, args => owned model self (context.roles owner) ordinary helper args
    | .guard owner _, .cons condition .nil =>
      ((Participant.guard (services := services) (Value := model.Value) self
        (context.roles owner) (condition.bind ProtocolValue.toConcrete)).interpret
          (actions model)).bind fun _ ↦ .done .nil
    | .exchange _ sender receiver site, .cons value .nil =>
      (exchange model context self sender receiver site value).bind fun value ↦
        .done (.cons value .nil)
    | .query owner operation site, args =>
      ((Participant.query (services := services) self (context.roles owner)
        (qualifyProtocolSite context.applicationPrefix site) operation
        (ProtocolValue.concreteComponents args)).interpret serviceAction |>.interpret
          (actions model)).bind fun result ↦
            .done (.cons (result.map (ProtocolValue.ofConcrete operation.result)) .nil)
    | .draw owner field site, args =>
      ((Participant.query (services := services) self (context.roles owner)
        (qualifyProtocolSite context.applicationPrefix site) (.draw field)
        (ProtocolValue.concreteComponents args)).interpret (actions model)).bind
          fun result ↦ .done (.cons (result.map (ProtocolValue.ofConcrete (.field field))) .nil)
    | .statement .., _ => .done .nil
    | .mark site, .nil =>
      .call (.mark site (qualifyProtocolSite context.applicationPrefix site)) (fun _ ↦ .done .nil)
    | _, _ => .halt .refused -- structural cases are dispatched by ProtocolAlgebra.operation

structure Frame where
  invocation : InvocationCoordinate
  definition : Nat
  block : List Nat := [7]
  next : Nat := 0
  row : List Nat := []

structure State (snapshot : Snapshot) (domains : List DomainSpec)
    (math : OracleMathEnvironment) (S : Type) where
  oracle : OracleRuntimeState model snapshot domains math S
  frame : Frame
  parents : List Frame := []

inductive Event (E : Type) where
  | logical (event : OracleEvent E)
  | ordinary (event : E)
  | mark (site : String)

def sourceSite (snapshot : Snapshot) (frame : Frame) (site : String) : Except String (List Nat) := do
  let some (.function function) := snapshot.definitions[frame.definition]?
    | throw "oracle-execution-definition"
  let some (_, row) := (function.body.siteRows Limits.nesting [7]).find?
      (fun occurrence ↦ occurrence.1 == site && occurrence.2 == frame.row)
    | throw "oracle-execution-site"
  return row

/-- Canonical lowering retains one mark for every stored instruction, including unnamed
calculations. The checked row advances in the current lexical block only. Entering a
repeat callback selects its actual child block; successful exit restores the caller cursor.
Rendered names and dynamic allocation counts never determine an Oracle anchor. -/
def sourceStep (snapshot : Snapshot) (frame : Frame) (site : String) : Except String Frame := do
  let row := frame.block ++ [1, frame.next]
  let located := {frame with row := row}
  let _ ← sourceSite snapshot located site
  return {located with next := frame.next + 1}

theorem sourceSite_stored {snapshot : Snapshot} {frame : Frame} {site : String}
    {row : List Nat} (located : sourceSite snapshot frame site = .ok row) :
    ∃ function, snapshot.definitions[frame.definition]? = some (.function function) ∧
      (site, row) ∈ function.body.siteRows Limits.nesting [7] ∧ row = frame.row := by
  unfold sourceSite at located
  split at located <;> try contradiction
  rename_i function original
  split at located <;> try contradiction
  rename_i occurrence found
  have same := List.find?_some found
  simp only [Bool.and_eq_true, beq_iff_eq] at same
  obtain ⟨sameSite, sameRow⟩ := same
  have member := List.mem_of_find?_eq_some found
  have output := Except.ok.inj located
  exact ⟨function, original, by simpa [sameSite, output] using member,
    output.symm.trans sameRow⟩

theorem sourceStep_cursor {snapshot : Snapshot} {before after : Frame} {site : String}
    (stepped : sourceStep snapshot before site = .ok after) :
    after.row = before.block ++ [1, before.next] ∧ after.next = before.next + 1 ∧
      after.invocation = before.invocation ∧ after.definition = before.definition := by
  unfold sourceStep at stepped
  cases located : sourceSite snapshot
      {before with row := before.block ++ [1, before.next]} site with
  | error code => simp [located] at stepped
  | ok row =>
    simp only [located, pure, Except.pure] at stepped
    cases stepped
    exact ⟨rfl, rfl, rfl, rfl⟩

def handler {snapshot : Snapshot} {domains : List DomainSpec} {math : OracleMathEnvironment}
    {S E : Type} (oracles : List (CheckedOracle snapshot domains math))
    (ordinary : PIR.Handler (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.Handler (oracleReadInterface model.toCarriers) S E) :
    PIR.Handler (Interface model) (State model snapshot domains math S) (Event E) :=
  fun action state ↦
    let stop := fun {A : Type} ↦
      (⟨.stopped .refused, state, []⟩ : PIR.Execution _ (Event E) A)
    match action with
    | .mark original observed =>
      match sourceStep snapshot state.frame original with
      | .error _ => stop
      | .ok frame => ⟨.returned (), {state with frame := frame}, [.mark observed]⟩
    | .ordinary action =>
      let result := ordinary action state.oracle.provider
      ⟨result.outcome, {state with oracle.provider := result.state}, result.events.map Event.ordinary⟩
    | .oracle request =>
      if request.location.definition != state.frame.definition ||
          request.location.row != state.frame.row then stop
      else
        let location := {request.location with invocation := state.frame.invocation}
        let result := OracleExecution.operation model oracles base location request.self request.roles
          request.operation request.arguments state.oracle
        ⟨result.outcome, {state with oracle := result.state}, result.events.map Event.logical⟩
    | .demand request =>
      let location : OracleLocation :=
        ⟨state.frame.invocation, state.frame.definition, state.frame.row⟩
      let result := OracleStore.demandBase request location state.oracle
      ⟨result.outcome, {state with oracle := result.state}, result.events.map Event.logical⟩
    | .application signature site =>
      match sourceSite snapshot state.frame site with
      | .error _ => stop
      | .ok row =>
        let index := snapshot.definitions.findIdx (·.name == signature.name)
        match snapshot.definitions[index]? with
        | some (.function function) =>
          if resolveProtocolSignature function != .ok signature then stop
          else
            let frame : Frame := {
              invocation := {state.frame.invocation with frames :=
                state.frame.invocation.frames ++ [.application state.frame.definition row]}
              definition := index }
            ⟨.returned (), {state with frame := frame, parents := state.frame :: state.parents}, []⟩
        | _ => stop
    | .iteration site index =>
      match sourceSite snapshot state.frame site with
      | .error _ => stop
      | .ok row =>
        let frame : Frame := {state.frame with
          invocation.frames :=
            state.frame.invocation.frames ++ [.iteration state.frame.definition row index]
          block := row ++ [4, 0, 3]
          next := 0
          row := []}
        ⟨.returned (), {state with frame := frame, parents := state.frame :: state.parents}, []⟩
    | .leave => match state.parents with
      | [] => stop
      | parent :: parents => ⟨.returned (), {state with frame := parent, parents := parents}, []⟩

end OracleProtocol

def UnitPayload.oracleCalculations (payload : UnitPayload) (model : DomainModel) (self : Nat) :
    ProtocolCalculation.Tables model.toCarriers (OracleProtocol.Interface model) :=
  let ordinary := payload.definitions.foldl
    (Evaluation.ComponentTablesOn.extend model (.silent _)) ⟨[], []⟩
  payload.definitions.foldl
    (ProtocolCalculation.extend model (OracleProtocol.demand model) self ordinary) []

def UnitPayload.oracleProtocolTable (payload : UnitPayload) (model : DomainModel) (self : Nat) :
    ProtocolTable (ProtocolValue model.toCarriers) (OracleProtocol.Interface model) :=
  let ordinary := payload.definitions.foldl
    (Evaluation.ComponentTablesOn.extend model (.silent _)) ⟨[], []⟩
  payload.protocols.foldl
    (ProtocolAlgebra.extend (OracleProtocol.algebra model self ordinary
      (payload.oracleCalculations model self))) []

/-- Execute the same checked root and exact captured protocol prefixes on lazy values.
Oracle effects are interpreted only by the checked-unit runtime, below. -/
def Program.oracleParticipant (program : Program) (model : DomainModel) (self : Nat)
    (inputs : Values (Component (ProtocolValue model.toCarriers)) program.payload.entry.inputs) :
    PIR.Process (OracleProtocol.Interface model)
      (Values (Component (ProtocolValue model.toCarriers)) program.payload.entry.outputs) :=
  invokeProtocol (program.payload.oracleProtocolTable model self)
    program.payload.entry.signature {} self inputs

end Zkc.Source.Structured
