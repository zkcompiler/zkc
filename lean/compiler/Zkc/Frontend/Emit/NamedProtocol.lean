module

public import Zkc.Frontend.Typed.Checked
public import Zkc.Frontend.Emit.Named

@[expose] public section

set_option autoImplicit false

/-!
# The emission of a protocol body to the named program

Placement computes the holders of source values and the participants of control. The
emitter reads its tables and preserves the source evaluation order, including the written
order of call arguments. A message is one flow to all its recipients. The core assigns the
sender and receiver actions at each role projection. Local computations inside a protocol
use the same region and operation emitter as functions.
-/

namespace Zkc.Frontend.Emit.Named

open Syntax Static
open Typing (EmitM EmitFailure toTy)

abbrev ProtocolInstruction (b : Bindings) := Core.Instruction (Core.ProtocolRaw b.vocabulary) (List Core.Role)
abbrev ProtocolRegion (b : Bindings) := Core.Region (Core.ProtocolRaw b.vocabulary) (List Core.Role)

structure ProtocolContext where
  roles : Typed.Roles
  roster : Array String

variable {b : Bindings}

mutual
  /-- Place local operations and their nested control at the computing roles. -/
  def placeInstruction (who : List Core.Role) :
      Core.Instruction (Core.LocalRaw b.vocabulary) Unit → ProtocolInstruction b
    | .op key results op args => .op key results (.compute who op) args
    | .guard key _ test why => .guard key who test why
    | .choose key _ test rs yes no => .choose key who test rs (placeRegion who yes) (placeRegion who no)
    | .cases key _ value rs arms => .cases key who value rs (placeArms who arms)
    | .loop key _ count starts rs body => .loop key who count starts rs (placeRegion who body)
    | .block key ordinal rs body => .block key ordinal rs (placeRegion who body)
    | .attempt key _ rs body => .attempt key who rs (placeRegion who body)
  def placeRegion (who : List Core.Role) : LocalRegion b → ProtocolRegion b
    | .mk inputs steps results => .mk inputs (placeSteps who steps) results
  def placeArms (who : List Core.Role) : List (LocalRegion b) → List (ProtocolRegion b)
    | [] => []
    | arm :: arms => placeRegion who arm :: placeArms who arms
  def placeSteps (who : List Core.Role) :
      List (Core.Instruction (Core.LocalRaw b.vocabulary) Unit) → List (ProtocolInstruction b)
    | [] => []
    | step :: rest => placeInstruction who step :: placeSteps who rest
end

def pushStep (instruction : ProtocolInstruction b) : NamedM b Unit :=
  modify fun state => { state with steps := state.steps.modify (state.steps.size - 1) (·.push instruction) }

def emitStepAt (tag : Tag) (step : Core.Key → List ValueName → ProtocolInstruction b) (count : Nat) :
    NamedM b (Core.Key × List ValueName) := do
  let results ← (List.range count).mapM fun _ => fresh
  let key ← freshKey tag
  pushStep (step key results)
  return (key, results)

def emitStep (tag : Tag) (step : Core.Key → List ValueName → ProtocolInstruction b) (count : Nat) :
    NamedM b (List ValueName) := do
  return (← emitStepAt tag step count).2

def protocolOp (tag : Tag) (op : Core.ProtocolRaw b.vocabulary) (args : List ValueName) :
    NamedM b ValueName := do
  let [result] ← emitStep tag (fun key rs => .op key rs op args) 1 | defect "expected one result"
  return result

def computeAt {α : Type} (roles : List Nat) (action : NamedM b α) : NamedM b α := do
  modify fun state => { state with frames := state.frames.push #[] }
  let result ← action
  let state ← get
  let steps := state.frames.back!
  set { state with frames := state.frames.pop }
  unless roles.isEmpty do
    for step in steps do pushStep (placeInstruction roles step)
  return result

def locatedExpr (roles : List Core.Role) (expr : Typed.Expr) : NamedM b ValueName := do
  let value ← computeAt roles (emitExpr expr)
  protocolOp expr.info.id (.narrow roles) [value]

/-- Builds a region of a protocol body with its own inputs: `action` emits its instructions and
gives the names it returns. A name bound in the region does not leave it. -/
def inProtocolRegion (inputs : List ValueName) (action : NamedM b (List ValueName)) :
    NamedM b (ProtocolRegion b) := do
  let saved := (← get).names
  let types := (← get).types
  modify fun state => { state with steps := state.steps.push #[] }
  let returned ← action
  let state ← get
  let instructions := state.steps.back!
  set { state with steps := state.steps.pop, names := saved, types }
  return .mk inputs instructions.toList returned

namespace ProtocolContext

def computing (context : ProtocolContext) (node : Typed.NodeId) : List Nat :=
  ((context.roles.computing[node]?).getD RoleSet.empty).toArray.toList

def participants (context : ProtocolContext) (node : Typed.NodeId) : List Nat :=
  ((context.roles.participants[node]?).getD RoleSet.empty).toArray.toList

def holders (context : ProtocolContext) (binder : LocalId) : List Nat :=
  ((context.roles.holders[binder]?).getD (RoleSet.all context.roster.size)).toArray.toList

end ProtocolContext

def exitUpdates (context : ProtocolContext) (tag : Tag) (updates : Array LocalId) : NamedM b (List ValueName) :=
  updates.toList.mapM fun id => do protocolOp tag (.narrow (context.holders id)) [← currentOf id]

mutual
  partial def emitProtocolStmts (context : ProtocolContext)
      (statements : Array Typed.Stmt) : NamedM b Unit := do
    for statement in statements do emitProtocolStmt context statement

  /-- Emit a statement with the roles computed by placement. -/
  partial def emitProtocolStmt (context : ProtocolContext) :
      Typed.Stmt → NamedM b Unit
    | statement@(.bind mark ..) | statement@(.unpack mark ..) | statement@(.update mark ..)
    | statement@(.guard mark ..) =>
      computeAt (context.computing mark.id) (emitStmt statement)
    | .scope _ body => emitProtocolStmts context body
    | .«if» mark condition onTrue onFalse control => do
      let participants := context.participants mark.id
      let subject ← computeAt participants (emitExpr condition)
      let arm (statements : Array Typed.Stmt) : NamedM b (ProtocolRegion b) :=
        inProtocolRegion [] do
          emitProtocolStmts context statements
          exitUpdates context mark.id control.updates
      let whenTrue ← arm onTrue
      let whenFalse ← arm onFalse
      let results ← emitStep mark.id (fun key rs => .choose key participants subject rs whenTrue whenFalse)
        control.updates.size
      rebind control results
    | .«match» mark scrutinee binder inst cases control => do
      let participants := context.participants mark.id
      let subject ← computeAt participants (emitExpr scrutinee)
      if let some binder := binder then bind binder.id (.value subject)
      let alternatives ← match (← readThe Compile.State).table.content? inst with
        | some (.«variant» alternatives) => pure alternatives
        | _ => defect "a match on a variant whose alternatives are not evaluated"
      let mut regions := #[]
      for index in [0:alternatives.size] do
        let some (.«case» _ _ payload body) := cases.find? fun (.«case» _ covered _ _) => covered.contains index
          | defect "an alternative that no case covers"
        let payloadTypes := alternatives[index]!.2
        let input ← fresh
        let region ← inProtocolRegion [input] do
          -- the payload is held by every participant, who takes its parts
          computeAt participants do
            if payloadTypes.size == 1 then
              if let some (some binder) := payload[0]? then bind binder.id (.value input)
            else unpackParts mark.id payload input (payloadType payloadTypes)
          emitProtocolStmts context body
          exitUpdates context mark.id control.updates
        regions := regions.push region
      let results ← emitStep mark.id
        (fun key rs => .cases key participants subject rs regions.toList) control.updates.size
      rebind control results
    | .«for» mark loop control => emitProtocolFor context mark loop control
    | .event mark _ what => emitEvent context mark what
    | .error .. => defect "a body with an error node is emitted"

  /-- A loop of a protocol body. -/
  partial def emitProtocolFor (context : ProtocolContext) (mark : Typed.Mark)
      (loop : Typed.Loop) (control : Typed.Control) : NamedM b Unit := do
    let .loop index domain collected body := loop
    let tag := mark.id
    let participants := context.participants tag
    let iterations ← match body with
      | .uniform statements values =>
        let prepared ← computeAt participants (emitDomain tag domain)
        let carried ← exitUpdates context tag control.updates
        let number ← fresh
        let inputs ← control.updates.toList.mapM fun _ => fresh
        let region ← inProtocolRegion (number :: inputs) do
          rebind control inputs
          computeAt participants (bindLoopItem tag prepared domain index number none)
          emitProtocolStmts context statements
          let mut returned := #[]
          for value in values do
            returned := returned.push
              (← locatedExpr (context.computing value.info.id) value)
          return (← exitUpdates context tag control.updates) ++ returned.toList
        let (key, results) ← emitStepAt tag (fun key rs => .loop key participants prepared.count carried rs region)
          (values.size + control.updates.size)
        if prepared.count matches .count _ then
          modify fun s => { s with dynamicLoops := s.dynamicLoops.push (key, participants) }
        for (binder, value) in collected.toList.zip (results.drop control.updates.size) do bind binder.id (.value value)
        rebind control (results.take control.updates.size)
        return
      | .stepped iterations => pure iterations
      -- of a loop of no iteration nothing is emitted
      | .empty .. => pure #[]
    if iterations.isEmpty then
      -- the collection is evaluated once all the same, by the roles that placement names
      -- when its evaluation can stop
      if let .collection source _ _ := domain then
        discard <| computeAt (context.computing source.info.id) (emitDomain tag domain)
      for binder in collected do
        let .seq element _ := binder.type | defect "a collected name that is no collection"
        let value ← computeAt (context.holders binder.id)
          (do builtin tag .make [.seq (← ty element) (some 0)] [] [])
        bind binder.id (.value value)
      return
    -- a loop in sequence: its domain once, then a block per iteration
    let prepared ← computeAt participants (emitDomain tag domain)
    let mut gathered : Array (Array (ValueName × ClosedType)) := collected.map fun _ => #[]
    for (.iteration k statements values) in iterations do
      -- the `mut` names from outside that this iteration updates
      let inner := Typed.updatedIn statements
      let updated := control.updates.filter inner.contains
      -- the block: its instructions, the names it returns, and the type of each at its end
      let saved := (← get).names
      let before := (← get).types
      modify fun state => { state with steps := state.steps.push #[] }
      computeAt participants do
        let position ← match domain with
          | .collection .. => literal tag .nat (.nat k)
          | .range .. => pure 0
        bindLoopItem tag prepared domain index position (some k)
      emitProtocolStmts context statements
      let mut values' : Array (ValueName × ClosedType × List Nat) := #[]
      for value in values do
        let computing := context.computing value.info.id
        values' := values'.push (← locatedExpr computing value, value.type, computing)
      let finals ← exitUpdates context tag updated
      let state ← get
      let types := updated.map fun binder => (state.types[binder]?).getD ClosedType.nat
      let instructions := state.steps.back!
      set { state with steps := state.steps.pop, names := saved, types := before }
      let region : ProtocolRegion b := .mk [] instructions.toList (finals ++ values'.toList.map (·.1))
      let results ← emitStep tag (fun key rs => .block key k rs region) (updated.size + values'.size)
      rebind { updates := updated, carried := types } (results.take updated.size)
      gathered := (gathered.zip ((results.drop updated.size).toArray.zip (values'.map (·.2.1)))).map
        fun (all, value) => all.push value
    for (binder, values) in collected.zip gathered do
      let names := values.toList.map (·.1)
      let value ← computeAt (context.holders binder.id) do
        match binder.type with
        | .seq element (some count) => builtin tag .make [.seq (← ty element) (some count)] [] names
        | _ => builtin tag .make [← tupleTy (values.map (·.2))] [] names
      bind binder.id (.value value)

  /-- Emit an event and bind its results. -/
  partial def emitEvent (context : ProtocolContext) (mark : Typed.Mark) :
      Typed.Event → NamedM b Unit
    | .send binder payload _ receivers => do
      let some sender := context.roles.senders[mark.id]?
        | defect "a send whose sender the placement pass did not find"
      let value ← computeAt [sender] (emitExpr payload)
      let result ← protocolOp mark.id (.event (.flow .message sender receivers.toList) (← ty payload.type)) [value]
      if let some name := binder then bind name.id (.value result)
    | .draw binder law owner receivers => emitCoin mark.id binder law owner receivers.toList
    | .sample binder law owner => emitCoin mark.id binder law owner []
    | .attempt .. => throw (EmitFailure.waiting "an `attempt` (a later layer)")
    | .apply results callee arguments specification roleMap order proofArguments => do
      -- each argument at the mapped holders of its port, in the order written
      let mut operands : Array ValueName := arguments.map fun _ => 0
      for position in order do
        let some argument := arguments[position]? | defect "an argument without its port"
        let value ← computeAt (context.computing argument.info.id) (emitExpr argument)
        operands := operands.set! position value
      let (site, given) ← emitStepAt mark.id
        (fun key rs => .op key rs (.apply ⟨callee⟩ roleMap.toList) operands.toList) results.size
      modify fun state => { state with
        specification := state.specification.push ⟨site, callee, specification, proofArguments⟩ }
      for (binder, name) in results.toList.zip given do
        if let some binder := binder then bind binder.id (.value name)

  partial def emitCoin (tag : Tag) (binder : Option Typed.Binder) (law : Typed.RowRef)
      (owner : Core.Role) (others : List Core.Role) : NamedM b Unit := do
    let some row := Typing.rowOf? law.request | throw (EmitFailure.waiting s!"unknown law {law.name}")
    let (.sampling, #[out]) := (row.kind, row.outputs) | defect "expected a sampling law with one result"
    let some t := StandardNames.typeOf? out | throw (EmitFailure.waiting "a law on a project type")
    unless law.name == "law.uniform" do throw (EmitFailure.waiting s!"unresolved law {law.name}")
    let result ← protocolOp tag (.event (.given (.coin (.uniform t)) owner others) (← ty out)) []
    if let some name := binder then bind name.id (.value result)
end

structure ProtocolEmission (b : Bindings) where
  definition : Core.Definition b.vocabulary
  sourceNodes : Array Tag
  specification : Array ApplicationArguments
  dynamicLoops : Array (Core.Key × List Core.Role)

/-- A protocol instance as a protocol of the named program: its ports that are not `spec`,
each once with its holders; its body; its results, each computed by its holders. -/
def emitProtocol (context : Context b) (protocol : ProtocolContext) (key : Core.Key)
    (body : Typed.ProtocolBody) : EmitM (ProtocolEmission b) := do
  let action : NamedM b (Core.Definition b.vocabulary) := do
    let mut inputs := #[]
    let mut ports := #[]
    for port in body.ports do
      if port.specification then continue
      let name ← fresh
      bind port.binder.id (.value name)
      inputs := inputs.push name
      ports := ports.push (⟨← ty port.binder.type, port.holders.toArray.toList⟩ : Core.LTy b.vocabulary)
    emitProtocolStmts protocol body.statements
    let mut returned := #[]
    let mut outputs := #[]
    for result in body.results do
      let holders := result.holders.toArray.toList
      returned := returned.push (← locatedExpr holders result.value)
      outputs := outputs.push (⟨← ty result.value.type, holders⟩ : Core.LTy b.vocabulary)
    let steps := ((← get).steps[0]?).getD #[]
    return .protocol key body.roster.size ports.toList outputs.toList (.mk inputs.toList steps.toList returned.toList)
  let (definition, state) ← (action.run context).run {}
  return ⟨definition, state.sourceNodes, state.specification, state.dynamicLoops⟩

end Zkc.Frontend.Emit.Named
