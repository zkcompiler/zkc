module

public import Zkc.Frontend.Typed.Checked
public import Zkc.Frontend.Emit.Named

@[expose] public section

set_option autoImplicit false

/-!
# The emission of a protocol body to the named program

A checked protocol body is the tree of its statements and the tables of the passes: who holds
each name, who computes each statement, who takes part in each choice and loop, who sends. The
emitter walks the statements once. It types nothing and decides nothing about roles: what a
role does is what the tables say.

- **A statement that computes** (a binding, a level of a pattern, an update, a guard) is one
  `compute` of the roles that compute it, with the instructions of its expression as local
  code emits them. A name it binds is held by those roles.
- **A send** is the payload computed by the sender, an `exchange` per receiver in the order
  written, each at the site of its part, and the binder is the `join` of the sender's copy and
  the receivers' copies. **A draw** and **a sample** are their events.
- **An application**: each argument is computed by the mapped holders of its port, in the
  order written; the results are the callee's, one name each.
- **`if` and `match`** are a `choose` of the participants on the condition or on the matched
  value, which the participants compute; the outputs are the `mut` names that the arms update,
  each with its holders. A condition is not taken one operand at a time here: the arms have
  events.
- **A uniform loop** is a `repeat` of the participants, who compute its domain; the carried
  values are the updated `mut` names. **A loop in sequence** is a block per iteration, with
  the key of its program point; the block returns the `mut` names from outside that the
  iteration updates and the values it collects. **A loop of no iteration** is nothing, and a
  name it collects is the collection of no elements.
- **A result** is computed by the holders that the head gives it.
-/

namespace Zkc.Frontend.Emit.Named

open Syntax
open Static
open Zkc.Core.Named (ValueName Tag Instruction LocalOp Exit Count ProtocolInstruction ProtocolOp Output)
open Typing (EmitM EmitFailure toTy variantNumber rowNumberOf)

/-- What the emission of a protocol body reads beside the tree. -/
structure ProtocolContext where
  roster : Array String
  /-- The tables of the placement pass. -/
  roles : Typed.Roles
  /-- The occurrences of the events of the body. -/
  occurrences : Array Typed.Occurrence
  /-- The events of the text, by their numbers (EV3): the name of each. -/
  events : Array SourceEvent
  /-- The places of the loops of the text, in its order: the number of a loop is its place in
  this list. -/
  loops : Array Span
  /-- The number of a protocol instance in the package, with its ports and results as the
  package has them. -/
  callee : InstanceId → EmitM (Nat × Zkc.Core.Named.Protocol)

def pushStep (instruction : ProtocolInstruction) : NamedM Unit :=
  modify fun state =>
    { state with steps := state.steps.modify (state.steps.size - 1) (·.push instruction) }

/-- Emits an operation of a protocol body with `count` results. -/
def emitStep (tag : Tag) (step : ProtocolOp) (count : Nat) : NamedM (List ValueName) := do
  let results ← (List.range count).mapM fun _ => fresh
  pushStep (.mk tag results step)
  return results

/-- The local code of an action as one `compute` of roles. When no role computes, nothing is
emitted: the names it binds are read by nobody. -/
def computeAt {α : Type} (tag : Tag) (roles : List Nat) (action : NamedM α) : NamedM α := do
  modify fun state => { state with frames := state.frames.push #[] }
  let result ← action
  let state ← get
  let steps := state.frames.back!
  set { state with frames := state.frames.pop }
  unless steps.isEmpty || roles.isEmpty do pushStep (.mk tag [] (.compute roles steps.toList))
  return result

/-- Builds a region of a protocol body with its own inputs: `action` emits its instructions and
gives the names it returns. A name bound in the region does not leave it. -/
def inProtocolRegion (inputs : List ValueName) (action : NamedM (List ValueName)) :
    NamedM Zkc.Core.Named.ProtocolRegion := do
  let saved := (← get).names
  let types := (← get).types
  modify fun state => { state with steps := state.steps.push #[] }
  let returned ← action
  let state ← get
  let instructions := state.steps.back!
  set { state with steps := state.steps.pop, names := saved, types }
  return .mk inputs instructions.toList (.ret returned)

namespace ProtocolContext

def computing (context : ProtocolContext) (node : Typed.NodeId) : List Nat :=
  ((context.roles.computing[node]?).getD RoleSet.empty).toArray.toList

def participants (context : ProtocolContext) (node : Typed.NodeId) : List Nat :=
  ((context.roles.participants[node]?).getD RoleSet.empty).toArray.toList

def holders (context : ProtocolContext) (binder : LocalId) : List Nat :=
  ((context.roles.holders[binder]?).getD (RoleSet.all context.roster.size)).toArray.toList

/-- The site of a part of an event at its occurrence: its key, and its name. -/
def site (context : ProtocolContext) (node : Typed.NodeId) (event : Nat) (part : String) :
    Zkc.Core.Named.Site :=
  let iteration := ((context.occurrences.find? (·.node == node)).map (·.iteration.toList)).getD []
  let name := ((context.events[event]?).bind (·.name)).getD s!"site{event}"
  { key := { event, part, iteration }
    name := if iteration.isEmpty then name
            else s!"{name}.{".".intercalate (iteration.map toString)}" }

/-- The number of a loop of the text. A loop in sequence of a protocol body is a loop that the
source writes: one that is not among the written loops is a defect of the frontend, since two
of them would share the key of their program points. -/
def loopNumber (context : ProtocolContext) (span : Span) : Except EmitFailure Nat :=
  match context.loops.findIdx? fun place =>
      place.file == span.file && place.startByte == span.startByte with
  | some number => .ok number
  | none => .error (.defect "a loop in sequence that is no loop of the text")

end ProtocolContext

/-- The outputs of a choice, a loop or a block for the `mut` names it updates: each at its type
with its holders. -/
def updateOutputs (context : ProtocolContext) (updates : Array LocalId) (types : Array ClosedType) :
    NamedM (List Output) :=
  (updates.zip types).toList.mapM fun (binder, type) => do
    return { type := ← ty type, holders := context.holders binder }

mutual
  partial def emitProtocolStmts (context : ProtocolContext) (iteration : List Nat)
      (statements : Array Typed.Stmt) : NamedM Unit := do
    for statement in statements do emitProtocolStmt context iteration statement

  /-- Emits a statement of a protocol body. `iteration` is the iteration of each loop in
  sequence around it. -/
  partial def emitProtocolStmt (context : ProtocolContext) (iteration : List Nat) :
      Typed.Stmt → NamedM Unit
    | statement@(.bind mark ..) | statement@(.unpack mark ..) | statement@(.update mark ..)
    | statement@(.guard mark ..) =>
      computeAt mark.id (context.computing mark.id) (emitStmt statement)
    | .scope _ body => emitProtocolStmts context iteration body
    | .«if» mark condition onTrue onFalse control => do
      let participants := context.participants mark.id
      let subject ← computeAt mark.id participants (emitExpr condition)
      let outputs ← updateOutputs context control.updates control.carried
      let arm (statements : Array Typed.Stmt) : NamedM Zkc.Core.Named.ProtocolRegion :=
        inProtocolRegion [] do
          emitProtocolStmts context iteration statements
          control.updates.toList.mapM currentOf
      let whenTrue ← arm onTrue
      let whenFalse ← arm onFalse
      let results ← emitStep mark.id (.choose participants subject .condition outputs [whenTrue, whenFalse])
        control.updates.size
      rebind control results
    | .«match» mark scrutinee binder inst cases control => do
      let participants := context.participants mark.id
      let subject ← computeAt mark.id participants (emitExpr scrutinee)
      if let some binder := binder then bind binder.id (.value subject)
      let alternatives ← match (← readThe Compile.State).table.content? inst with
        | some (.«variant» alternatives) => pure alternatives
        | _ => defect "a match on a variant whose alternatives are not evaluated"
      let outputs ← updateOutputs context control.updates control.carried
      let mut regions := #[]
      for index in [0:alternatives.size] do
        let some (.«case» _ _ payload body) := cases.find? fun (.«case» _ covered _ _) => covered.contains index
          | defect "an alternative that no case covers"
        let payloadTypes := alternatives[index]!.2
        let input ← fresh
        let region ← inProtocolRegion [input] do
          -- the payload is held by every participant, who takes its parts
          computeAt mark.id participants do
            for position in [0:payload.size] do
              let some binder := payload[position]! | continue
              let item ← if payloadTypes.size == 1 then pure input
                else builtin mark.id (.tupleGet (← tys payloadTypes) position) [input]
              bind binder.id (.value item)
          emitProtocolStmts context iteration body
          control.updates.toList.mapM currentOf
        regions := regions.push region
      let results ← emitStep mark.id
        (.choose participants subject (.alternative (← (variantNumber inst : EmitM Nat)) []) outputs
          regions.toList) control.updates.size
      rebind control results
    | .«for» mark loop control => emitProtocolFor context iteration mark loop control
    | .event mark event what => emitEvent context mark event what
    | .error .. => defect "a body with an error node is emitted"

  /-- A loop of a protocol body. -/
  partial def emitProtocolFor (context : ProtocolContext) (iteration : List Nat) (mark : Typed.Mark)
      (loop : Typed.Loop) (control : Typed.Control) : NamedM Unit := do
    let .loop index domain collected body := loop
    let tag := mark.id
    let participants := context.participants tag
    let iterations ← match body with
      | .uniform statements values =>
        let prepared ← computeAt tag participants (emitDomain tag domain)
        let carried ← control.updates.toList.mapM fun binder => do
          return (← currentOf binder, context.holders binder)
        let gathered ← (values.zip collected).toList.mapM fun (value, binder) => do
          return ({ type := ← ty value.type, holders := context.holders binder.id } : Output)
        let number ← fresh
        let inputs ← control.updates.toList.mapM fun _ => fresh
        let region ← inProtocolRegion (number :: inputs) do
          rebind control inputs
          computeAt tag participants (bindLoopItem tag prepared domain index number none)
          emitProtocolStmts context iteration statements
          let mut returned := #[]
          for value in values do
            returned := returned.push
              (← computeAt value.info.id (context.computing value.info.id) (emitExpr value))
          return returned.toList ++ (← control.updates.toList.mapM currentOf)
        let results ← emitStep tag (.«repeat» participants prepared.count carried gathered region)
          (values.size + control.updates.size)
        for (binder, value) in collected.toList.zip results do bind binder.id (.value value)
        rebind control (results.drop values.size)
        return
      | .stepped iterations => pure iterations
      -- of a loop of no iteration nothing is emitted
      | .empty .. => pure #[]
    if iterations.isEmpty then
      -- the collection is evaluated once all the same, by the roles that placement names
      -- when its evaluation can stop
      if let .collection source _ _ := domain then
        discard <| computeAt source.info.id (context.computing source.info.id) (emitExpr source)
      for binder in collected do
        let .seq element _ := binder.type | defect "a collected name that is no collection"
        let value ← computeAt tag (context.holders binder.id)
          (do builtin tag (.seqMake (← ty element) 0) [])
        bind binder.id (.value value)
      return
    -- a loop in sequence: its domain once, then a block per iteration
    let prepared ← computeAt tag participants (emitDomain tag domain)
    let number ← match context.loopNumber mark.span with
      | .ok number => pure number
      | .error failure => throw failure
    let mut gathered : Array (Array (ValueName × ClosedType)) := collected.map fun _ => #[]
    for (.iteration k statements values) in iterations do
      -- the `mut` names from outside that this iteration updates
      let inner := Typed.updatedIn statements
      let updated := control.updates.filter inner.contains
      -- the block: its instructions, the names it returns, and the type of each at its end
      let saved := (← get).names
      let before := (← get).types
      modify fun state => { state with steps := state.steps.push #[] }
      computeAt tag participants do
        let position ← match domain with
          | .collection .. => literal tag (.nat k)
          | .range .. => pure 0
        bindLoopItem tag prepared domain index position (some k)
      emitProtocolStmts context (iteration ++ [k]) statements
      let mut values' : Array (ValueName × ClosedType × List Nat) := #[]
      for value in values do
        let computing := context.computing value.info.id
        values' := values'.push (← computeAt value.info.id computing (emitExpr value), value.type, computing)
      let finals ← updated.toList.mapM currentOf
      let state ← get
      let types := updated.map fun binder => (state.types[binder]?).getD ClosedType.nat
      let instructions := state.steps.back!
      set { state with steps := state.steps.pop, names := saved, types := before }
      let outputs := (← updateOutputs context updated types) ++
        (← values'.toList.mapM fun (_, type, computing) => do
          return ({ type := ← ty type, holders := computing } : Output))
      let region : Zkc.Core.Named.ProtocolRegion :=
        .mk [] instructions.toList (.ret (finals ++ values'.toList.map (·.1)))
      let results ← emitStep tag (.block { loop := number, iteration := iteration ++ [k] } outputs region)
        outputs.length
      rebind { updates := updated, carried := types } (results.take updated.size)
      gathered := (gathered.zip ((results.drop updated.size).toArray.zip (values'.map (·.2.1)))).map
        fun (all, value) => all.push value
    for (binder, values) in collected.zip gathered do
      let names := values.toList.map (·.1)
      let value ← computeAt tag (context.holders binder.id) do
        match binder.type with
        | .seq element (some count) => builtin tag (.seqMake (← ty element) count) names
        | _ => builtin tag (.tupleMake (← tys (values.map (·.2)))) names
      bind binder.id (.value value)

  /-- An event of a protocol body. -/
  partial def emitEvent (context : ProtocolContext) (mark : Typed.Mark) (event : Nat) :
      Typed.Event → NamedM Unit
    | .send binder payload _ receivers => do
      let some sender := context.roles.senders[mark.id]?
        | defect "a send whose sender the placement pass did not find"
      let value ← computeAt payload.info.id [sender] (emitExpr payload)
      let mut copies := #[(value, sender)]
      for receiver in receivers do
        let part := if receivers.size ≤ 1 then "value"
          else s!"to {(context.roster[receiver]?).getD "?"}"
        let received ← emitStep mark.id
          (.exchange sender receiver (context.site mark.id event part) value) 1
        if let [name] := received then copies := copies.push (name, receiver)
      if let some binder := binder then
        -- the sender's copy and the receivers' copies are one name
        let joined ← emitStep mark.id (.join copies.toList) 1
        if let [name] := joined then bind binder.id (.value name)
    | .draw binder law owner receivers => do
      let some row := Typing.rowOf? law.request
        | throw (EmitFailure.waiting s!"the law `{law.name}`, which the vocabulary does not have")
      let drawn ← emitStep mark.id
        (.draw owner receivers.toList (context.site mark.id event "value") (← (rowNumberOf row : EmitM Nat)) []) 1
      if let (some binder, [name]) := (binder, drawn) then bind binder.id (.value name)
    | .sample binder law owner => do
      let some row := Typing.rowOf? law.request
        | throw (EmitFailure.waiting s!"the law `{law.name}`, which the vocabulary does not have")
      let sampled ← emitStep mark.id
        (.sample owner (context.site mark.id event "value") (← (rowNumberOf row : EmitM Nat)) []) 1
      if let (some binder, [name]) := (binder, sampled) then bind binder.id (.value name)
    | .attempt .. => throw (EmitFailure.waiting "an `attempt` (a later layer)")
    | .apply results callee arguments _ roleMap order => do
      let (number, protocol) ← (context.callee callee : EmitM (Nat × Zkc.Core.Named.Protocol))
      -- each argument at the mapped holders of its port, in the order written
      let mut operands : Array ValueName := arguments.map fun _ => 0
      for position in order do
        let some argument := arguments[position]? | defect "an argument without its port"
        let value ← computeAt argument.info.id (context.computing argument.info.id) (emitExpr argument)
        operands := operands.set! position value
      let given ← emitStep mark.id
        (.apply number roleMap.toList (context.site mark.id event "value") operands.toList)
        protocol.outputs.length
      for (binder, name) in results.toList.zip given do
        if let some binder := binder then bind binder.id (.value name)
end

/-- A protocol instance as a protocol of the named program: its ports that are not `spec`,
each once with its holders; its body; its results, each computed by its holders. -/
def emitProtocol (context : Context) (protocol : ProtocolContext) (specificationOnly : Bool)
    (body : Typed.ProtocolBody) : EmitM Zkc.Core.Named.Protocol := do
  let action : NamedM Zkc.Core.Named.Protocol := do
    let mut inputs := #[]
    let mut ports := #[]
    for port in body.ports do
      if port.specification then continue
      let name ← fresh
      bind port.binder.id (.value name)
      inputs := inputs.push name
      ports := ports.push ({ type := ← ty port.binder.type, holders := port.holders.toArray.toList } : Output)
    emitProtocolStmts protocol [] body.statements
    let mut returned := #[]
    let mut outputs := #[]
    for result in body.results do
      let holders := result.holders.toArray.toList
      returned := returned.push (← computeAt result.value.info.id holders (emitExpr result.value))
      outputs := outputs.push ({ type := ← ty result.value.type, holders } : Output)
    let instructions := ((← get).steps[0]?).getD #[]
    return { specificationOnly, roles := body.roster.size, inputs := ports.toList
             outputs := outputs.toList
             body := .mk inputs.toList instructions.toList (.ret returned.toList) }
  (action.run context).run' {}

end Zkc.Frontend.Emit.Named
