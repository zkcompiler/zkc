import Zkc.Tools.Frontend.Differential
import Zkc.Tools.Frontend.Trees

/-!
# The second reading of a typed tree

An evaluation of the typed tree of a protocol instance that returns what each role shows: what
it sent, received, heard, drew and sampled, each under the key of the event in the source, and
how it ended. It is in the form that the comparison of runs compares
(`Zkc.Core.RunComparison.Shown`), so that a tree is compared with the run of a package emitted
for the same instance, under the same provider, seed and inputs.

The reading follows the tree and its tables and nothing else of the frontend:

- a role has its own value of every name it holds, and is running, stopped with a reason, or
  waiting for a message that no role sends;
- a statement is evaluated by each of the roles that the placement pass says compute it, on
  that role's values; a statement inside an expression is local code of the role that
  evaluates the expression;
- an event moves a value between roles and records it under its key, composed along the
  applications through which its definition was reached;
- a choice and a loop are followed by each participant on its own copy of what decides it.

The operations of the core are computed here, on data. The rows of the vocabulary, the literals
of its types, and the coins are the provider's, asked through the tables of the package that
the reading is compared with: a row and a type of the tree are found in the package's catalogue
by their names and static arguments.
-/

set_option autoImplicit false

namespace Zkc.Tools.Frontend.Reading

open Zkc.Frontend
open Zkc.Core (Ty Static CatalogueRow Operation)
open Zkc.Core.Concrete (Datum)
open Zkc.Core.Execute (Outcome)

/-- What the provider answers, on data. -/
structure World where
  /-- A row of the package, by its number: its outputs, or none where it has no value. -/
  apply : Nat → List Datum → Option (List Datum)
  /-- A literal of a nominal type of the package, by the number of the type. -/
  literal : Nat → List Nat → Datum
  /-- The coin of a key at a count and a type. -/
  coin : List Nat → Nat → Ty → Option Datum

/-- The catalogue of a package: its nominal types and its rows, by which the names of the tree
are found. -/
structure Dictionary where
  types : Array CatalogueRow
  operations : Array Operation

namespace Dictionary

mutual
  /-- The core type of a closed type that has no record and no variant. -/
  partial def tyOf (dictionary : Dictionary) : ClosedType → Option Ty
    | .bool => some .bool
    | .nat => some .nat
    | .index bound => some (.fin bound)
    | .nonzero field => do
      let inner ← dictionary.tyOf field
      dictionary.nominal "nonzero" [.type inner]
    | .nominal row arguments => do
      dictionary.nominal row (← arguments.toList.mapM dictionary.staticOf)
    | .seq element size => do return .seq (← dictionary.tyOf element) size
    | .tuple components _ => do return .tuple (← components.toList.mapM dictionary.tyOf)
    | _ => none

  partial def staticOf (dictionary : Dictionary) : StaticValue → Option Static
    | .natural value => some (.nat value)
    | .type type => do return .type (← dictionary.tyOf type)
    | _ => none

  partial def nominal (dictionary : Dictionary) (name : String) (statics : List Static) : Option Ty :=
    (dictionary.types.findIdx? fun row => row.name.toString == name && row.statics == statics).map Ty.nominal
end

/-- The number of the package's row with a name and static arguments. -/
def row? (dictionary : Dictionary) (name : String) (statics : Array StaticValue) : Option Nat := do
  let statics ← statics.toList.mapM dictionary.staticOf
  dictionary.operations.findIdx? fun operation =>
    operation.identity.name.toString == name && operation.identity.statics == statics

end Dictionary

/-- Why an evaluation does not go on. -/
inductive Halt where
  /-- The role that evaluates stops, at a guard. -/
  | stop (reason : PIR.Stop)
  /-- The reading cannot go on: something it does not read, or a tree that does not mean
  anything here. -/
  | broken (message : String)

structure Context where
  world : World
  dictionary : Dictionary
  results : ResultStore

/-- The values of one role in one body, and the work left to the reading. -/
structure Local where
  env : Std.HashMap LocalId Datum := {}
  fuel : Nat

abbrev LocalM := ReaderT Context (StateT Local (Except Halt))

def broken {α : Type} (message : String) : LocalM α := throw (.broken message)

/-- One step of work; the reading is broken off when none is left. -/
def tick : LocalM Unit := do
  let state ← get
  if state.fuel == 0 then broken "the reading reached its limit of work"
  set { state with fuel := state.fuel - 1 }

def natOf (datum : Datum) : LocalM Nat :=
  match datum with
  | .number value => pure value
  | .sequence _ => broken "a collection where a number stands"

def itemsOf (datum : Datum) : LocalM (List Datum) :=
  match datum with
  | .sequence items => pure items
  | .number _ => broken "a number where a collection stands"

/-- A row of the tree applied to data: found in the package by its name and static
arguments. -/
def applyRow (name : String) (statics : Array StaticValue) (arguments : List Datum) : LocalM Datum := do
  let context ← read
  let some row := context.dictionary.row? name statics
    | broken s!"the package has no row `{name}` at these static arguments"
  match context.world.apply row arguments with
  | some [result] => pure result
  | some results => pure (.sequence results)
  | none => broken s!"the row `{name}` has no value on these arguments"

/-- An operation of the core, on data. Outside its domain it has no value, and the reading is
broken off: an admitted program does not apply it there. -/
def applyOperation (operation : Typed.CoreOperation) (type : ClosedType) (arguments : List Datum) :
    LocalM Datum := do
  let outside := broken s!"`{operation.name}` is applied outside its domain"
  match operation, arguments with
  | .natAdd, [.number a, .number b] => pure (.number (a + b))
  | .natSub, [.number a, .number b] => if b ≤ a then pure (.number (a - b)) else outside
  | .natMul, [.number a, .number b] => pure (.number (a * b))
  | .natDiv, [.number a, .number b] => if 1 ≤ b then pure (.number (a / b)) else outside
  | .natRem, [.number a, .number b] => if 1 ≤ b then pure (.number (a % b)) else outside
  | .natPow, [.number a, .number b] => pure (.number (a ^ b))
  | .natEqual, [.number a, .number b] => pure (Datum.ofBool (a == b))
  | .natLess, [.number a, .number b] => pure (Datum.ofBool (a < b))
  | .boolAnd, [a, b] => pure (Datum.ofBool (a.toBool && b.toBool))
  | .boolOr, [a, b] => pure (Datum.ofBool (a.toBool || b.toBool))
  | .boolNot, [a] => pure (Datum.ofBool !a.toBool)
  | .boolEqual, [a, b] => pure (Datum.ofBool (a.toBool == b.toBool))
  | .seqLength, [.sequence items] => pure (.number items.length)
  | .seqAt, [.sequence items, .number index] =>
    match items[index]? with
    | some item => pure item
    | none => outside
  | .seqSlice, [.sequence items, .number lower, .number upper] =>
    if lower ≤ upper && upper ≤ items.length then pure (.sequence ((items.drop lower).take (upper - lower)))
    else outside
  | .seqConcat, [.sequence left, .sequence right] => pure (.sequence (left ++ right))
  | .seqFill, [element] =>
    match type with
    | .seq _ (some size) => pure (.sequence (List.replicate size element))
    | _ => broken "`seq.fill` at a type without a size"
  | _, _ => broken s!"`{operation.name}` on arguments it does not take"

/-- The parts of the payload of an alternative: the payload itself when it has one part,
otherwise its components. -/
def payloadParts (payload : Datum) (count : Nat) : LocalM (List Datum) :=
  if count == 1 then pure [payload] else itemsOf payload

mutual
  /-- A conversion, on data. A widening keeps the datum; a refining conversion keeps it where
  its fact holds, and has no value elsewhere. -/
  partial def convert (conversion : Typed.Conversion) (source target : ClosedType) (value : Datum) :
      LocalM Datum := do
    match conversion, source, target with
    | .unsized, _, _ | .indexToNat, _, _ | .widenIndex, _, _ => pure value
    | .fromNonzero, .nonzero field, _ => applyRow "field.from_nonzero" #[.type field] [value]
    | .nonzero, _, .nonzero field => applyRow "field.nonzero" #[.type field] [value]
    | .sized, _, .seq _ (some size) =>
      if (← itemsOf value).length == size then pure value
      else broken "a collection is taken at a size it does not have"
    | .bounded, _, .index bound =>
      if (← natOf value) < bound then pure value else broken "a number is taken below a bound it reaches"
    | .elements inner, .seq from_ _, .seq to _ =>
      return .sequence (← (← itemsOf value).mapM (convert inner from_ to))
    | .components inner, .tuple sources _, .tuple targets _ => do
      let items ← itemsOf value
      let mut converted := #[]
      for index in [0:items.length] do
        let item := items[index]!
        match (inner[index]?).join, sources[index]?, targets[index]? with
        | some part, some from_, some to => converted := converted.push (← convert part from_ to item)
        | _, _, _ => converted := converted.push item
      return .sequence converted.toList
    | .empty, _, _ => pure (.sequence [])
    | .andThen first middle second, _, _ => do
      convert second middle target (← convert first source middle value)
    | _, _, _ => broken "a conversion between types it does not convert"

  partial def eval (expr : Typed.Expr) : LocalM Datum := do
    tick
    match expr with
    | .literal info value =>
      match value with
      | .nat number | .index number => pure (.number number)
      | .bool flag => pure (Datum.ofBool flag)
      | .bytes data => pure (Datum.ofBytes data)
      | .nominal data =>
        let context ← read
        match context.dictionary.tyOf info.type with
        | some (.nominal row) => pure (context.world.literal row data)
        | _ => broken "a literal of a type that the package does not name"
    | .staticValue _ value _ => pure (.number value)
    | .local _ binder =>
      match (← get).env[binder]? with
      | some value => pure value
      | none => broken s!"a role reads the name #{binder}, of which it has no value"
    | .apply info callee arguments => do
      let values ← arguments.toList.mapM eval
      match callee with
      | .operation operation => applyOperation operation info.type values
      | .row row => applyRow row.name row.statics values
      | .boundRow row =>
        applyRow row.key.name (row.key.statics.map fun
          | .type type => StaticValue.type type
          | .nat value => .natural value) values
      | .instance inst => call inst values
      | .member .. => broken "a member of an interface, in an instance"
      | .specification name => broken s!"the specification operation `{name}`"
    | .construct _ what parts => do
      let values ← parts.toList.mapM eval
      match what with
      | .tuple | .sequence | .record _ => pure (.sequence values)
      | .alternative _ index =>
        let payload := match values with
          | [only] => only
          | several => .sequence several
        pure (.sequence [.number index, payload])
    | .project _ target position _ => do
      match (← itemsOf (← eval target))[position]? with
      | some part => pure part
      | none => broken "a part that the value does not have"
    | .convert info conversion value _ => do convert conversion value.type info.type (← eval value)
    | .conditional _ _ condition onTrue onFalse => do
      if (← eval condition).toBool then eval onTrue else eval onFalse
    | .block _ statements result => do
      run statements
      eval result
    | .error .. => broken "an error node"

  /-- A call of a function instance: a row when the function is bound to one, otherwise its
  body, in values of its own. -/
  partial def call (inst : InstanceId) (arguments : List Datum) : LocalM Datum := do
    let context ← read
    if let some (.row rowId) := context.results.body? inst then
      let some row := context.results.rows[rowId]? | broken "a row that the run does not have"
      return ← applyRow row.key.name (row.key.statics.map fun
        | .type type => StaticValue.type type
        | .nat value => .natural value) arguments
    let some definition := context.results.trees.result? inst
      | broken "a function whose tree was not kept"
    let .function body := definition.body | broken "a call of what has no body"
    let outer := (← get).env
    let mut env : Std.HashMap LocalId Datum := {}
    for (parameter, value) in body.parameters.toList.zip arguments do
      env := env.insert parameter.id value
    modify fun state => { state with env }
    run body.statements
    let result ← eval body.result
    modify fun state => { state with env := outer }
    return result

  partial def bind (binder : Typed.Binder) (value : Datum) : LocalM Unit :=
    modify fun state => { state with env := state.env.insert binder.id value }

  /-- Takes a value apart into the binders of a level of a pattern. -/
  partial def unpack (binders : Array (Option Typed.Binder)) (type : ClosedType) (value : Datum) :
      LocalM Unit := do
    let parts ← match type with
      | .variant _ =>
        match ← itemsOf value with
        | [_, payload] => payloadParts payload binders.size
        | _ => broken "a variant that is no alternative"
      | _ => itemsOf value
    for (binder, part) in binders.toList.zip parts do
      if let some binder := binder then bind binder part

  /-- The statements of local code. -/
  partial def run (statements : Array Typed.Stmt) : LocalM Unit := statements.forM runStmt

  partial def runStmt : Typed.Stmt → LocalM Unit
    | .bind _ binder value _ => do bind binder (← eval value)
    | .unpack _ binders value _ => do unpack binders value.type (← eval value)
    | .update _ target value _ => do
      let result ← eval value
      modify fun state => { state with env := state.env.insert target result }
    | .guard _ condition reason _ => do
      unless (← eval condition).toBool do throw (.stop reason.stop)
    | .if _ condition onTrue onFalse _ => do
      if (← eval condition).toBool then run onTrue else run onFalse
    | .match _ scrutinee binder _ cases _ => do
      let value ← eval scrutinee
      if let some binder := binder then bind binder value
      let [.number alternative, payload] ← itemsOf value | broken "a variant that is no alternative"
      let some (.case _ _ binders body) := cases.find? fun (.case _ covered _ _) => covered.contains alternative
        | broken "an alternative that no case covers"
      -- a case of one alternative binds its payload
      unless binders.isEmpty do
        for (binder, part) in binders.toList.zip (← payloadParts payload binders.size) do
          if let some binder := binder then bind binder part
      run body
    | .for _ (.loop index domain collected body) _ => do
      let (start, items) ← match domain with
        | .range start stop _ => do
          let first ← natOf (← eval start)
          let last ← natOf (← eval stop)
          pure (first, (List.range (last - first)).map fun _ => (none : Option Datum))
        | .collection source _ _ => do pure (0, (← itemsOf (← eval source)).map some)
      let mut gathered : Array (Array Datum) := collected.map fun _ => #[]
      let bodies : List (Array Typed.Stmt × Array Typed.Expr) := match body with
        | .uniform statements values => items.map fun _ => (statements, values)
        | .stepped iterations => iterations.toList.map fun (.iteration _ statements values) => (statements, values)
        | .empty .. => []
      let mut position := 0
      for (item, (statements, values)) in items.zip bodies do
        bind index (.number (start + position))
        if let (.collection _ binder _, some element) := (domain, item) then bind binder element
        run statements
        for slot in [0:values.size] do
          gathered := gathered.modify slot (·.push (← eval values[slot]!))
        position := position + 1
      for (binder, values) in collected.toList.zip gathered.toList do
        bind binder (.sequence values.toList)
    | .scope _ body => run body
    | .event .. => broken "an event inside local code"
    | .error .. => broken "an error node"
end

/-! ## The roles together -/

/-- What a role of the run has done, and how it ended, when it has. -/
structure Role where
  ended : Option (Outcome (List Datum)) := none
  did : Array (Zkc.Core.Execute.Event.Kind × Option (List Nat) × Datum) := #[]
  deriving Inhabited

structure Joint where
  roles : Array Role
  /-- How often each key was asked for a coin. -/
  asked : Std.HashMap (List Nat) Nat := {}
  fuel : Nat

abbrev JointM := ReaderT Context (StateT Joint (Except String))

/-- One protocol body in the run: the role of the run that each of its roles is, the keys of
the applications through which it was reached, and its tables. -/
structure Frame where
  roleMap : Array Nat
  depth : Nat
  reached : List Nat
  body : Typed.ProtocolBody
  roles : Typed.Roles

abbrev Envs := Array (Std.HashMap LocalId Datum)

abbrev FrameM := StateT Envs JointM

def running (role : Nat) : JointM Bool := return ((← get).roles[role]?).any (·.ended.isNone)

def endRole (role : Nat) (ended : Outcome (List Datum)) : JointM Unit :=
  modify fun state => { state with roles := state.roles.modify role fun found =>
    if found.ended.isNone then { found with ended := some ended } else found }

def record (role : Nat) (kind : Zkc.Core.Execute.Event.Kind) (key : List Nat) (value : Datum) :
    JointM Unit :=
  modify fun state => { state with roles := state.roles.modify role fun found =>
    { found with did := found.did.push (kind, some key, value) } }

/-- A role that waits for a message that no role sends. -/
def starve (role : Nat) : JointM Unit := do
  if ← running role then endRole role (.failed Zkc.Core.RunComparison.waitingMessage)

/-- An evaluation by one role of a body, on its values: its result, or none when the role is
not running or stops here. -/
def atRole {α : Type} (frame : Frame) (role : Nat) (action : LocalM α) : FrameM (Option α) := do
  let some physical := frame.roleMap[role]? | throw "a role that the body does not have"
  unless ← liftM (running physical : JointM Bool) do return none
  let envs ← get
  let joint ← getThe Joint
  match (action.run (← read)).run { env := (envs[role]?).getD {}, fuel := joint.fuel } with
  | .ok (result, after) =>
    set (envs.set! role after.env)
    modifyThe Joint fun state => { state with fuel := after.fuel }
    return some result
  | .error (.stop reason) =>
    liftM (endRole physical (.stopped reason) : JointM Unit)
    return none
  | .error (.broken message) => throw message

def bindAt (role : Nat) (binder : Option Typed.Binder) (value : Datum) : FrameM Unit := do
  if let some binder := binder then
    modify fun envs => envs.modify role (·.insert binder.id value)

/-- The key of a part of an event of a body, composed along the applications that reached the
body. -/
def keyOf (frame : Frame) (event : Nat) (part : String) (iteration : Array Nat) : List Nat × List Nat :=
  let own := [event, Differential.partNumber part, iteration.size] ++ iteration.toList
  ((frame.depth + 1) :: (frame.reached ++ own), own)

/-- The next coin of a key at a type. -/
def nextCoin (key : List Nat) (type : ClosedType) : JointM Datum := do
  let context ← read
  let some core := context.dictionary.tyOf type | throw "a law at a type that the package does not name"
  let count := ((← get).asked[key]?).getD 0
  modify fun state => { state with asked := state.asked.insert key (count + 1) }
  match context.world.coin key count core with
  | some value => return value
  | none => throw "the provider has no coin at a law's type"

def rolesOf (roles : Typed.Roles) (node : Typed.NodeId) : Array Nat :=
  ((roles.computing[node]?).getD .empty).toArray

def participantsOf (roles : Typed.Roles) (node : Typed.NodeId) : Array Nat :=
  ((roles.participants[node]?).getD .empty).toArray

/-- What the participants that are running make of what decides a choice or a loop: one value,
on which they agree, or none when no participant is running. -/
def decided {α : Type} [BEq α] (frame : Frame) (participants : Array Nat) (action : LocalM α)
    (what : String) : FrameM (Option α) := do
  let mut found : Option α := none
  for role in participants do
    let some value ← atRole frame role action | continue
    match found with
    | some earlier => unless earlier == value do throw s!"the participants do not agree on {what}"
    | none => found := some value
  return found

mutual
  partial def together (frame : Frame) (iteration : Array Nat) (statements : Array Typed.Stmt) :
      FrameM Unit := statements.forM (togetherStmt frame iteration)

  partial def togetherStmt (frame : Frame) (iteration : Array Nat) : Typed.Stmt → FrameM Unit
    | .bind mark binder value _ => do
      for role in rolesOf frame.roles mark.id do
        if let some result ← atRole frame role (eval value) then bindAt role (some binder) result
    | .unpack mark binders value _ => do
      for role in rolesOf frame.roles mark.id do
        discard <| atRole frame role do unpack binders value.type (← eval value)
    | .update mark target value _ => do
      for role in rolesOf frame.roles mark.id do
        if let some result ← atRole frame role (eval value) then
          modify fun envs => envs.modify role (·.insert target result)
    | statement@(.guard mark ..) => do
      for role in rolesOf frame.roles mark.id do
        discard <| atRole frame role (runStmt statement)
    | .if mark condition onTrue onFalse _ => do
      let participants := participantsOf frame.roles mark.id
      match ← decided frame participants (do return (← eval condition).toBool) "a condition" with
      | some true => together frame iteration onTrue
      | some false => together frame iteration onFalse
      | none => pure ()
    | .match mark scrutinee binder _ cases _ => do
      let participants := participantsOf frame.roles mark.id
      let chosen ← decided frame participants (what := "an alternative") do
        let value ← eval scrutinee
        if let some binder := binder then bind binder value
        let [.number alternative, payload] ← itemsOf value | broken "a variant that is no alternative"
        let some (.case _ _ binders _) := cases.find? fun (.case _ covered _ _) => covered.contains alternative
          | broken "an alternative that no case covers"
        unless binders.isEmpty do
          for (binder, part) in binders.toList.zip (← payloadParts payload binders.size) do
            if let some binder := binder then bind binder part
        return alternative
      if let some alternative := chosen then
        if let some (.case _ _ _ body) := cases.find? fun (.case _ covered _ _) => covered.contains alternative then
          together frame iteration body
    | .for mark (.loop index domain collected body) _ => do
      if let .empty .. := body then
        -- a loop of no iteration: each collected name is the empty collection, at its holders
        for binder in collected do
          for role in ((frame.roles.holders[binder.id]?).getD .empty).toArray do
            bindAt role (some binder) (.sequence [])
        return
      let participants := participantsOf frame.roles mark.id
      -- the domain at each participant that is running: where its index starts, the elements of
      -- its collection, and the count, on which the participants agree
      let mut domains : Array (Option (Nat × List Datum)) := frame.roleMap.map fun _ => none
      let mut count : Option Nat := none
      for role in participants do
        let found ← atRole frame role do
          match domain with
          | .range start stop _ => do
            let first ← natOf (← eval start)
            let last ← natOf (← eval stop)
            return (first, last - first, ([] : List Datum))
          | .collection source _ _ => do
            let items ← itemsOf (← eval source)
            return (0, items.length, items)
        let some (first, size, items) := found | continue
        match count with
        | some earlier => unless earlier == size do throw "the participants do not agree on the count of a loop"
        | none => count := some size
        domains := domains.set! role (some (first, items))
      let some iterations := count | return
      let bodies : List (Nat × Array Typed.Stmt × Array Typed.Expr) := match body with
        | .uniform statements values => (List.range iterations).map fun k => (k, statements, values)
        | .stepped iterations => iterations.toList.map fun (.iteration k statements values) => (k, statements, values)
        | .empty .. => []
      let stepped := body matches .stepped _
      -- the iterations of a loop in sequence are those of its count
      if stepped && bodies.length != iterations then
        throw "a loop in sequence whose iterations are not as many as its count"
      let mut gathered : Array (Array (Array Datum)) := collected.map fun _ => frame.roleMap.map fun _ => #[]
      let mut position := 0
      for (k, statements, values) in bodies do
        -- the index and the item, at each participant
        for role in participants do
          let some (first, items) := (domains[role]?).join | continue
          discard <| atRole frame role do
            bind index (.number (first + position))
            if let .collection _ item _ := domain then
              match items[position]? with
              | some element => bind item element
              | none => broken "an element that the collection does not have"
        together frame (if stepped then iteration.push k else iteration) statements
        for slot in [0:values.size] do
          let value := values[slot]!
          for role in rolesOf frame.roles value.info.id do
            if let some result ← atRole frame role (eval value) then
              gathered := gathered.modify slot (·.modify role (·.push result))
        position := position + 1
      for slot in [0:collected.size] do
        let binder := collected[slot]!
        for role in ((frame.roles.holders[binder.id]?).getD .empty).toArray do
          bindAt role (some binder) (.sequence (((gathered[slot]?).bind (·[role]?)).getD #[]).toList)
    | .scope _ body => together frame iteration body
    | .event mark event what => togetherEvent frame iteration mark event what
    | .error .. => throw "an error node"

  partial def togetherEvent (frame : Frame) (iteration : Array Nat) (mark : Typed.Mark) (event : Nat) :
      Typed.Event → FrameM Unit
    | .send binder payload _ receivers => do
      let some sender := frame.roles.senders[mark.id]? | throw "a send without a sender"
      let sent ← atRole frame sender (eval payload)
      if let some value := sent then bindAt sender binder value
      for receiver in receivers do
        let part := if receivers.size ≤ 1 then "value" else s!"to {(frame.body.roster[receiver]?).getD "?"}"
        let (key, _) := keyOf frame event part iteration
        let some to := frame.roleMap[receiver]? | throw "a receiver that the body does not have"
        match sent, frame.roleMap[sender]? with
        | some value, some from_ =>
          liftM (record from_ .sent key value : JointM Unit)
          if ← liftM (running to : JointM Bool) then
            liftM (record to .received key value : JointM Unit)
            bindAt receiver binder value
        | _, _ => liftM (starve to : JointM Unit)
    | .draw binder law owner receivers => do
      let (key, _) := keyOf frame event "value" iteration
      let some drawer := frame.roleMap[owner]? | throw "an owner that the body does not have"
      let type : ClosedType := match law.statics[0]? with
        | some (StaticValue.type type) => type
        | _ => .unit
      if ← liftM (running drawer : JointM Bool) then
        let value ← liftM (nextCoin key type : JointM Datum)
        liftM (record drawer .drew key value : JointM Unit)
        bindAt owner binder value
        for receiver in receivers do
          let some to := frame.roleMap[receiver]? | throw "a receiver that the body does not have"
          if ← liftM (running to : JointM Bool) then
            liftM (record to .heard key value : JointM Unit)
            bindAt receiver binder value
      else
        for receiver in receivers do
          let some to := frame.roleMap[receiver]? | throw "a receiver that the body does not have"
          liftM (starve to : JointM Unit)
    | .sample binder law role => do
      let (key, _) := keyOf frame event "value" iteration
      let some sampler := frame.roleMap[role]? | throw "a role that the body does not have"
      let type : ClosedType := match law.statics[0]? with
        | some (StaticValue.type type) => type
        | _ => .unit
      if ← liftM (running sampler : JointM Bool) then
        let value ← liftM (nextCoin key type : JointM Datum)
        liftM (record sampler .sampled key value : JointM Unit)
        bindAt role binder value
    | .attempt .. => throw "an `attempt`"
    | .apply results callee arguments _ roleMap order => do
      let context ← read
      let some definition := context.results.trees.result? callee | throw "a callee whose tree was not kept"
      let some checked := context.results.checked? callee | throw "a callee that the passes did not read"
      let .protocol body := definition.body | throw "an application of what is no protocol"
      let (_, own) := keyOf frame event "value" iteration
      let inner : Frame :=
        { roleMap := roleMap.map fun role => (frame.roleMap[role]?).getD 0
          depth := frame.depth + 1, reached := frame.reached ++ own, body, roles := checked.roles }
      -- each argument, by each mapped holder of its port, in the order written (HO4)
      let mut envs : Envs := body.roster.map fun _ => {}
      let ports := body.ports.filter (!·.specification)
      for position in order do
        let (some port, some argument) := (ports[position]?, arguments[position]?) | continue
        for holder in port.holders.toArray do
          let some caller := roleMap[holder]? | throw "a role that the map does not give"
          if let some value ← atRole frame caller (eval argument) then
            envs := envs.modify holder (·.insert port.binder.id value)
      let outer ← get
      set envs
      together inner #[] body.statements
      -- the results, each computed by its holders in the callee and bound in the caller
      let mut returned : Array (Nat × Typed.Binder × Datum) := #[]
      for (result, binder) in body.results.toList.zip results.toList do
        for holder in result.holders.toArray do
          if let some value ← atRole inner holder (eval result.value) then
            if let (some binder, some caller) := (binder, roleMap[holder]?) then
              returned := returned.push (caller, binder, value)
      set outer
      for (caller, binder, value) in returned do bindAt caller (some binder) value
end

/-- What each role of a protocol instance shows on inputs, one datum per port and holder in the
order of the ports: the reading of its tree. -/
def read (context : Context) (root : InstanceId) (data : List Datum) (fuel : Nat) :
    Except String (List Zkc.Core.RunComparison.Shown) := do
  let some definition := context.results.trees.result? root | throw "the root has no tree"
  let some checked := context.results.checked? root | throw "the passes did not read the root"
  let .protocol body := definition.body | throw "the root is no protocol"
  let count := body.roster.size
  let frame : Frame :=
    { roleMap := (List.range count).toArray, depth := 0, reached := [], body, roles := checked.roles }
  -- the inputs: one datum per port and holder
  let mut envs : Envs := body.roster.map fun _ => {}
  let mut rest := data
  for port in body.ports do
    if port.specification then continue
    for holder in port.holders.toArray do
      match rest with
      | datum :: more =>
        envs := envs.modify holder (·.insert port.binder.id datum)
        rest := more
      | [] => throw "fewer inputs than ports"
  let action : FrameM (Array (Array Datum)) := do
    together frame #[] body.statements
    -- what each role returns: its copy of each result it holds, in the order of the head
    let mut outputs : Array (Array Datum) := body.roster.map fun _ => #[]
    for result in body.results do
      for holder in result.holders.toArray do
        if let some value ← atRole frame holder (eval result.value) then
          outputs := outputs.modify holder (·.push value)
    return outputs
  let initial : Joint := { roles := body.roster.map fun _ => {}, fuel }
  let ((outputs, _), joint) ← ((action.run envs).run context).run initial
  return (List.range count).map fun role =>
    let found := (joint.roles[role]?).getD {}
    { did := found.did.toList
      ended := found.ended.getD (.returned ((outputs[role]?).getD #[]).toList) }

/-! ## The reading against the run of the package -/

open Zkc.Core in
/-- The model of the vocabulary's rows, on data: what the provider `RunComparison.arithmetic`
answers for a package under a seed. -/
def arithmeticWorld (package : Raw.Package) (seed : Nat) : World :=
  let types := package.types.toArray
  { apply := fun row data =>
      match package.operations[row]? with
      | some operation =>
        match Vocabulary.applyOperation Vocabulary.table types operation data with
        | .ok results => some results
        | .error _ => none
      | none => none
    literal := Vocabulary.literalDatum Vocabulary.table types
    coin := fun key count type =>
      match ValidData.coin Vocabulary.table types seed key count type with
      | .ok value => some value
      | .error _ => none }

open Zkc.Core in
/-- Uninterpreted rows, on data: what the provider of `Zkc.Core.UninterpretedRows` answers
for a package under a seed. -/
def uninterpretedWorld (package : Raw.Package) (seed : Nat)
    (settings : UninterpretedRows.Settings := {}) : World :=
  let types := package.types.toArray
  let rows := UninterpretedRows.rowsOf package
  { apply := fun row data =>
      (package.operations[row]?).map fun operation =>
        UninterpretedRows.answer rows seed settings.trueSeeds
          { row, inputs := operation.signature.inputs, outputs := operation.signature.outputs } data
    literal := UninterpretedRows.literalTerm types
    coin := fun key count type =>
      match UninterpretedRows.coin seed key count type with
      | .ok value => some value
      | .error _ => none }

/-- The work that one reading may do. -/
def workLimit : Nat := 4000000

open Zkc.Core.RunComparison in
/-- The reading of the tree of a protocol root against the run of its package, over seeds,
under a provider: the package's run on the left, the reading on the right. -/
def compareRoot (results : ResultStore) (root : InstanceId) (side : Side) (uninterpreted : Bool)
    (seeds : List Nat) : Verdict :=
  let provider := if uninterpreted then Zkc.Core.UninterpretedRows.provider else arithmetic
  match side.typed.protocols.head?, tooLarge? side.package, provider.refuses side.package with
  | _, some reason, _ | _, _, some reason => .incomplete (.cannotRun reason)
  | none, none, none => .incomplete (.cannotRun "the package has no protocol")
  | some header, none, none =>
    let dictionary : Dictionary :=
      { types := side.package.types.toArray, operations := side.package.operations.toArray }
    overSeeds seeds fun seed => do
      let inputs := agreed (agreementsOf side.package)
        (← provider.inputs side.package seed (header.inputs.map (·.type)))
      let first ← provider.protocol side seed inputs Zkc.Core.defaultLimit
      let world := if uninterpreted then uninterpretedWorld side.package seed
        else arithmeticWorld side.package seed
      -- a reading that breaks off is a fault of the tree, of its tables or of the reading: it is
      -- named so that it is not counted with what the provider cannot run
      let second ← match read { world, dictionary, results } root inputs workLimit with
        | .ok shown => pure shown
        | .error message => throw s!"the reading breaks off: {message}"
      return (inputs, compareShown first second)

/-- The readings of the trees of a program's protocol roots against the runs of their
packages: per root, its description and the verdict. A root whose tree has a refusal, or whose
package is not complete, is not compared. -/
def compareProgram (program : Trees.ProgramTrees) (uninterpreted : Bool) (seeds : List Nat) :
    Array (String × Zkc.Core.RunComparison.Verdict) := Id.run do
  let state := program.session.state
  let results := state.results
  -- the tables of sites of the protocols, by name
  let mut sites : Array (String × Array Differential.SiteRow) := #[]
  for entry in results.bodies.entries do
    let .done (.protocol code) := entry.state | continue
    sites := sites.push (code.name, code.sites.map fun site =>
      { event := site.event, part := site.part, iteration := site.iteration })
  let held : Array (String × RootPackage) := match (program.session.admitRoots none).completeRoots with
    | .ok (roots, _) => roots.held
    | .error _ => #[]
  let mut verdicts := #[]
  for (description, held) in held do
    unless held.protocol.isSome do continue
    -- a root that is held was elaborated and checked without a refusal
    let verdict : Zkc.Core.RunComparison.Verdict :=
      match Differential.duplicateKey? held.package sites, Differential.side held.package sites with
      | some reason, _ => .incomplete (.cannotRun reason)
      | none, .error reason => .incomplete (.cannotRun reason)
      | none, .ok side => compareRoot results held.root side uninterpreted seeds
    verdicts := verdicts.push (description, verdict)
  return verdicts

/-- A verdict as a line. -/
def describeVerdict : Zkc.Core.RunComparison.Verdict → String
  | .agree seeds => s!"observed to agree under {seeds} seeds"
  | .differ seed _ role left right =>
    let who := match role with
      | some role => s!"role {role}"
      | none => "the run"
    s!"observed to differ under seed {seed}: {who}: the package {left}; the tree {right}"
  | .incomplete why => s!"incomplete: {why.describe}"

/-- `zkc-check trees --runs`: after the trees, the reading of each protocol root against the run
of its package. -/
def trees (options : Names.Options) : IO UInt32 := do
  if options.count then return ← Trees.count options
  let code ← Trees.trees options
  unless options.runs do return code
  let inputs ← options.files.mapM Names.readInput
  match ← Trees.treesOf inputs (Names.libraryLoader options.libraries) with
  | .error _ => return code
  | .ok program =>
    for (description, verdict) in compareProgram program options.uninterpreted (List.range options.seeds) do
      IO.println s!"reading {description}: {describeVerdict verdict}"
    return code

end Zkc.Tools.Frontend.Reading
