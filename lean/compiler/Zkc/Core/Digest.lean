module

public import Zkc.Core.Named
public import Std.Data.HashMap

public section

/-! The digest of a role: what a role of a named protocol does, apart from how it is written.

Two producers of one protocol, or one producer before and after a change, name values
differently, order the computations of a statement differently and compute a term once or
twice. What a role does is none of these. The digest of a role is the list, in order, of the
things it does that another party or a later check can see: its guards, the events it takes
part in, its choices and loops with what happens in their regions, and what it returns. Every
value in it is the term that computes it: the operation and the terms of its operands, by a
hash, so that the digest is as long as the body and no longer.

Rows, functions, protocols and declared types are named by what they are (a row's name and
static arguments, a function's name, the fields of a record), not by their numbers in the
package, which depend on the order in which a producer reaches them. A block is transparent:
it is a boundary for proofs and does nothing.

Two packages whose protocols have equal digests at every role make every role do the same
things in the same order on the same values. The converse does not hold where a producer
chooses another form with the same meaning (a boolean operation or a local `if`). The digest
is a check of producers; no theorem reads it.
-/

set_option autoImplicit false

namespace Zkc.Core.Named

namespace Digest

/-- A value as the digest knows it: the hash of the term that computes it, as text. A digest
made to be read has the term itself. -/
abbrev Term := String

/-- The term of a text: its hash, or the text when the digest is made to be read. -/
def term (readable : Bool) (text : String) : Term :=
  if readable then s!"({text})" else toString (hash text)

/-- A package's own names for what its numbers stand for. -/
structure Names where
  package : Package

namespace Names

mutual
  partial def ty (names : Names) : Ty → String
    | .bool => "bool"
    | .nat => "nat"
    | .fin bound => s!"fin{bound}"
    | .seq element size => s!"[{names.ty element};{size}]"
    | .tuple components => s!"({",".intercalate (components.map names.ty)})"
    | .nominal row =>
        match names.package.types[row]? with
        | some entry => s!"{entry.name.toString}<{",".intercalate (entry.statics.map names.static)}>"
        | none => s!"type{row}"
    | .record declaration _ _ =>
        match names.package.records[declaration]? with
        | some record => s!"record\{{",".intercalate (record.fields.map names.ty)}}"
        | none => s!"record{declaration}"
    | .variant declaration _ =>
        match names.package.variants[declaration]? with
        | some found => s!"variant\{{"|".intercalate (found.alternatives.map names.ty)}}"
        | none => s!"variant{declaration}"

  partial def static (names : Names) : Static → String
    | .domain name => name.toString
    | .nat value => toString value
    | .type type => names.ty type
end

def row (names : Names) (number : Nat) : String :=
  match names.package.operations[number]? with
  | some operation =>
      s!"{operation.identity.name.toString}<{",".intercalate (operation.identity.statics.map names.static)}>"
  | none => s!"row{number}"

def function (names : Names) (number : Nat) : String :=
  (names.package.functionNames[number]?).getD s!"function{number}"

def protocol (names : Names) (number : Nat) : String :=
  (names.package.protocolNames[number]?).getD s!"protocol{number}"

def builtin (names : Names) : Raw.Builtin → String
  | .seqLength element size => s!"seq.length[{names.ty element};{size}]"
  | .seqAt element size => s!"seq.at[{names.ty element};{size}]"
  | .seqSlice element size result => s!"seq.slice[{names.ty element};{size};{result}]"
  | .seqConcat element left right => s!"seq.concat[{names.ty element};{left};{right}]"
  | .seqFill element count => s!"seq.fill[{names.ty element};{count}]"
  | .seqMake element count => s!"seq.make[{names.ty element};{count}]"
  | .seqSized element size => s!"seq.sized[{names.ty element};{size}]"
  | .seqUnsized element size => s!"seq.unsized[{names.ty element};{size}]"
  | .tupleMake components => s!"tuple.make({",".intercalate (components.map names.ty)})"
  | .tupleGet components position => s!"tuple.get({",".intercalate (components.map names.ty)}).{position}"
  | .recordMake declaration => s!"make.{names.ty (.record declaration .free [])}"
  | .recordGet declaration position => s!"get.{names.ty (.record declaration .free [])}.{position}"
  | .variantMake declaration position => s!"variant.{names.ty (.variant declaration [])}.{position}"
  | other => reprStr other

def literal (names : Names) : Raw.Literal → String
  | .nominal row data => s!"literal.{names.ty (.nominal row)}{data}"
  | other => reprStr other

end Names

/-- What the digest of a role holds while it goes through a body: the term of each name that
the role has a copy of, and the things done so far. -/
structure State where
  terms : Std.HashMap ValueName Term := {}
  items : Array String := #[]
  /-- A number for the inputs of nested regions, so that two regions' inputs are two terms. -/
  depth : Nat := 0
  /-- Terms are written out and not hashed: for a reader, on a small body. -/
  readable : Bool := false
  /-- The parts of each tuple and record that the body makes: a part taken from one is that
  part, so that a producer that packs values and takes them apart again is one that does
  not. -/
  parts : Std.HashMap Term (List Term) := {}

abbrev DigestM := StateM State

def item (text : String) : DigestM Unit := modify fun state => { state with items := state.items.push text }

/-- The term of a text, in the digest being made. -/
def mk (text : String) : DigestM Term := return term (← get).readable text

def termOf (name : ValueName) : DigestM Term := do
  return ((← get).terms[name]?).getD "unheld"

def bindTerm (name : ValueName) (value : Term) : DigestM Unit :=
  modify fun state => { state with terms := state.terms.insert name value }

/-- Binds the results of an operation to the terms of an application. -/
def bindResults (results : List ValueName) (application : String) : DigestM Unit := do
  match results with
  | [result] => bindTerm result (← mk application)
  | results =>
      for (result, position) in results.zip (List.range results.length) do
        bindTerm result (← mk s!"{application}#{position}")

/-- The entries of a list that a role holds, each with its number among them. A producer may
state a value once with its holders or once per holder: the number of a value among those of a
role is the same in both. -/
def heldBy {α : Type} (held : α → Bool) (entries : List α) : List (α × Option Nat) :=
  (entries.foldl (init := (([] : List (α × Option Nat)), 0)) fun (found, next) entry =>
    if held entry then (found ++ [(entry, some next)], next + 1) else (found ++ [(entry, none)], next)).1

/-- The things done in a nested region, apart: the items, and the terms it returns. The names
bound in it do not leave it. -/
def nested {α : Type} (action : DigestM α) : DigestM (α × Array String) := do
  let saved ← get
  set { saved with items := #[], depth := saved.depth + 1 }
  let result ← action
  let inner := (← get).items
  set saved
  return (result, inner)

def showKey (key : SiteKey) : String := s!"{key.event}/{key.part}/{key.iteration}"

mutual
  /-- The instructions of local code at a role. -/
  partial def localInstructions (names : Names) : List Instruction → DigestM Unit
    | [] => pure ()
    | .mk _ results step :: rest => do
        localStep names results step
        localInstructions names rest

  /-- A local region with the terms of its own inputs: its items, and the terms it returns. -/
  partial def localRegion (names : Names) (inputs : List Term) :
      Region → DigestM (List Term × Array String)
    | .mk own instructions exit =>
        nested do
          for (name, value) in own.zip inputs do bindTerm name value
          localInstructions names instructions
          match exit with
          | .ret values => values.mapM termOf
          | .stop reason =>
              item s!"stop {reprStr reason}"
              pure []

  partial def localStep (names : Names) (results : List ValueName) : LocalOp → DigestM Unit
    | .op row operands => do
        bindResults results s!"{names.row row}({← operands.mapM termOf})"
    | .call callee operands => do
        bindResults results s!"call {names.function callee}({← operands.mapM termOf})"
    | .builtin operation operands => do
        let terms ← operands.mapM termOf
        -- a part of a tuple or a record that the body made is that part
        let parts := (← get).parts
        let taken : Option Term := match operation, terms with
          | .tupleGet _ position, [whole] | .recordGet _ position, [whole] =>
              (parts[whole]?).bind (·[position]?)
          | _, _ => none
        match taken, results with
        | some part, [result] => bindTerm result part
        | _, _ =>
            bindResults results s!"{names.builtin operation}({terms})"
            match operation, results with
            | .tupleMake _, [result] | .recordMake _, [result] =>
                let made ← termOf result
                modify fun state => { state with parts := state.parts.insert made terms }
            | _, _ => pure ()
    | .literal value => bindResults results (names.literal value)
    | .guard reason condition => do item s!"guard {reprStr reason} {← termOf condition}"
    | .conditional condition _ onTrue onFalse => do
        let depth := (← get).depth
        let (whenTrue, trueItems) ← localRegion names [] onTrue
        let (whenFalse, falseItems) ← localRegion names [] onFalse
        let text := s!"if {← termOf condition} then {whenTrue} {hash trueItems} else {whenFalse} {hash falseItems}"
        unless trueItems.isEmpty && falseItems.isEmpty do
          item s!"if {← termOf condition} at depth {depth}: {trueItems} else {falseItems}"
        bindResults results text
    | .match _ value _ arms => do
        let subject ← termOf value
        let mut described : Array String := #[]
        let mut effects := false
        for (arm, position) in arms.zip (List.range arms.length) do
          let (returned, items) ← localRegion names [← mk s!"payload {subject} {position}"] arm
          described := described.push s!"{returned} {hash items}"
          unless items.isEmpty do effects := true
          if effects then item s!"match {subject} arm {position}: {items}"
        bindResults results s!"match {subject} {described}"
    | .loop count _ carried _ body => do
        let depth := (← get).depth
        let counted ← match count with
          | .static count => pure s!"{count}"
          | .runtime value => do pure s!"value {← termOf value}"
        let initial ← carried.mapM termOf
        let readable := (← get).readable
        let inputs := term readable s!"iteration {depth}" ::
          (List.range carried.length).map fun position => term readable s!"carried {depth} {position}"
        let (returned, items) ← localRegion names inputs body
        unless items.isEmpty do item s!"loop {counted} from {initial}: {items}"
        bindResults results s!"loop {counted} from {initial} gives {returned} {hash items}"
    | .block _ (.mk _ instructions exit) => do
        -- a block does nothing: its instructions are those of the region around it
        localInstructions names instructions
        if let .ret values := exit then
          for (result, value) in results.zip values do bindTerm result (← termOf value)
end

mutual
  /-- The instructions of a protocol body as a role sees them. -/
  partial def protocolInstructions (names : Names) (role : Nat) :
      List ProtocolInstruction → DigestM Unit
    | [] => pure ()
    | .mk _ results step :: rest => do
        protocolStep names role results step
        protocolInstructions names role rest

  /-- A region of a protocol body with the terms of its own inputs: its items, and the terms
  it returns. A value that the role does not hold has the term of no value. -/
  partial def protocolRegion (names : Names) (role : Nat) (inputs : List (Option Term)) :
      ProtocolRegion → DigestM (List Term × Array String)
    | .mk own instructions exit =>
        nested do
          for (name, value) in own.zip inputs do
            if let some value := value then bindTerm name value
          protocolInstructions names role instructions
          match exit with
          | .ret values => values.mapM termOf
          | .stop reason =>
              item s!"stop {reprStr reason}"
              pure []

  partial def protocolStep (names : Names) (role : Nat) (results : List ValueName) :
      ProtocolOp → DigestM Unit
    | .compute roles steps => do
        if roles.contains role then localInstructions names steps
    | .exchange sender receiver site value => do
        if role == sender then
          let sent ← termOf value
          item s!"send {showKey site.key} to {receiver}: {sent}"
          if role != receiver then bindResults results s!"sent {sent}"
          -- the sender's copy is the value sent
          if let [result] := results then bindTerm result sent
        if role == receiver then
          item s!"receive {showKey site.key} from {sender}"
          bindResults results s!"received {showKey site.key}"
    | .draw owner receivers site law operands => do
        if role == owner then
          item s!"draw {showKey site.key} {names.row law}({← operands.mapM termOf}) for {receivers}"
        else if receivers.contains role then item s!"hear {showKey site.key} from {owner}"
        if role == owner || receivers.contains role then bindResults results s!"coin {showKey site.key}"
    | .sample owner site law operands => do
        if role == owner then
          item s!"sample {showKey site.key} {names.row law}({← operands.mapM termOf})"
          bindResults results s!"sample {showKey site.key}"
    | .choose participants subject tag outputs arms => do
        unless participants.contains role do return
        let depth := (← get).depth
        let chosen ← termOf subject
        let mut described : Array String := #[]
        for (arm, position) in arms.zip (List.range arms.length) do
          let own ← mk s!"payload {chosen} {position}"
          let payload : List (Option Term) := match tag with
            | .alternative .. => [some own]
            | _ => []
          let (returned, items) ← protocolRegion names role payload arm
          -- what the role returns from the arm: the outputs that it holds
          let held := (returned.zip outputs).filterMap fun (value, output) =>
            if output.holders.contains role then some value else none
          described := described.push s!"arm {position}: {items} returns {held}"
        let text := s!"choose among {participants} on {chosen} at depth {depth}: {described}"
        item text
        for (result, _, position) in results.zip (heldBy (·.holders.contains role) outputs) do
          if let some position := position then bindTerm result (← mk s!"{text}#{position}")
    | .repeat participants count carried collected body => do
        unless participants.contains role do return
        let depth := (← get).depth
        let counted ← match count with
          | .static count => pure s!"{count}"
          | .runtime value => do pure s!"value {← termOf value}"
        let mut initial : Array String := #[]
        for (name, holders) in carried do
          if holders.contains role then initial := initial.push s!"{← termOf name}"
        let readable := (← get).readable
        let inputs : List (Option Term) := some (term readable s!"iteration {depth}") ::
          (heldBy (·.2.contains role) carried).map fun (_, position) =>
            position.map fun position => term readable s!"carried {depth} {position}"
        let (returned, items) ← protocolRegion names role inputs body
        let holders := collected.map (·.holders) ++ carried.map (·.2)
        let held := (returned.zip holders).filterMap fun (value, roles) =>
          if roles.contains role then some value else none
        let text := s!"repeat among {participants} {counted} from {initial}: {items} returns {held}"
        item text
        for (result, _, position) in results.zip (heldBy (·.contains role) holders) do
          if let some position := position then bindTerm result (← mk s!"{text}#{position}")
    | .apply callee roleMap site operands => do
        -- the roles of the callee that this role plays
        let played := (roleMap.zip (List.range roleMap.length)).filterMap fun (caller, position) =>
          if caller == role then some position else none
        if played.isEmpty then return
        let target := names.package.protocols[callee]?
        let ports := (target.map (·.inputs)).getD []
        let mut passed : Array String := #[]
        for (name, port) in operands.zip ports do
          if port.holders.any played.contains then passed := passed.push s!"{← termOf name}"
        let text := s!"apply {names.protocol callee} at {showKey site.key} as {played} on {passed}"
        item text
        let outputs := (target.map (·.outputs)).getD []
        for (result, _, position) in results.zip (heldBy (·.holders.any played.contains) outputs) do
          if let some position := position then bindTerm result (← mk s!"{text}#{position}")
    | .block _ outputs (.mk _ instructions exit) => do
        -- a block does nothing: its instructions are those of the region around it
        protocolInstructions names role instructions
        if let .ret values := exit then
          for ((result, value), output) in (results.zip values).zip outputs do
            if output.holders.contains role then bindTerm result (← termOf value)
    | .join copies => do
        for (name, holder) in copies do
          if holder == role then
            if let [result] := results then bindTerm result (← termOf name)
end

/-- The digest of a role of a protocol of a package. -/
def ofRole (package : Package) (protocol : Protocol) (role : Nat) (readable : Bool := false) :
    Array String :=
  let names : Names := ⟨package⟩
  let action : DigestM Unit := do
    let .mk own instructions exit := protocol.body
    for (name, _, position) in own.zip (heldBy (·.holders.contains role) protocol.inputs) do
      if let some position := position then bindTerm name (← mk s!"port {position}")
    protocolInstructions names role instructions
    if let .ret values := exit then
      let mut returned : Array String := #[]
      for (value, output) in values.zip protocol.outputs do
        if output.holders.contains role then returned := returned.push s!"{← termOf value}"
      item s!"return {returned}"
  (action.run { readable }).2.items

/-- The digest of a function: its one role's. -/
def ofFunction (package : Package) (function : Function) : Array String :=
  let names : Names := ⟨package⟩
  match function.body with
  | none => #["header"]
  | some (.mk own instructions exit) =>
      let action : DigestM Unit := do
        for (name, position) in own.zip (List.range own.length) do bindTerm name (← mk s!"input {position}")
        localInstructions names instructions
        match exit with
        | .ret values => item s!"return {← values.mapM termOf}"
        | .stop reason => item s!"stop {reprStr reason}"
      (action.run {}).2.items

end Digest

/-- The digests of a package: each function by its name, and each role of each protocol by the
names of the protocol and of the role. -/
def Package.digests (package : Package) (readable : Bool := false) : List (String × Array String) :=
  (package.functions.zip package.functionNames).map (fun (function, name) =>
      (name, Digest.ofFunction package function)) ++
    (package.protocols.zip (package.protocolNames.zip package.roleNames)).flatMap
      fun (protocol, name, roles) =>
        (List.range protocol.roles).map fun role =>
          (s!"{name} @ {roles.getD role s!"role{role}"}", Digest.ofRole package protocol role readable)

end Zkc.Core.Named
