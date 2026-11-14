module

public import Zkc.Core.Named
public import Std.Data.HashMap
public import Std.Data.HashSet

public section

/-! The lowering: from a named program to a raw program.

It makes what the positional syntax asks of a producer and what a named program does not
state:

- one raw input per holder of each port, in the order of the ports and of the holders, and an
  agreement per port with several holders, those over the inputs first;
- for a `compute`, for each role in the order of the roles, one `at` per step of the sequence,
  each on that role's copies;
- positions;
- the captures of a nested region: the values around it that it reads, in the order in which
  it first reads them. For a region of a protocol body a value is read by a role, and a copy is
  captured when its holder reads it inside;
- the region of `false` first for a `choose` on a condition, as the raw form wants;
- site numbers in the order of the body, with the table of their keys and names;
- a block per `block` of the named program, with the key of its program point.

It writes the maximum 0 at every loop of a protocol body with a run-time count:
`Zkc.Core.fillMaxima` writes the bound that the facts give.

It shares nothing, removes nothing and holds no rule of facts. It refuses a defect of the
producer: a named program of another shape than its operations have (below), and a value used
where no copy of it is in scope. It is outside the proved part: what it gives is admitted like
any raw program.

It returns, beside the raw package: for each instruction of a raw body, the producer's tag
and the role for which the instruction is a copy; the keys of the sites; the keys of the
program points.
-/

set_option autoImplicit false

namespace Zkc.Core.Named

/-- A defect of the producer: a named program that has no raw program. -/
structure Defect where
  tag : Tag
  message : String
  deriving Repr, Inhabited

/-- Where an instruction of a raw body comes from: its path (in the numbering of the check of
facts), the producer's tag, and, in a protocol body, the role for which it is a copy. -/
structure Origin where
  path : List Nat
  tag : Tag
  role : Option Nat
  deriving Repr, Inhabited

/-- What the lowering of one definition collects. -/
structure Collected where
  origins : Array Origin := #[]
  sites : Array Site := #[]
  points : Array (List Nat × PointKey) := #[]
  deriving Inhabited

abbrev LowerM := StateT Collected (Except Defect)

/-- The position of each copy in scope: of a name, at a role. Local code of a function is at
role 0. -/
abbrev Positions := Std.HashMap (ValueName × Nat) Nat

/-- The positions after binding names at a role, from `next` on. -/
def bindNames (positions : Positions) (role : Nat) (next : Nat) (names : List ValueName) :
    Positions × Nat :=
  names.foldl (fun (positions, next) name => (positions.insert (name, role) next, next + 1))
    (positions, next)

/-- The positions after binding copies, from `next` on. -/
def bindCopies (positions : Positions) (next : Nat) (copies : List (ValueName × Nat)) :
    Positions × Nat :=
  copies.foldl (fun (positions, next) copy => (positions.insert copy next, next + 1))
    (positions, next)

/-- The position of the copy of a name at a role. -/
def lookup (positions : Positions) (tag : Tag) (role : Nat) (name : ValueName) : LowerM Nat :=
  match positions[(name, role)]? with
  | some position => pure position
  | none =>
      throw ⟨tag, s!"the value {name} is used at role {role}, where no copy of it is in scope"⟩

/-- A list without repetitions, in the order of first occurrence. -/
def distinct {α : Type} [BEq α] [Hashable α] (items : List α) : List α :=
  (items.foldl (init := ((#[] : Array α), ({} : Std.HashSet α))) fun (kept, seen) item =>
    if seen.contains item then (kept, seen) else (kept.push item, seen.insert item)).1.toList

/-! ## The shape of a named program

The lowering binds the names that an instruction lists, in order. A named program whose
instruction lists another number of names than its operation has results, or binds a name
twice, would have a raw program with another meaning than the one it names, and admission
could not tell: the raw program is well typed whenever the types happen to agree. So the shape
is checked before anything is lowered: every instruction names exactly the results of its
operation, a region names exactly its own inputs, a name is bound once in a definition, and a
role map has a role for every holder of the callee's ports. -/

/-- The number of results of each row and of each function of a package. -/
structure Arities where
  rows : Array Nat
  functions : Array Nat
  deriving Inhabited

/-- The number of results of a local operation, when the package says it. -/
def LocalOp.arity? (arities : Arities) : LocalOp → Option Nat
  | .op row _ => arities.rows[row]?
  | .call callee _ => arities.functions[callee]?
  | .conditional _ outputs _ _ | .match _ _ outputs _ | .block outputs _ => some outputs.length
  | .loop _ _ carried collected _ => some (collected.length + carried.length)
  | .guard .. => some 0
  | .literal _ | .builtin .. => some 1

/-- The names bound so far in a definition. -/
abbrev ShapeM := StateT (Std.HashSet ValueName) (Except Defect)

/-- Binds names, each for the first time in the definition. -/
def bindOnce (tag : Tag) (names : List ValueName) : ShapeM Unit := do
  for name in names do
    if (← get).contains name then throw ⟨tag, s!"the name {name} is bound twice in a definition"⟩
    modify (·.insert name)

/-- An instruction names as many results as its operation has. -/
def expectResults (tag : Tag) (what : String) (results : List ValueName) (count : Nat) :
    ShapeM Unit :=
  unless results.length == count do
    throw ⟨tag, s!"{what} has {count} results and {results.length} names"⟩

mutual
  /-- The shape of a local region with a number of inputs of its own. -/
  partial def Region.checkShape (arities : Arities) (tag : Tag) (inputs : Nat) : Region → ShapeM Unit
    | .mk own instructions _ => do
        unless own.length == inputs do
          throw ⟨tag, s!"a region with {inputs} inputs of its own names {own.length}"⟩
        bindOnce tag own
        for instruction in instructions do instruction.checkShape arities

  partial def Instruction.checkShape (arities : Arities) : Instruction → ShapeM Unit
    | .mk tag results step => do
        match step with
        | .conditional _ _ onTrue onFalse =>
            onTrue.checkShape arities tag 0
            onFalse.checkShape arities tag 0
        | .match _ _ _ arms => for arm in arms do arm.checkShape arities tag 1
        | .loop _ _ carried _ body => body.checkShape arities tag (1 + carried.length)
        | .block _ body => body.checkShape arities tag 0
        | _ => pure ()
        if let some count := step.arity? arities then expectResults tag "a local operation" results count
        bindOnce tag results
end

/-- The shape of a region of a protocol body with a number of inputs of its own. -/
partial def ProtocolRegion.checkShape (arities : Arities) (callees : Array Protocol) (tag : Tag)
    (inputs : Nat) : ProtocolRegion → ShapeM Unit
  | .mk own instructions _ => do
      unless own.length == inputs do
        throw ⟨tag, s!"a region with {inputs} inputs of its own names {own.length}"⟩
      bindOnce tag own
      for instruction in instructions do
        let .mk tag results step := instruction
        match step with
        | .compute _ steps =>
            expectResults tag "a `compute`" results 0
            for inner in steps do inner.checkShape arities
        | .exchange .. => expectResults tag "an exchange" results 1
        | .draw .. => expectResults tag "a draw" results 1
        | .sample .. => expectResults tag "a sample" results 1
        | .join _ => expectResults tag "a join" results 1
        | .choose _ _ kind outputs arms =>
            let own := match kind with
              | .alternative .. => 1
              | _ => 0
            for arm in arms do arm.checkShape arities callees tag own
            expectResults tag "a choice" results outputs.length
        | .repeat _ _ carried collected body =>
            body.checkShape arities callees tag (1 + carried.length)
            expectResults tag "a loop" results (collected.length + carried.length)
        | .apply callee roleMap _ operands =>
            let some protocol := callees[callee]?
              | throw ⟨tag, s!"the protocol {callee} is applied before it is defined"⟩
            unless operands.length == protocol.inputs.length do
              throw ⟨tag, s!"an application of a protocol with {protocol.inputs.length} ports has {operands.length} operands"⟩
            for port in protocol.inputs ++ protocol.outputs do
              for holder in port.holders do
                unless holder < roleMap.length do
                  throw ⟨tag, s!"the role map of an application has no role for the callee's role {holder}"⟩
            expectResults tag "an application" results protocol.outputs.length
        | .block _ outputs body =>
            body.checkShape arities callees tag 0
            expectResults tag "a block" results outputs.length
        bindOnce tag results

/-! ## Local code -/

mutual
  /-- The names that a local operation reads, those of its nested regions included. -/
  partial def LocalOp.reads : LocalOp → List ValueName
    | .op _ operands | .call _ operands | .builtin _ operands => operands
    | .conditional condition _ onTrue onFalse => condition :: (onTrue.free ++ onFalse.free)
    | .match _ value _ arms => value :: arms.flatMap Region.free
    | .loop count _ carried _ body =>
        (match count with
          | .runtime value => [value]
          | .static _ => []) ++ carried ++ body.free
    | .guard _ condition => [condition]
    | .literal _ => []
    | .block _ body => body.free

  /-- The names that a region reads from around it. -/
  partial def Region.free : Region → List ValueName
    | .mk inputs instructions exit => Id.run do
        let mut bound : Std.HashSet ValueName := inputs.foldl (·.insert ·) {}
        let mut free : Array ValueName := #[]
        for instruction in instructions do
          let .mk _ results step := instruction
          for name in step.reads do
            unless bound.contains name do free := free.push name
          for name in results do bound := bound.insert name
        if let .ret values := exit then
          for name in values do
            unless bound.contains name do free := free.push name
        return distinct free.toList
end

/-- The captures of nested local regions of a role: the names they read of which the role has
a copy in scope, with the positions of the copies, in the order in which the regions first read
them. The order is that of the code and not of where the copies happen to stand, so the same
code at two roles captures alike, and the check of copies sees that it is the same code. -/
def localCaptures (positions : Positions) (role : Nat) (regions : List Region) :
    List (ValueName × Nat) :=
  (distinct (regions.flatMap Region.free)).filterMap fun name =>
    (positions[(name, role)]?).map fun position => (name, position)

mutual
  /-- A local region in positional form: its inputs, then its captures, then the results of
  its instructions. -/
  partial def lowerRegion (role : Nat) (copyOf : Option Nat) (path : List Nat) (region : Region)
      (captures : List ValueName) : LowerM Raw.LocalRegion := do
    let .mk inputs instructions exit := region
    let (positions, next) := bindNames {} role 0 (inputs ++ captures)
    lowerInstructions role copyOf path 0 positions next instructions exit

  partial def lowerInstructions (role : Nat) (copyOf : Option Nat) (path : List Nat) (index : Nat)
      (positions : Positions) (next : Nat) :
      List Instruction → Exit → LowerM Raw.LocalRegion
    | [], .ret values => return .ret (← values.mapM (lookup positions 0 role))
    | [], .stop reason => return .stop reason
    | .mk tag results step :: rest, exit => do
        modify fun collected =>
          { collected with origins := collected.origins.push ⟨path ++ [index], tag, copyOf⟩ }
        match step with
        | .block outputs (.mk _ inner innerExit) =>
            let body ← lowerInstructions role copyOf (path ++ [index]) 0 positions next inner
              innerExit
            let (positions, next) := bindNames positions role next results
            return .block outputs body
              (← lowerInstructions role copyOf path (index + 1) positions next rest exit)
        | step =>
            let raw ← lowerStep role copyOf (path ++ [index]) positions tag step
            let (positions, next) := bindNames positions role next results
            return .step raw
              (← lowerInstructions role copyOf path (index + 1) positions next rest exit)

  partial def lowerStep (role : Nat) (copyOf : Option Nat) (path : List Nat) (positions : Positions)
      (tag : Tag) : LocalOp → LowerM Raw.LocalStep
    | .op row operands => return .op row (← operands.mapM (lookup positions tag role))
    | .call callee operands => return .call callee (← operands.mapM (lookup positions tag role))
    | .conditional condition outputs onTrue onFalse => do
        let captures := localCaptures positions role [onTrue, onFalse]
        return .conditional (← lookup positions tag role condition) (captures.map (·.2)) outputs
          (← lowerRegion role copyOf (path ++ [0]) onTrue (captures.map (·.1)))
          (← lowerRegion role copyOf (path ++ [1]) onFalse (captures.map (·.1)))
    | .match declaration value outputs arms => do
        let captures := localCaptures positions role arms
        let mut lowered : Array Raw.LocalRegion := #[]
        for arm in arms do
          lowered := lowered.push
            (← lowerRegion role copyOf (path ++ [lowered.size]) arm (captures.map (·.1)))
        return .match declaration (← lookup positions tag role value) (captures.map (·.2)) outputs
          (Raw.LocalArms.ofList lowered.toList)
    | .loop count maximum carried collected body => do
        let captures := localCaptures positions role [body]
        let rawCount : Raw.LoopCount ← match count with
          | .static count => pure (.static count)
          | .runtime value => pure (.runtime maximum (← lookup positions tag role value))
        return .loop rawCount (← carried.mapM (lookup positions tag role)) (captures.map (·.2))
          collected (← lowerRegion role copyOf (path ++ [0]) body (captures.map (·.1)))
    | .guard reason condition => return .guard reason (← lookup positions tag role condition)
    | .literal value => return .literal value
    | .builtin operation operands =>
        return .builtin operation (← operands.mapM (lookup positions tag role))
    | .block .. => throw ⟨tag, "a block stands among the instructions of a region"⟩
end

/-! ## Protocol bodies -/

/-- The copies that a list of names is, at the holders given for each: per name, one copy per
holder, in order. -/
def copiesOf (names : List ValueName) (holders : List (List Nat)) : List (ValueName × Nat) :=
  (names.zip holders).flatMap fun (name, roles) => roles.map fun role => (name, role)

/-- The located types of outputs: per output, one per holder, in order. -/
def locatedOf (outputs : List Output) : List Located :=
  outputs.flatMap fun output => output.holders.map fun holder => ⟨output.type, holder⟩

mutual
  /-- The copies that an operation of a protocol body reads: a name, at the role that reads
  it. -/
  partial def ProtocolOp.uses (callees : Array Protocol) : ProtocolOp → List (ValueName × Nat)
    | .compute roles steps =>
        (Region.mk [] steps (.ret [])).free.flatMap fun name => roles.map fun role => (name, role)
    | .exchange sender _ _ value => [(value, sender)]
    | .draw owner _ _ _ operands | .sample owner _ _ operands => operands.map fun name => (name, owner)
    | .choose participants subject _ outputs arms =>
        participants.map (fun role => (subject, role)) ++
          arms.flatMap fun arm => arm.uses callees (outputs.map (·.holders))
    | .repeat participants count carried collected body =>
        (match count with
          | .runtime value => participants.map fun role => (value, role)
          | .static _ => []) ++
          copiesOf (carried.map (·.1)) (carried.map (·.2)) ++
          body.uses callees (collected.map (·.holders) ++ carried.map (·.2))
    | .apply callee roleMap _ operands =>
        match callees[callee]? with
        | some protocol =>
            (operands.zip protocol.inputs).flatMap fun (name, port) =>
              port.holders.map fun holder => (name, roleMap.getD holder 0)
        | none => []
    | .block _ outputs body => body.uses callees (outputs.map (·.holders))
    | .join copies => copies

  /-- The copies that a region of a protocol body reads from around it. `returned` gives, for
  each value that the region returns, the roles that hold it. -/
  partial def ProtocolRegion.uses (callees : Array Protocol) (returned : List (List Nat)) :
      ProtocolRegion → List (ValueName × Nat)
    | .mk inputs instructions exit => Id.run do
        let mut bound : Std.HashSet ValueName := inputs.foldl (·.insert ·) {}
        let mut free : Array (ValueName × Nat) := #[]
        for instruction in instructions do
          let .mk _ results step := instruction
          for use in step.uses callees do
            unless bound.contains use.1 do free := free.push use
          for name in results do bound := bound.insert name
          -- a `compute` binds the results of its steps
          if let .compute _ steps := step then
            for inner in steps do
              let .mk _ made _ := inner
              for name in made do bound := bound.insert name
        if let .ret values := exit then
          for use in copiesOf values returned do
            unless bound.contains use.1 do free := free.push use
        return distinct free.toList
end

/-- The captures of nested regions of a protocol body: the copies they read that are in
scope, with their positions, in the order in which the regions first read them. -/
def protocolCaptures (positions : Positions) (uses : List (ValueName × Nat)) :
    List ((ValueName × Nat) × Nat) :=
  (distinct uses).filterMap fun copy => (positions[copy]?).map fun position => (copy, position)

/-- The number of a new site. -/
def newSite (site : Site) : LowerM Nat := do
  let number := (← get).sites.size
  modify fun collected => { collected with sites := collected.sites.push site }
  return number

mutual
  /-- A region of a protocol body in positional form: its inputs, in the order given, then
  the results of its instructions. -/
  partial def lowerProtocolRegion (callees : Array Protocol) (path : List Nat)
      (inputs : List (ValueName × Nat)) (returned : List (List Nat)) (region : ProtocolRegion) :
      LowerM Raw.ProtocolRegion := do
    let .mk _ instructions exit := region
    let (positions, next) := bindCopies {} 0 inputs
    lowerProtocolInstructions callees path 0 positions next returned instructions exit

  partial def lowerProtocolInstructions (callees : Array Protocol) (path : List Nat) (index : Nat)
      (positions : Positions) (next : Nat) (returned : List (List Nat)) :
      List ProtocolInstruction → Exit → LowerM Raw.ProtocolRegion
    | [], .ret values =>
        return .ret (← (copiesOf values returned).mapM fun (name, role) =>
          lookup positions 0 role name)
    | [], .stop reason => return .stop reason
    | .mk tag results step :: rest, exit => do
        let origin (offset : Nat) (role : Option Nat) : LowerM Unit :=
          modify fun collected =>
            { collected with origins := collected.origins.push ⟨path ++ [index + offset], tag, role⟩ }
        let continue_ (positions : Positions) (next : Nat) (count : Nat) :
            LowerM Raw.ProtocolRegion :=
          lowerProtocolInstructions callees path (index + count) positions next returned rest exit
        match step with
        | .compute roles steps =>
            -- for each role, in the order of the roles, the whole sequence: one `at` per step
            let mut positions := positions
            let mut next := next
            let mut made : Array Raw.ProtocolStep := #[]
            for role in roles do
              for inner in steps do
                let .mk innerTag innerResults step := inner
                let place := path ++ [index + made.size]
                modify fun collected =>
                  { collected with origins := collected.origins.push ⟨place, innerTag, some role⟩ }
                let raw ← lowerStep role (some role) (path ++ [index + made.size]) positions
                  innerTag step
                made := made.push (.at role raw)
                (positions, next) := bindNames positions role next innerResults
            let after ← continue_ positions next made.size
            return made.foldr (init := after) fun step rest => .step step rest
        | .exchange sender receiver site value =>
            origin 0 none
            let sent ← lookup positions tag sender value
            let raw := Raw.ProtocolStep.exchange sender receiver (← newSite site) sent
            let positions := match results with
              | [result] => (positions.insert (result, receiver) next).insert (result, sender) sent
              | _ => positions
            return .step raw (← continue_ positions (next + 1) 1)
        | .draw owner receivers site law operands =>
            origin 0 none
            let raw := Raw.ProtocolStep.draw owner receivers (← newSite site) law
              (← operands.mapM (lookup positions tag owner))
            let (positions, next) := match results with
              | [result] => bindCopies positions next ((owner :: receivers).map fun role => (result, role))
              | _ => (positions, next + 1 + receivers.length)
            return .step raw (← continue_ positions next 1)
        | .sample owner site law operands =>
            origin 0 none
            let raw := Raw.ProtocolStep.sample owner (← newSite site) law
              (← operands.mapM (lookup positions tag owner))
            let (positions, next) := bindCopies positions next (results.map fun result => (result, owner))
            return .step raw (← continue_ positions next 1)
        | .choose participants subject kind outputs arms =>
            origin 0 none
            let holders := outputs.map (·.holders)
            let captures := protocolCaptures positions
              (arms.flatMap fun arm => arm.uses callees holders)
            let tags ← participants.mapM fun role => lookup positions tag role subject
            -- the regions in the order of the raw form: for a condition, `false` first
            let ordered : List ProtocolRegion := match kind, arms with
              | .condition, [onTrue, onFalse] => [onFalse, onTrue]
              | _, arms => arms
            let mut lowered : Array Raw.ProtocolRegion := #[]
            for arm in ordered do
              let .mk own _ _ := arm
              -- the payload of an alternative, at every participant, before the captures
              let ownCopies := own.flatMap fun name => participants.map fun role => (name, role)
              lowered := lowered.push
                (← lowerProtocolRegion callees (path ++ [index, lowered.size])
                  (ownCopies ++ captures.map (·.1)) holders arm)
            let raw := Raw.ProtocolStep.choose participants tags kind (captures.map (·.2))
              (locatedOf outputs) (Raw.ProtocolArms.ofList lowered.toList)
            let (positions, next) := bindCopies positions next (copiesOf results holders)
            return .step raw (← continue_ positions next 1)
        | .repeat participants count carried collected body =>
            origin 0 none
            let holders := collected.map (·.holders) ++ carried.map (·.2)
            let captures := protocolCaptures positions (body.uses callees holders)
            let rawCount : Raw.RepeatCount ← match count with
              | .static count => pure (.static count)
              | .runtime value =>
                  pure (.runtime 0 (← participants.mapM fun role => lookup positions tag role value))
            let initial ← (copiesOf (carried.map (·.1)) (carried.map (·.2))).mapM fun (name, role) =>
              lookup positions tag role name
            let .mk own _ _ := body
            -- the iteration number at every participant, then the carried values at their holders
            let ownCopies := match own with
              | [] => []
              | number :: inner =>
                  participants.map (fun role => (number, role)) ++ copiesOf inner (carried.map (·.2))
            let region ← lowerProtocolRegion callees (path ++ [index, 0])
              (ownCopies ++ captures.map (·.1)) holders body
            let raw := Raw.ProtocolStep.repeat participants rawCount initial (captures.map (·.2))
              (locatedOf collected) region
            let (positions, next) := bindCopies positions next (copiesOf results holders)
            return .step raw (← continue_ positions next 1)
        | .apply callee roleMap site operands =>
            origin 0 none
            let some protocol := callees[callee]?
              | throw ⟨tag, s!"the protocol {callee} is applied before it is defined"⟩
            let mapped (holders : List Nat) : List Nat := holders.map fun holder => roleMap.getD holder 0
            let passed ← (copiesOf operands (protocol.inputs.map fun port => mapped port.holders)).mapM
              fun (name, role) => lookup positions tag role name
            let raw := Raw.ProtocolStep.apply callee roleMap (← newSite site) passed
            let (positions, next) := bindCopies positions next
              (copiesOf results (protocol.outputs.map fun port => mapped port.holders))
            return .step raw (← continue_ positions next 1)
        | .block point outputs (.mk _ inner innerExit) =>
            origin 0 none
            modify fun collected =>
              { collected with points := collected.points.push (path ++ [index], point) }
            let holders := outputs.map (·.holders)
            let body ← lowerProtocolInstructions callees (path ++ [index]) 0 positions next holders
              inner innerExit
            let (positions, next) := bindCopies positions next (copiesOf results holders)
            return .block (locatedOf outputs) body (← continue_ positions next 1)
        | .join copies =>
            -- no instruction: the result at each role is the copy named there
            let mut positions := positions
            for (name, role) in copies do
              let position ← lookup positions tag role name
              if let [result] := results then positions := positions.insert (result, role) position
            continue_ positions next 0
end

/-! ## Definitions and packages -/

/-- A function in positional form, with the origins of its instructions. -/
def lowerFunction (arities : Arities) (function : Function) :
    Except Defect (Raw.Function × Collected) :=
  match function.body with
  | none => .ok (⟨function.specificationOnly, function.inputs, function.outputs, none⟩, {})
  | some region => do
      (region.checkShape arities 0 function.inputs.length).run' {}
      let (body, collected) ← (lowerRegion 0 none [] region []).run {}
      return (⟨function.specificationOnly, function.inputs, function.outputs, some body⟩, collected)

/-- The agreements of ports: one per port with several holders, over the positions of its
copies. -/
def agreementsOf (overOutputs : Bool) (ports : List Output) : List Raw.Agreement :=
  (ports.foldl (init := ((#[] : Array Raw.Agreement), 0)) fun (agreements, position) port =>
    let copies := List.range port.holders.length |>.map (position + ·)
    (if port.holders.length > 1 then agreements.push ⟨overOutputs, copies⟩ else agreements,
      position + port.holders.length)).1.toList

/-- A protocol in positional form, with what its lowering collects. -/
def lowerProtocol (arities : Arities) (callees : Array Protocol) (protocol : Protocol) :
    Except Defect (Raw.Protocol × Collected) := do
  (protocol.body.checkShape arities callees 0 protocol.inputs.length).run' {}
  let .mk names _ _ := protocol.body
  let inputs := copiesOf names (protocol.inputs.map (·.holders))
  let (body, collected) ← (lowerProtocolRegion callees [] inputs
    (protocol.outputs.map (·.holders)) protocol.body).run {}
  return ({ specificationOnly := protocol.specificationOnly, roles := protocol.roles
            inputs := locatedOf protocol.inputs, outputs := locatedOf protocol.outputs
            agreements := agreementsOf false protocol.inputs ++ agreementsOf true protocol.outputs
            body }, collected)

/-- Which definition a defect or an origin is in. -/
inductive Definition where
  | function (number : Nat)
  | protocol (number : Nat)
  deriving Repr, Inhabited, DecidableEq

/-- What the lowering gives: the raw package; the keys of the sites of each protocol; for each
definition, the origins of the instructions of its body; for each protocol, the program points
of its blocks. -/
structure Lowered where
  package : Raw.Package
  keys : SiteKeys
  functionOrigins : List (List Origin)
  protocolOrigins : List (List Origin)
  points : List (List (List Nat × PointKey))

/-- The raw package of a named package. -/
def lower (package : Package) : Except (Definition × Defect) Lowered := do
  let arities : Arities :=
    { rows := (package.operations.map (·.signature.outputs.length)).toArray
      functions := (package.functions.map (·.outputs.length)).toArray }
  let mut functions : Array Raw.Function := #[]
  let mut functionOrigins : Array (List Origin) := #[]
  for function in package.functions do
    match lowerFunction arities function with
    | .ok (raw, collected) =>
        functions := functions.push raw
        functionOrigins := functionOrigins.push collected.origins.toList
    | .error defect => throw (.function functions.size, defect)
  let mut protocols : Array Raw.Protocol := #[]
  let mut protocolOrigins : Array (List Origin) := #[]
  let mut keys : Array (List SiteKey) := #[]
  let mut siteNames : Array (List String) := #[]
  let mut points : Array (List (List Nat × PointKey)) := #[]
  let callees := package.protocols.toArray
  for protocol in package.protocols do
    match lowerProtocol arities (callees.extract 0 protocols.size) protocol with
    | .ok (raw, collected) =>
        protocols := protocols.push raw
        protocolOrigins := protocolOrigins.push collected.origins.toList
        keys := keys.push (collected.sites.toList.map (·.key))
        siteNames := siteNames.push (collected.sites.toList.map (·.name))
        points := points.push collected.points.toList
    | .error defect => throw (.protocol protocols.size, defect)
  return {
    package :=
      { types := package.types, records := package.records, variants := package.variants
        operations := package.operations, functions := functions.toList
        protocols := protocols.toList
        names := some
          { functions := package.functionNames, protocols := package.protocolNames
            roles := package.roleNames, sites := siteNames.toList } }
    keys := keys.toList
    functionOrigins := functionOrigins.toList
    protocolOrigins := protocolOrigins.toList
    points := points.toList }

end Zkc.Core.Named
