module

public import Zkc.Core.Elaborate
public import Zkc.Core.Facts
public import Zkc.Core.ProtocolFacts
public import Zkc.Core.VocabularyModel

@[expose] public section

/-! Mutants of a package: the package changed at one instruction, for measuring how much a
comparison of runs tells apart.

Four kinds of change, at every instruction of every function and of every protocol, nested
regions included. Three of them are made on the raw text of the package:

- **Exchange**: two operands of an operation, a call or an application, at two positions that
  hold different values, exchanged; not at an operation that is commutative (`add`, `mul`,
  `equal` and `inner` of the vocabulary, the core's `nat.add`, `nat.mul`, `nat.equal` and the
  binary operations of `bool`), where the mutant would be equivalent.
- **Literal**: a literal changed by one: a number or a natural of a nominal literal one more,
  a `bool` negated, the first byte of bytes one more.
- **Replace**: a row replaced by another row of the package with the same signature (inputs,
  outputs and kind); a row of the arithmetic of the vocabulary (`add`, `sub`, `mul` of a type)
  by another of them at the same type that the package does not have, added to its table when
  the vocabulary gives it the same signature; and an operation that the core owns by another of
  its group: the
  arithmetic of naturals (`nat.add`, `nat.mul`, `nat.sub`, `nat.div`, `nat.rem`, `nat.pow`), the
  comparisons of naturals (`nat.equal`, `nat.less`), the binary operations of `bool`
  (`bool.and`, `bool.or`, `bool.equal`).

The fourth is made with the core's own elaboration of each instruction, so that every
candidate is typed (`replacementCandidates`):

- **Replace an operand**: one operand of an instruction, or one value that a region returns,
  replaced by another value of its type in scope; in a protocol, by one that the same role
  holds.

A mutant is kept when the core admits it: `elaborate` accepts it and every function and
protocol passes the check of facts (`admitted`). An exchange of two operands of different types
is refused there, so an exchange that is kept exchanges two operands of one type. Each mutant
names its definition, the number of its instruction in the order of the text of the
definition, and the change.

A **probe** of an instruction is the package with a stop just before the instruction
(`probes`). The runs of a package and of a probe differ under a seed exactly when the
instruction is reached under it, which tells a mutant that survives because its instruction
is never reached from one whose change the runs reach and do not show. -/

set_option autoImplicit false

namespace Zkc.Core.Mutation

open Raw

/-- One change of a package, with the place and the change in words. `place` names the
definition and the instruction alone: a mutant and the probe of its instruction have one
place. -/
structure Mutant where
  description : String
  package : Raw.Package
  place : String := ""

/-- The groups of operations that the core owns, each of one signature. -/
def builtinGroups : List (List Raw.Builtin) :=
  [[.natAdd, .natMul, .natSub, .natDiv, .natRem, .natPow], [.natEqual, .natLess],
   [.boolAnd, .boolOr, .boolEqual]]

/-- The operations of the vocabulary that are commutative, by the member of their row's name:
`add`, `mul` and `equal` of fields, groups, rings and collections, and the inner product of
collections of a field. An exchange of their two operands is an equivalent mutant, and is not
made. -/
def commutativeRow (name : String) : Bool :=
  [".add", ".mul", ".equal", ".inner"].any fun member => name.endsWith member

/-- The operations that the core owns that are commutative. -/
def commutativeBuiltin : Raw.Builtin → Bool
  | .natAdd | .natMul | .natEqual | .boolAnd | .boolOr | .boolEqual => true
  | _ => false

/-- The operands at two positions exchanged, for every pair of positions that hold different
values. -/
def exchanges (operands : List Nat) : List (String × List Nat) := Id.run do
  let values := operands.toArray
  let mut found := #[]
  for first in [0:values.size] do
    for second in [first + 1:values.size] do
      if values[first]! != values[second]! then
        let swapped := (values.set! first values[second]!).set! second values[first]!
        found := found.push (s!"operands {first} and {second} exchanged", swapped.toList)
  return found.toList

/-- A literal changed by one. -/
def literalChanges : Raw.Literal → List (String × Raw.Literal)
  | .nat value => [("the natural one more", .nat (value + 1))]
  | .bool value => [("the `bool` negated", .bool !value)]
  | .fin bound value => [("the index one more", .fin bound (value + 1))]
  | .nominal row (first :: rest) => [("the first number one more", .nominal row ((first + 1) :: rest))]
  | .nominal _ [] => []
  | .bytes (first :: rest) => [("the first byte one more", .bytes (((first + 1) % 256) :: rest))]
  | .bytes [] => []

/-- The members of the arithmetic of a type of the vocabulary that may replace one another. -/
def arithmeticMembers : List String := ["add", "sub", "mul"]

/-- The rows of the vocabulary that may replace a row of arithmetic and that a package does not
have: the same type and static arguments, another member of `arithmeticMembers`, with the
signature that the vocabulary gives it the same as the row's. -/
def vocabularyReplacements (package : Raw.Package) (operation : Operation) : List Operation :=
  match operation.identity.name.toString.splitOn "." with
  | [owner, member] =>
    if !arithmeticMembers.contains member then []
    else (arithmeticMembers.filter (· != member)).filterMap fun other =>
      let candidate : Operation :=
        { operation with identity := { operation.identity with name := Name.ofString s!"{owner}.{other}" } }
      if package.operations.any (·.identity == candidate.identity) then none
      else if (Vocabulary.mismatch Vocabulary.table package candidate).isNone then some candidate
      else none
  | _ => []

/-- The changes of one local instruction, without its nested regions: the description, the
changed instruction, and the row that the change adds to the package's table, if any (the
instruction names it by the number after the last row). -/
def stepChanges (package : Raw.Package) : LocalStep → List (String × LocalStep × Option Operation)
  | .op row operands =>
    let operations := package.operations
    let replacements := match operations[row]? with
      | some operation =>
        let present := (List.range operations.length).filterMap fun other =>
          match operations[other]? with
          | some candidate =>
            if other != row && candidate.signature == operation.signature then
              some (s!"row `{operation.identity.name.toString}` replaced by `{candidate.identity.name.toString}`",
                LocalStep.op other operands, none)
            else none
          | none => none
        present ++ (vocabularyReplacements package operation).map fun candidate =>
          (s!"row `{operation.identity.name.toString}` replaced by `{candidate.identity.name.toString}`, added",
            LocalStep.op operations.length operands, some candidate)
      | none => []
    let commutative := (operations[row]?).any fun operation =>
      commutativeRow operation.identity.name.toString
    (if commutative then [] else
      (exchanges operands).map fun (what, swapped) => (what, .op row swapped, none)) ++ replacements
  | .builtin operation operands =>
    let group := (builtinGroups.find? (·.contains operation)).getD []
    (if commutativeBuiltin operation then [] else
      (exchanges operands).map fun (what, swapped) => (what, .builtin operation swapped, none)) ++
      (group.filter (· != operation)).map fun other =>
        (s!"`{operation.name}` replaced by `{other.name}`", .builtin other operands, none)
  | .call callee operands =>
    (exchanges operands).map fun (what, swapped) => (what, .call callee swapped, none)
  | .literal value => (literalChanges value).map fun (what, changed) => (what, .literal changed, none)
  | _ => []

/-- A change found by a walk: the number of its instruction in the walk, the change, and the row
that it adds to the table, if any. -/
abbrev Found (α : Type) := List (Nat × String × α × Option Operation)

mutual
  /-- The changes of a local region, each with the number of its instruction, numbered from
  `next` in the order of the text. -/
  partial def localRegion (package : Raw.Package) :
      LocalRegion → StateM Nat (Found LocalRegion)
    | .ret _ | .stop _ => pure []
    | .step instruction next => do
      let here ← localStep package instruction
      let later ← localRegion package next
      return here.map (fun (at_, what, changed, added) => (at_, what, .step changed next, added)) ++
        later.map fun (at_, what, changed, added) => (at_, what, .step instruction changed, added)
    | .block outputs body next => do
      let inside ← localRegion package body
      let later ← localRegion package next
      return inside.map (fun (at_, what, changed, added) => (at_, what, .block outputs changed next, added)) ++
        later.map fun (at_, what, changed, added) => (at_, what, .block outputs body changed, added)

  /-- The changes of a local instruction and of its nested regions. -/
  partial def localStep (package : Raw.Package) (instruction : LocalStep) :
      StateM Nat (Found LocalStep) := do
    let number ← modifyGet fun number => (number, number + 1)
    let own := (stepChanges package instruction).map fun (what, changed, added) => (number, what, changed, added)
    let nested ← match instruction with
      | .conditional condition captures outputs onTrue onFalse => do
        let first ← localRegion package onTrue
        let second ← localRegion package onFalse
        pure (first.map (fun (at_, what, changed, added) =>
            (at_, what, LocalStep.conditional condition captures outputs changed onFalse, added)) ++
          second.map fun (at_, what, changed, added) =>
            (at_, what, LocalStep.conditional condition captures outputs onTrue changed, added))
      | .«match» declaration value captures outputs arms => do
        let changed ← localArms package arms
        pure (changed.map fun (at_, what, arms, added) =>
          (at_, what, LocalStep.«match» declaration value captures outputs arms, added))
      | .loop count carried captures collected body => do
        let changed ← localRegion package body
        pure (changed.map fun (at_, what, body, added) =>
          (at_, what, LocalStep.loop count carried captures collected body, added))
      | _ => pure []
    return own ++ nested

  partial def localArms (package : Raw.Package) : LocalArms → StateM Nat (Found LocalArms)
    | .none => pure []
    | .arm region rest => do
      let here ← localRegion package region
      let later ← localArms package rest
      return here.map (fun (at_, what, changed, added) => (at_, what, .arm changed rest, added)) ++
        later.map fun (at_, what, changed, added) => (at_, what, .arm region changed, added)
end

mutual
  /-- The changes of a protocol region, numbered as `localRegion` numbers them. -/
  partial def protocolRegion (package : Raw.Package) :
      ProtocolRegion → StateM Nat (Found ProtocolRegion)
    | .ret _ | .stop _ => pure []
    | .step instruction next => do
      let here ← protocolStep package instruction
      let later ← protocolRegion package next
      return here.map (fun (at_, what, changed, added) => (at_, what, .step changed next, added)) ++
        later.map fun (at_, what, changed, added) => (at_, what, .step instruction changed, added)
    | .block outputs body next => do
      let inside ← protocolRegion package body
      let later ← protocolRegion package next
      return inside.map (fun (at_, what, changed, added) => (at_, what, .block outputs changed next, added)) ++
        later.map fun (at_, what, changed, added) => (at_, what, .block outputs body changed, added)

  partial def protocolStep (package : Raw.Package) (instruction : ProtocolStep) :
      StateM Nat (Found ProtocolStep) := do
    match instruction with
    | .at role step =>
      let changed ← localStep package step
      return changed.map fun (at_, what, step, added) => (at_, what, .at role step, added)
    | .apply callee roleMap site operands =>
      let number ← modifyGet fun number => (number, number + 1)
      return (exchanges operands).map fun (what, swapped) =>
        (number, what, .apply callee roleMap site swapped, none)
    | .«repeat» participants count carried captures collected body =>
      let _ ← modifyGet fun number => (number, number + 1)
      let changed ← protocolRegion package body
      return changed.map fun (at_, what, body, added) =>
        (at_, what, .«repeat» participants count carried captures collected body, added)
    | .choose participants tags tag captures outputs arms =>
      let _ ← modifyGet fun number => (number, number + 1)
      let changed ← protocolArms package arms
      return changed.map fun (at_, what, arms, added) =>
        (at_, what, .choose participants tags tag captures outputs arms, added)
    | _ =>
      let _ ← modifyGet fun number => (number, number + 1)
      return []

  partial def protocolArms (package : Raw.Package) :
      ProtocolArms → StateM Nat (Found ProtocolArms)
    | .none => pure []
    | .arm region rest => do
      let here ← protocolRegion package region
      let later ← protocolArms package rest
      return here.map (fun (at_, what, changed, added) => (at_, what, .arm changed rest, added)) ++
        later.map fun (at_, what, changed, added) => (at_, what, .arm region changed, added)
end

/-- The name of a definition in the side table of names, or its kind and number. -/
def definitionName (names : List String) (kind : String) (number : Nat) : String :=
  match names[number]? with
  | some name => s!"{kind} `{name}`"
  | none => s!"{kind} {number}"

/-- Every package that differs from a package at one instruction by one change, before
admission. -/
def candidates (package : Raw.Package) : List Mutant :=
  let functionNames := (package.names.map (·.functions)).getD []
  let protocolNames := (package.names.map (·.protocols)).getD []
  let ofFunctions := (List.range package.functions.length).flatMap fun index =>
    match package.functions[index]? with
    | some function =>
      match function.body with
      | some body =>
        let place := definitionName functionNames "function" index
        ((localRegion package body).run' 0).map fun (at_, what, changed, added) =>
          let mutated : Raw.Function := { function with body := some changed }
          { description := s!"{place}, instruction {at_}: {what}"
            place := s!"{place}, instruction {at_}"
            package := { package with functions := package.functions.set index mutated
                                      operations := package.operations ++ added.toList } }
      | none => []
    | none => []
  let ofProtocols := (List.range package.protocols.length).flatMap fun index =>
    match package.protocols[index]? with
    | some protocol =>
      let place := definitionName protocolNames "protocol" index
      ((protocolRegion package protocol.body).run' 0).map fun (at_, what, changed, added) =>
        let mutated : Raw.Protocol := { protocol with body := changed }
        { description := s!"{place}, instruction {at_}: {what}"
          place := s!"{place}, instruction {at_}"
          package := { package with protocols := package.protocols.set index mutated
                                    operations := package.operations ++ added.toList } }
    | none => []
  ofFunctions ++ ofProtocols

/-- Whether the core admits a package: `elaborate` accepts it, and every function and every
protocol passes the check of facts. -/
def admitted (package : Raw.Package) : Bool :=
  match elaborate package with
  | .ok typed =>
    typed.program.functions.unjustified.isEmpty && typed.program.protocols.unjustified.isEmpty
  | .error _ => false

/-- At most `count` of a list, evenly spaced from its first element. -/
def spread {α : Type} (count : Nat) (items : List α) : List α :=
  if items.length ≤ count then items
  else (List.range count).filterMap fun index => items[index * items.length / count]?

/-- The mutants of a package that the core admits, of at most `count` candidates evenly spaced
in the order of the text. -/
def mutants (package : Raw.Package) (count : Nat) : List Mutant :=
  (spread count (candidates package)).filter (admitted ·.package)

/-! ## The fourth kind: an operand replaced by another value of its type

**Replace an operand**: one operand of one instruction replaced by another value of the
context at that point that has the operand's type: in a function, any earlier value of the
type in scope; in a protocol, a value of the type that the same role holds (the holder is part
of the located type). The operands are those that elaboration reads (`elaborateLocalStep`,
`elaborateProtocolStep`): of an operation, a call, an operation the core owns, a guard, the
condition, the scrutinee, the count, the carried values and the captures of a nested region,
the value sent by an exchange, the operands of a draw, a sample and an application; and the
values that a region returns. The types are read by elaborating each instruction in its
context, so every candidate has the type its position requires; the check of facts still
refuses some. -/

/-- A local instruction with its operands, in the order that elaboration reads them, replaced. -/
def setLocalOperands : LocalStep → List Nat → LocalStep
  | .op row _, operands => .op row operands
  | .call callee _, operands => .call callee operands
  | .conditional _ _ outputs onTrue onFalse, operands =>
    .conditional (operands.headD 0) operands.tail outputs onTrue onFalse
  | .«match» declaration _ _ outputs arms, operands =>
    .«match» declaration (operands.headD 0) operands.tail outputs arms
  | .loop count carried _ collected body, operands =>
    let (count, rest) : Raw.LoopCount × List Nat := match count with
      | .static number => (.static number, operands)
      | .runtime maximum _ => (.runtime maximum (operands.headD 0), operands.tail)
    .loop count (rest.take carried.length) (rest.drop carried.length) collected body
  | .guard reason _, operands => .guard reason (operands.headD 0)
  | .literal value, _ => .literal value
  | .builtin operation _, operands => .builtin operation operands

/-- A protocol instruction with its operands, in the order that elaboration reads them,
replaced. -/
def setProtocolOperands : ProtocolStep → List Nat → ProtocolStep
  | .at role instruction, operands => .at role (setLocalOperands instruction operands)
  | .exchange sender receiver site _, operands => .exchange sender receiver site (operands.headD 0)
  | .draw owner receivers site law _, operands => .draw owner receivers site law operands
  | .sample owner site law _, operands => .sample owner site law operands
  | .«repeat» participants count carried _ collected body, operands =>
    let (count, rest) : Raw.RepeatCount × List Nat := match count with
      | .static number => (.static number, operands)
      | .runtime maximum counts => (.runtime maximum (operands.take counts.length), operands.drop counts.length)
    .«repeat» participants count (rest.take carried.length) (rest.drop carried.length) collected body
  | .choose participants tags tag _ outputs arms, operands =>
    .choose participants (operands.take tags.length) tag (operands.drop tags.length) outputs arms
  | .apply callee roleMap site _, operands => .apply callee roleMap site operands

/-- Each operand replaced by each other value of the context of its type (with its holder, in a
protocol): the description and the operands. -/
def operandChanges {α : Type} [BEq α] {Γ : List α} (scope : Zkc.Source.Scope Γ) (types : List α)
    (operands : List Nat) : List (String × List Nat) :=
  (operands.zip types).zipIdx.flatMap fun ((operand, type), position) =>
    (List.range scope.depth).filterMap fun value =>
      if value != operand && scope.type? value == some type then
        some (s!"operand {position} (value {operand}) replaced by value {value}", operands.set position value)
      else none

/-- The tables that elaboration reads an instruction against. -/
structure Tables where
  typeTable : TypeTable
  operations : List OperationSignature
  functions : List FunctionHeader
  protocols : List ProtocolHeader
  rows : Zkc.Source.Scope operations
  callees : Zkc.Source.Scope functions
  applied : Zkc.Source.Scope protocols
  deployed : Bool

mutual
  /-- The replacements of the operands of a local region in a context. -/
  partial def replaceLocal (tables : Tables) {Γ : List Ty} (scope : Zkc.Source.Scope Γ) (out : List Ty) :
      LocalRegion → StateM Nat (Found LocalRegion)
    | .ret values => do
      let number ← get
      return (operandChanges scope out values).map fun (what, changed) =>
        (number, s!"the returned {what}", LocalRegion.ret changed, none)
    | .stop _ => pure []
    | .step instruction next => do
      let number ← modifyGet fun number => (number, number + 1)
      match elaborateLocalStep tables.typeTable tables.rows tables.callees tables.deployed scope.type?
          instruction with
      | .error _ => return []
      | .ok elaborated =>
        let own := (operandChanges scope elaborated.op.arguments elaborated.operands).map fun (what, changed) =>
          (number, what, LocalRegion.step (setLocalOperands instruction changed) next, (none : Option Operation))
        let nested ← replaceLocalNested tables instruction elaborated.op.regions
        let later ← replaceLocal tables (scope.bindAll elaborated.op.results) out next
        return own ++ nested.map (fun (at_, what, changed, added) => (at_, what, .step changed next, added)) ++
          later.map fun (at_, what, changed, added) => (at_, what, .step instruction changed, added)
    | .block outputs body next => do
      match Ty.fillAll tables.typeTable outputs with
      | none => return []
      | some filled =>
        let inside ← replaceLocal tables scope filled body
        let later ← replaceLocal tables (scope.bindAll filled) out next
        return inside.map (fun (at_, what, changed, added) => (at_, what, .block outputs changed next, added)) ++
          later.map fun (at_, what, changed, added) => (at_, what, .block outputs body changed, added)

  /-- The replacements inside the nested regions of a local instruction, each region in the
  context of its signature. -/
  partial def replaceLocalNested (tables : Tables) (instruction : LocalStep)
      (signatures : List (List Ty × List Ty)) : StateM Nat (Found LocalStep) :=
    match instruction, signatures with
    | .conditional condition captures outputs onTrue onFalse, [(firstInputs, firstOutputs), (secondInputs, secondOutputs)] => do
      let first ← replaceLocal tables (Zkc.Source.Scope.empty.bindAll firstInputs) firstOutputs onTrue
      let second ← replaceLocal tables (Zkc.Source.Scope.empty.bindAll secondInputs) secondOutputs onFalse
      return first.map (fun (at_, what, changed, added) =>
          (at_, what, LocalStep.conditional condition captures outputs changed onFalse, added)) ++
        second.map fun (at_, what, changed, added) =>
          (at_, what, LocalStep.conditional condition captures outputs onTrue changed, added)
    | .«match» declaration value captures outputs arms, signatures => do
      let changed ← replaceLocalArms tables signatures arms
      return changed.map fun (at_, what, arms, added) =>
        (at_, what, LocalStep.«match» declaration value captures outputs arms, added)
    | .loop count carried captures collected body, [(inputs, outputs)] => do
      let changed ← replaceLocal tables (Zkc.Source.Scope.empty.bindAll inputs) outputs body
      return changed.map fun (at_, what, body, added) =>
        (at_, what, LocalStep.loop count carried captures collected body, added)
    | _, _ => pure []

  partial def replaceLocalArms (tables : Tables) :
      List (List Ty × List Ty) → LocalArms → StateM Nat (Found LocalArms)
    | (inputs, outputs) :: signatures, .arm region rest => do
      let here ← replaceLocal tables (Zkc.Source.Scope.empty.bindAll inputs) outputs region
      let later ← replaceLocalArms tables signatures rest
      return here.map (fun (at_, what, changed, added) => (at_, what, .arm changed rest, added)) ++
        later.map fun (at_, what, changed, added) => (at_, what, .arm region changed, added)
    | _, _ => pure []
end

mutual
  /-- The replacements of the operands of a protocol region in a context of located types. -/
  partial def replaceProtocol (tables : Tables) {Γ : List Located} (scope : Zkc.Source.Scope Γ)
      (out : List Located) : ProtocolRegion → StateM Nat (Found ProtocolRegion)
    | .ret values => do
      let number ← get
      return (operandChanges scope out values).map fun (what, changed) =>
        (number, s!"the returned {what}", ProtocolRegion.ret changed, none)
    | .stop _ => pure []
    | .step instruction next => do
      let number ← modifyGet fun number => (number, number + 1)
      match elaborateProtocolStep tables.typeTable tables.rows tables.callees tables.applied tables.deployed
          scope instruction with
      | .error _ => return []
      | .ok elaborated =>
        let own := (operandChanges scope elaborated.op.arguments elaborated.operands).map fun (what, changed) =>
          (number, what, ProtocolRegion.step (setProtocolOperands instruction changed) next, (none : Option Operation))
        let nested ← match instruction with
          | .at role localInstruction =>
            match elaborateLocalStep tables.typeTable tables.rows tables.callees tables.deployed
                (localType scope) localInstruction with
            | .ok localElaborated => do
              let changed ← replaceLocalNested tables localInstruction localElaborated.op.regions
              pure (changed.map fun (at_, what, changed, added) => (at_, what, ProtocolStep.at role changed, added))
            | .error _ => pure []
          | _ => replaceProtocolNested tables instruction elaborated.op.regions
        let later ← replaceProtocol tables (scope.bindAll elaborated.op.results) out next
        return own ++ nested.map (fun (at_, what, changed, added) => (at_, what, .step changed next, added)) ++
          later.map fun (at_, what, changed, added) => (at_, what, .step instruction changed, added)
    | .block outputs body next => do
      match Located.fillAll tables.typeTable outputs with
      | none => return []
      | some filled =>
        let inside ← replaceProtocol tables scope filled body
        let later ← replaceProtocol tables (scope.bindAll filled) out next
        return inside.map (fun (at_, what, changed, added) => (at_, what, .block outputs changed next, added)) ++
          later.map fun (at_, what, changed, added) => (at_, what, .block outputs body changed, added)

  partial def replaceProtocolNested (tables : Tables) (instruction : ProtocolStep)
      (signatures : List (List Located × List Located)) : StateM Nat (Found ProtocolStep) :=
    match instruction, signatures with
    | .«repeat» participants count carried captures collected body, [(inputs, outputs)] => do
      let changed ← replaceProtocol tables (Zkc.Source.Scope.empty.bindAll inputs) outputs body
      return changed.map fun (at_, what, body, added) =>
        (at_, what, ProtocolStep.«repeat» participants count carried captures collected body, added)
    | .choose participants tags tag captures outputs arms, signatures => do
      let changed ← replaceProtocolArms tables signatures arms
      return changed.map fun (at_, what, arms, added) =>
        (at_, what, ProtocolStep.choose participants tags tag captures outputs arms, added)
    | _, _ => pure []

  partial def replaceProtocolArms (tables : Tables) :
      List (List Located × List Located) → ProtocolArms → StateM Nat (Found ProtocolArms)
    | (inputs, outputs) :: signatures, .arm region rest => do
      let here ← replaceProtocol tables (Zkc.Source.Scope.empty.bindAll inputs) outputs region
      let later ← replaceProtocolArms tables signatures rest
      return here.map (fun (at_, what, changed, added) => (at_, what, .arm changed rest, added)) ++
        later.map fun (at_, what, changed, added) => (at_, what, .arm region changed, added)
    | _, _ => pure []
end

/-- A list in order as a scope: the last is the most recent. -/
def scopeOf {α : Type} (items : List α) : (Γ : List α) × Zkc.Source.Scope Γ :=
  items.foldl (fun found item => ⟨item :: found.1, found.2.push item⟩) ⟨[], Zkc.Source.Scope.empty⟩

/-- The label of the place of a replacement: of the values that a region returns, or of an
instruction. The probes are labelled alike. -/
def placeLabel (what : String) : String :=
  if what.startsWith "the returned" then "return" else "instruction"

/-- Every package that differs from a package by one operand replaced by another value of its
type (and holder), before admission. -/
def replacementCandidates (package : Raw.Package) : List Mutant :=
  match elaborate package with
  | .error _ => []
  | .ok typed =>
    let functionHeaders := typed.functions.reverse
    let protocolHeaders := typed.protocols.reverse
    let rows := tableScope (typed.table.map (·.signature))
    let everyFunction := scopeOf functionHeaders
    let functionNames := (package.names.map (·.functions)).getD []
    let protocolNames := (package.names.map (·.protocols)).getD []
    let ofFunctions := (List.range package.functions.length).flatMap fun index =>
      match package.functions[index]?, functionHeaders[index]? with
      | some function, some header =>
        match function.body with
        | some body =>
          let callees := scopeOf (functionHeaders.take index)
          let tables : Tables := { typeTable := typed.typeTable, operations := typed.table.map (·.signature)
                                   functions := callees.1, protocols := [], rows, callees := callees.2
                                   applied := (Zkc.Source.Scope.empty : Zkc.Source.Scope ([] : List ProtocolHeader))
                                   deployed := !header.specificationOnly }
          let place := definitionName functionNames "function" index
          ((replaceLocal tables (Zkc.Source.Scope.empty.bindAll header.inputs) header.outputs body).run' 0).map
            fun (at_, what, changed, _) =>
              { description := s!"{place}, instruction {at_}: {what}"
                place := s!"{place}, {placeLabel what} {at_}"
                package := { package with functions := package.functions.set index { function with body := some changed } } }
        | none => []
      | _, _ => []
    let ofProtocols := (List.range package.protocols.length).flatMap fun index =>
      match package.protocols[index]?, protocolHeaders[index]? with
      | some protocol, some header =>
        let applied := scopeOf (protocolHeaders.take index)
        let tables : Tables := { typeTable := typed.typeTable, operations := typed.table.map (·.signature)
                                 functions := everyFunction.1, protocols := applied.1, rows, callees := everyFunction.2
                                 applied := applied.2, deployed := !protocol.specificationOnly }
        let place := definitionName protocolNames "protocol" index
        ((replaceProtocol tables (Zkc.Source.Scope.empty.bindAll header.inputs) header.outputs protocol.body).run' 0).map
          fun (at_, what, changed, _) =>
            { description := s!"{place}, instruction {at_}: {what}"
              place := s!"{place}, {placeLabel what} {at_}"
              package := { package with protocols := package.protocols.set index { protocol with body := changed } } }
      | _, _ => []
    ofFunctions ++ ofProtocols

/-- The mutants of the fourth kind that the core admits, of at most `count` candidates evenly
spaced in the order of the text. -/
def replacements (package : Raw.Package) (count : Nat) : List Mutant :=
  (spread count (replacementCandidates package)).filter (admitted ·.package)

/-! ## Probes of reach

A **probe** of an instruction is the package with a stop just before the instruction: in a
local region a block whose body stops `refused`; in a protocol region, where no region stops, a
block in which the role that performs the instruction (the sender, the owner, the first
participant or the first role of an application) makes a `false` literal and a guard on it that
stops `refused`. A block binds nothing in the surrounding context, so no value is renumbered.
When the runs of a root under some seed end otherwise with the probe than without it, the
instruction is reached under that seed. The probes are numbered as the mutants are, and a probe
of the values a region returns is numbered with the number after the region's last
instruction, as its mutants are. -/

/-- The region that stops before a local region. -/
def localStop (region : LocalRegion) : LocalRegion := .block [] (.stop .refused) region

/-- The region in which a role stops before a protocol region, in a context of `depth` values. -/
def protocolStop (role depth : Nat) (region : ProtocolRegion) : ProtocolRegion :=
  .block [] (.step (.at role (.literal (.bool false))) (.step (.at role (.guard .refused depth)) (.ret [])))
    region

/-- The role that performs a protocol instruction, for its probe. -/
def performer : ProtocolStep → Nat
  | .at role _ => role
  | .exchange sender .. => sender
  | .draw owner .. => owner
  | .sample owner .. => owner
  | .«repeat» participants .. => participants.headD 0
  | .choose participants .. => participants.headD 0
  | .apply _ roleMap .. => roleMap.headD 0

mutual
  /-- The probes of a local region: a label and the changed region. -/
  partial def probeLocal : LocalRegion → StateM Nat (List (String × LocalRegion))
    | .ret values => do
      let number ← get
      return [(s!"return {number}", localStop (.ret values))]
    | .stop _ => pure []
    | .step instruction next => do
      let number ← modifyGet fun number => (number, number + 1)
      let nested ← probeLocalNested instruction
      let later ← probeLocal next
      return (s!"instruction {number}", localStop (.step instruction next)) ::
        (nested.map (fun (label, changed) => (label, .step changed next)) ++
          later.map fun (label, changed) => (label, .step instruction changed))
    | .block outputs body next => do
      let inside ← probeLocal body
      let later ← probeLocal next
      return inside.map (fun (label, changed) => (label, .block outputs changed next)) ++
        later.map fun (label, changed) => (label, .block outputs body changed)

  partial def probeLocalNested : LocalStep → StateM Nat (List (String × LocalStep))
    | .conditional condition captures outputs onTrue onFalse => do
      let first ← probeLocal onTrue
      let second ← probeLocal onFalse
      return first.map (fun (label, changed) => (label, LocalStep.conditional condition captures outputs changed onFalse)) ++
        second.map fun (label, changed) => (label, LocalStep.conditional condition captures outputs onTrue changed)
    | .«match» declaration value captures outputs arms => do
      let changed ← probeLocalArms arms
      return changed.map fun (label, arms) => (label, LocalStep.«match» declaration value captures outputs arms)
    | .loop count carried captures collected body => do
      let changed ← probeLocal body
      return changed.map fun (label, body) => (label, LocalStep.loop count carried captures collected body)
    | _ => pure []

  partial def probeLocalArms : LocalArms → StateM Nat (List (String × LocalArms))
    | .none => pure []
    | .arm region rest => do
      let here ← probeLocal region
      let later ← probeLocalArms rest
      return here.map (fun (label, changed) => (label, .arm changed rest)) ++
        later.map fun (label, changed) => (label, .arm region changed)
end

mutual
  /-- The probes of a protocol region in a context of located types. -/
  partial def probeProtocol (tables : Tables) {Γ : List Located} (scope : Zkc.Source.Scope Γ) (out : List Located) :
      ProtocolRegion → StateM Nat (List (String × ProtocolRegion))
    | .ret values => do
      let number ← get
      return [(s!"return {number}", protocolStop 0 scope.depth (.ret values))]
    | .stop _ => pure []
    | .step instruction next => do
      let number ← modifyGet fun number => (number, number + 1)
      match elaborateProtocolStep tables.typeTable tables.rows tables.callees tables.applied tables.deployed
          scope instruction with
      | .error _ => return []
      | .ok elaborated =>
        let nested ← match instruction with
          | .at role localInstruction => do
            let changed ← probeLocalNested localInstruction
            pure (changed.map fun (label, changed) => (label, ProtocolStep.at role changed))
          | _ => probeProtocolNested tables instruction elaborated.op.regions
        let later ← probeProtocol tables (scope.bindAll elaborated.op.results) out next
        return (s!"instruction {number}", protocolStop (performer instruction) scope.depth (.step instruction next)) ::
          (nested.map (fun (label, changed) => (label, .step changed next)) ++
            later.map fun (label, changed) => (label, .step instruction changed))
    | .block outputs body next => do
      match Located.fillAll tables.typeTable outputs with
      | none => return []
      | some filled =>
        let inside ← probeProtocol tables scope filled body
        let later ← probeProtocol tables (scope.bindAll filled) out next
        return inside.map (fun (label, changed) => (label, .block outputs changed next)) ++
          later.map fun (label, changed) => (label, .block outputs body changed)

  partial def probeProtocolNested (tables : Tables) (instruction : ProtocolStep)
      (signatures : List (List Located × List Located)) : StateM Nat (List (String × ProtocolStep)) :=
    match instruction, signatures with
    | .«repeat» participants count carried captures collected body, [(inputs, outputs)] => do
      let changed ← probeProtocol tables (Zkc.Source.Scope.empty.bindAll inputs) outputs body
      return changed.map fun (label, body) =>
        (label, ProtocolStep.«repeat» participants count carried captures collected body)
    | .choose participants tags tag captures outputs arms, signatures => do
      let changed ← probeProtocolArms tables signatures arms
      return changed.map fun (label, arms) => (label, ProtocolStep.choose participants tags tag captures outputs arms)
    | _, _ => pure []

  partial def probeProtocolArms (tables : Tables) :
      List (List Located × List Located) → ProtocolArms → StateM Nat (List (String × ProtocolArms))
    | (inputs, outputs) :: signatures, .arm region rest => do
      let here ← probeProtocol tables (Zkc.Source.Scope.empty.bindAll inputs) outputs region
      let later ← probeProtocolArms tables signatures rest
      return here.map (fun (label, changed) => (label, .arm changed rest)) ++
        later.map fun (label, changed) => (label, .arm region changed)
    | _, _ => pure []
end

/-- The probes of every instruction of every function and protocol of a package that the core
admits, each named like a mutant: the definition and the label. -/
def probes (package : Raw.Package) : List Mutant :=
  match elaborate package with
  | .error _ => []
  | .ok typed =>
    let functionHeaders := typed.functions.reverse
    let protocolHeaders := typed.protocols.reverse
    let rows := tableScope (typed.table.map (·.signature))
    let everyFunction := scopeOf functionHeaders
    let functionNames := (package.names.map (·.functions)).getD []
    let protocolNames := (package.names.map (·.protocols)).getD []
    let ofFunctions := (List.range package.functions.length).flatMap fun index =>
      match package.functions[index]? with
      | some function =>
        match function.body with
        | some body =>
          let place := definitionName functionNames "function" index
          ((probeLocal body).run' 0).map fun (label, changed) =>
            { description := s!"{place}, {label}", place := s!"{place}, {label}"
              package := { package with functions := package.functions.set index { function with body := some changed } } }
        | none => []
      | none => []
    let ofProtocols := (List.range package.protocols.length).flatMap fun index =>
      match package.protocols[index]?, protocolHeaders[index]? with
      | some protocol, some header =>
        let applied := scopeOf (protocolHeaders.take index)
        let tables : Tables := { typeTable := typed.typeTable, operations := typed.table.map (·.signature)
                                 functions := everyFunction.1, protocols := applied.1, rows, callees := everyFunction.2
                                 applied := applied.2, deployed := !protocol.specificationOnly }
        let place := definitionName protocolNames "protocol" index
        ((probeProtocol tables (Zkc.Source.Scope.empty.bindAll header.inputs) header.outputs protocol.body).run' 0).map
          fun (label, changed) =>
            { description := s!"{place}, {label}", place := s!"{place}, {label}"
              package := { package with protocols := package.protocols.set index { protocol with body := changed } } }
      | _, _ => []
    (ofFunctions ++ ofProtocols).filter (admitted ·.package)

end Zkc.Core.Mutation
