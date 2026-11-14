module

public import Zkc.Core.Json
public import Zkc.Core.Raw

public section

/-! Reading and printing raw packages as `zkc.core/0` JSON.

The reader takes the `original` program of a package. It is the only part of the tool
that is not a definition theorems speak of: it maps bytes to raw syntax.

The JSON form lists functions and protocols in one sequence and names a callee by its
position in it. The reader separates the two kinds, keeping their order, and renumbers
every callee by its position among the definitions of its kind; the printer lists the
functions before the protocols. A `call` of a protocol and an `apply` of a function are
refused here: after the separation neither can be written.

A program has two tables of declarations after its type rows:
`[stage, types, records, variants, oracles, operations, definitions]`. A record declaration
is `[use, [type…]]` with `use` one of `"free"`, `"at_most_once"`, `"exactly_once"`; a variant
declaration is the list of the payload types of its alternatives. A type names a
declaration by its number only: `["record", k]`, `["variant", k]`. The reader gives every
declaration in the tables the use and the shape of the declarations it names, and refuses
a declaration that names itself, directly or through others: the raw tables carry whole
types, so that elaboration reads a shape and needs no search. A number that names no
declaration is read as it is; elaboration refuses it.

An operation the core owns is `["builtin", name, [static…], [operand…]]` (`readBuiltin`
says what the static data of each are); a row of the table named like one is refused.

Beyond the package chapter it reads `["if", v, [v…], region, region, [type…]]`,
`["match", d, v, [v…], [region…], [type…]]` on a value of the variant `d`, with one region
per alternative from its payload and the captures, and
`["branch", [[r, v]…], [v…], region, region, [port…]]` (with their output types),
`["choose", [[r, v]…], [v…], [region…], [port…]]`, whose tag is the number of an arm,
`["case", d, [[r, v]…], [v…], [region…], [port…]]`, whose tag is a value of the variant
`d`, with one region per alternative from the payload of each participant and the captures,
and `["block", [type…], region]`, whose region continues the numbering of the surrounding
one. A `branch` is the `choose` over a condition and a `case` the `choose` over a variant.
`["opaque", flags, [type…], [type…]]` is a function known by its header only.
-/

set_option autoImplicit false

namespace Zkc.Core.Raw

open Zkc (Json)

/-- For each definition of the JSON sequence: whether it is a protocol, and its
position among the definitions of its kind. -/
abbrev Kinds := Array (Bool × Nat)

abbrev Read := Except String

def readArray (what : String) : Json → Read (Array Json)
  | .arr items => pure items
  | other => throw s!"{what}: expected an array, found {other.render}"

def readString (what : String) : Json → Read String
  | .str value => pure value
  | other => throw s!"{what}: expected a string, found {other.render}"

def readNat (what : String) : Json → Read Nat
  | .num value => pure value
  | other => throw s!"{what}: expected a non-negative integer, found {other.render}"

def readNats (what : String) (json : Json) : Read (List Nat) := do
  (← readArray what json).toList.mapM (readNat what)

/-- A type, spelled as it is named, each in one way: `"bool"`, `"nat"`, `["fin", n]`,
`["nominal", n]`, a sequence whose length is a property of the value `["seq", T]` and one of
`n` elements `["seq", T, n]`, `["tuple", [T…]]` (the empty tuple is `["tuple", []]`). A
record or a variant is the number of its declaration, `["record", k]` or `["variant", k]`:
its raw form. -/
partial def readType : Json → Read Ty
  | .str "bool" => pure .bool
  | .str "nat" => pure .nat
  | .arr #[.str "fin", bound] => return .fin (← readNat "fin bound" bound)
  | .arr #[.str "nominal", row] => return .nominal (← readNat "nominal type row" row)
  | .arr #[.str "seq", element] => return .seq (← readType element) none
  | .arr #[.str "seq", element, size] =>
      return .seq (← readType element) (some (← readNat "sequence size" size))
  | .arr #[.str "tuple", .arr components] => return .tuple (← components.toList.mapM readType)
  | .arr #[.str "record", declaration] =>
      return .record (← readNat "record declaration" declaration) .free []
  | .arr #[.str "variant", declaration] =>
      return .variant (← readNat "variant declaration" declaration) []
  | other => throw s!"malformed type {other.render}"

def readTypes (what : String) (json : Json) : Read (List Ty) := do
  (← readArray what json).toList.mapM readType

def readPort : Json → Read Located
  | .arr #[type, holder] => return ⟨← readType type, ← readNat "holder" holder⟩
  | other => throw s!"malformed port {other.render}"

def readPorts (what : String) (json : Json) : Read (List Located) := do
  (← readArray what json).toList.mapM readPort

def readStatic : Json → Read Static
  | .arr #[.str "domain", name] => return .domain (Name.ofString (← readString "domain" name))
  | .arr #[.str "nat", value] => return .nat (← readNat "nat" value)
  | .arr #[.str "type", type] => return .type (← readType type)
  | other => throw s!"malformed static argument {other.render}"

def readStatics (json : Json) : Read (List Static) := do
  (← readArray "static arguments" json).toList.mapM readStatic

/-- A sequence type: its element and its size. -/
def readSequence (name : String) (json : Json) : Read (Ty × Option Nat) := do
  match ← readType json with
  | .seq element size => pure (element, size)
  | _ => throw s!"{name}: {json.render} is not a sequence type"

/-- A sized sequence type: its element and its size. -/
def readSized (name : String) (json : Json) : Read (Ty × Nat) := do
  match ← readSequence name json with
  | (element, some size) => pure (element, size)
  | _ => throw s!"{name}: {json.render} is not a sized sequence type"

/-- An operation the core owns, from its name and its static data. The static data are the
types that carry them, of an operand (`S`) or of the result (`R`), and numbers:
`seq.length` and `seq.at` `[S]`, `seq.slice` `[S, R]`, `seq.concat` `[S, S]`, `seq.fill`,
`seq.sized` and `local.make` `[R]` (a sized sequence, a tuple or a record), `seq.unsized`
`[S]`, `nat.below` and `fin.to_nat` `[bound]`, `fin.widen` `[bound, wider]`, `local.get`
`[S, position]` (a tuple or a record), `local.variant` `[variant type, position]`, the
others `[]`. -/
def readBuiltin (name : String) (statics : Array Json) : Read Builtin := do
  if let some operation := Builtin.plain? name then
    unless statics.isEmpty do throw s!"{name}: the operation has no static data"
    return operation
  let malformed : Read Builtin :=
    throw s!"{name}: malformed static data {(Json.arr statics).render}"
  match name, statics with
  | "seq.length", #[sequence] => do
      let (element, size) ← readSequence name sequence
      pure (.seqLength element size)
  | "seq.at", #[sequence] => do
      let (element, size) ← readSequence name sequence
      pure (.seqAt element size)
  | "seq.slice", #[sequence, result] => do
      let (element, size) ← readSequence name sequence
      let (resultElement, resultSize) ← readSequence name result
      unless resultElement == element do throw s!"{name}: the result has another element type"
      pure (.seqSlice element size resultSize)
  | "seq.concat", #[first, second] => do
      let (element, left) ← readSequence name first
      let (secondElement, right) ← readSequence name second
      unless secondElement == element do throw s!"{name}: the operands have other element types"
      pure (.seqConcat element left right)
  | "seq.fill", #[result] => do
      let (element, count) ← readSized name result
      pure (.seqFill element count)
  | "seq.sized", #[result] => do
      let (element, size) ← readSized name result
      pure (.seqSized element size)
  | "seq.unsized", #[sequence] => do
      let (element, size) ← readSized name sequence
      pure (.seqUnsized element size)
  | "local.make", #[result] => do
      match ← readType result with
      | .seq element (some count) => pure (.seqMake element count)
      | .tuple components => pure (.tupleMake components)
      | .record declaration _ _ => pure (.recordMake declaration)
      | _ => throw s!"{name}: {result.render} is neither a sized sequence, a tuple nor a record type"
  | "nat.below", #[bound] => return .natBelow (← readNat name bound)
  | "fin.to_nat", #[bound] => return .finToNat (← readNat name bound)
  | "fin.widen", #[bound, wider] => return .finWiden (← readNat name bound) (← readNat name wider)
  | "local.get", #[value, position] => do
      match ← readType value with
      | .tuple components => return .tupleGet components (← readNat name position)
      | .record declaration _ _ => return .recordGet declaration (← readNat name position)
      | _ => throw s!"{name}: {value.render} is neither a tuple nor a record type"
  | "local.variant", #[variant, position] => do
      match ← readType variant with
      | .variant declaration _ => return .variantMake declaration (← readNat name position)
      | _ => throw s!"{name}: {variant.render} is not a variant type"
  | _, _ =>
      if builtinNames.contains name then malformed
      else throw s!"{name} is not an operation of the core"

/-- The kind of the row `name`. A restricted row that names its domain row is
`["restricted", d]`, with the number of that row. The kind `partial` is refused: a row is
pure, restricted or sampling. -/
def readKind (name : String) : Json → Read OperationKind
  | .str "pure" => pure .pure
  | .str "restricted" => pure (.restricted none)
  | .arr #[.str "restricted", domain] => return .restricted (some (← readNat "domain row" domain))
  | .str "sampling" => pure .sampling
  | .str "partial" =>
      throw s!"operation row {name}: the kind \"partial\" is not a kind of the core; a row is pure, restricted or sampling"
  | other => throw s!"operation row {name}: unknown operation kind {other.render}"

def readStop : Json → Read PIR.Stop
  | .str "reject" => pure .reject
  | .str "abort" => pure .abort
  | .str "exhausted" => pure .exhausted
  | .str "incomplete" => pure .incomplete
  | .str "refused" => pure .refused
  | .str "undefined" => pure .undefined
  | other => throw s!"unknown stop reason {other.render}"

def readReason : Json → Read Reason
  | .str "reject" => pure .reject
  | .str "abort" => pure .abort
  | .str "exhausted" => pure .exhausted
  | .str "refused" => pure .refused
  | other => throw s!"unknown guard reason {other.render}"

/-- The count of a loop from the two positions after the instruction's name. The first is
`"static"` when the second is the count itself; otherwise the second is the number of the
count's value and the first its maximum, or `null` for none. -/
def readLoopCount (bound count : Json) : Read Raw.LoopCount := do
  match bound with
  | .str "static" => return .static (← readNat "count" count)
  | .null => return .runtime none (← readNat "count" count)
  | maximum => return .runtime (some (← readNat "maximum" maximum)) (← readNat "count" count)

/-- The participants and the count of a `repeat` from the two positions after the
instruction's name. With `["static", n]` in the second the participants are roles and the
count is `n`; otherwise each participant is given with the value that holds its count, and
the second position is the maximum. -/
def readRepeatCount (participants : Array Json) (bound : Json) :
    Read (List Nat × Raw.RepeatCount) := do
  match bound with
  | .arr #[.str "static", count] =>
      return (← participants.toList.mapM (readNat "participant"),
        .static (← readNat "count" count))
  | maximum =>
      let pairs ← participants.toList.mapM fun
        | .arr #[role, count] => return (← readNat "participant" role, ← readNat "count" count)
        | other => throw s!"malformed participant {other.render}"
      return (pairs.map (·.1), .runtime (← readNat "maximum" maximum) (pairs.map (·.2)))

/-- The parts of a region: its instructions and its returned values. -/
def regionParts : Json → Read (Array Json × List Nat)
  | .arr #[.arr instructions, returned] => return (instructions, ← readNats "returned values" returned)
  | other => throw s!"malformed region {other.render}"

/-- The position of a called function among the functions. -/
def readFunction (kinds : Kinds) (json : Json) : Read Nat := do
  let row ← readNat "callee" json
  match kinds[row]? with
  | some (false, position) => pure position
  | some (true, _) => throw s!"call of definition {row}, which is not a function"
  | none => pure row

/-- The position of an applied protocol among the protocols. -/
def readProtocol (kinds : Kinds) (json : Json) : Read Nat := do
  let row ← readNat "callee" json
  match kinds[row]? with
  | some (true, position) => pure position
  | some (false, _) => throw s!"apply of definition {row}, which is not a protocol"
  | none => pure row

mutual
  partial def readLocalStep (kinds : Kinds) : Json → Read LocalStep
    | .arr #[.str "op", row, operands] =>
        return .op (← readNat "operation row" row) (← readNats "operands" operands)
    | .arr #[.str "call", callee, operands] =>
        return .call (← readFunction kinds callee) (← readNats "operands" operands)
    | .arr #[.str "if", condition, captures, onTrue, onFalse, outputs] =>
        return .conditional (← readNat "condition" condition) (← readNats "captures" captures)
          (← readTypes "outputs" outputs) (← readLocalRegion kinds onTrue)
          (← readLocalRegion kinds onFalse)
    | .arr #[.str "match", declaration, value, captures, .arr arms, outputs] =>
        return .match (← readNat "variant declaration" declaration) (← readNat "value" value)
          (← readNats "captures" captures) (← readTypes "outputs" outputs)
          (.ofList (← arms.toList.mapM (readLocalRegion kinds)))
    | .arr #[.str "loop", bound, count, carried, captures, body] =>
        return .loop (← readLoopCount bound count) (← readNats "carried" carried)
          (← readNats "captures" captures) [] (← readLocalRegion kinds body)
    | .arr #[.str "loop", bound, count, carried, captures, body, collected] => do
        let collected ← readTypes "collected" collected
        if collected.isEmpty then
          throw "loop: a loop that collects nothing does not list collected types"
        return .loop (← readLoopCount bound count) (← readNats "carried" carried)
          (← readNats "captures" captures) collected (← readLocalRegion kinds body)
    | .arr #[.str "guard", reason, condition] =>
        return .guard (← readReason reason) (← readNat "condition" condition)
    | .arr #[.str "literal", .arr #[.str "nat", value]] =>
        return .literal (.nat (← readNat "literal" value))
    | .arr #[.str "literal", .arr #[.str "bool", value]] =>
        return .literal (.bool ((← readNat "literal" value) != 0))
    | .arr #[.str "literal", .arr #[.str "fin", bound, value]] =>
        return .literal (.fin (← readNat "literal bound" bound) (← readNat "literal" value))
    | .arr #[.str "literal", .arr #[.str "nominal", row, data]] =>
        return .literal (.nominal (← readNat "literal type" row) (← readNats "literal data" data))
    | .arr #[.str "literal", .arr #[.str "bytes", data]] =>
        return .literal (.bytes (← readNats "literal bytes" data))
    | .arr #[.str "builtin", .str name, .arr statics, operands] =>
        return .builtin (← readBuiltin name statics) (← readNats "operands" operands)
    | other => throw s!"unsupported local instruction {other.render}"

  partial def readLocalRegion (kinds : Kinds) (json : Json) : Read LocalRegion := do
    let (instructions, returned) ← regionParts json
    let mut region : LocalRegion := .ret returned
    let mut count := instructions.size
    if let some (.arr #[.str "stop", reason]) := instructions.back? then
      region := .stop (← readStop reason)
      count := count - 1
    for index in [0:count] do
      match instructions[count - 1 - index]! with
      | .arr #[.str "block", outputs, body] =>
          region := .block (← readTypes "outputs" outputs) (← readLocalRegion kinds body) region
      | instruction => region := .step (← readLocalStep kinds instruction) region
    pure region
end

mutual
  partial def readProtocolStep (kinds : Kinds) : Json → Read ProtocolStep
    | .arr #[.str "at", role, instruction] =>
        return .at (← readNat "role" role) (← readLocalStep kinds instruction)
    | .arr #[.str "exchange", sender, receiver, site, value] =>
        return .exchange (← readNat "sender" sender) (← readNat "receiver" receiver)
          (← readNat "site" site) (← readNat "value" value)
    | .arr #[.str "draw", owner, receivers, site, law, operands] =>
        return .draw (← readNat "owner" owner) (← readNats "receivers" receivers)
          (← readNat "site" site) (← readNat "law" law) (← readNats "operands" operands)
    | .arr #[.str "sample", owner, site, law, operands] =>
        return .sample (← readNat "owner" owner) (← readNat "site" site) (← readNat "law" law)
          (← readNats "operands" operands)
    | .arr #[.str "repeat", .arr participants, bound, carried, captures, body] => do
        let (roles, count) ← readRepeatCount participants bound
        return .repeat roles count (← readNats "carried" carried)
          (← readNats "captures" captures) [] (← readProtocolRegion kinds body)
    | .arr #[.str "repeat", .arr participants, bound, carried, captures, body, collected] => do
        let (roles, count) ← readRepeatCount participants bound
        let collected ← readPorts "collected" collected
        if collected.isEmpty then
          throw "repeat: a repeat that collects nothing does not list collected values"
        return .repeat roles count (← readNats "carried" carried)
          (← readNats "captures" captures) collected (← readProtocolRegion kinds body)
    | .arr #[.str "branch", .arr participants, captures, onTrue, onFalse, outputs] => do
        let pairs ← participants.toList.mapM fun
          | .arr #[role, condition] =>
              return (← readNat "participant" role, ← readNat "condition" condition)
          | other => throw s!"malformed participant {other.render}"
        return .choose (pairs.map (·.1)) (pairs.map (·.2)) .condition
          (← readNats "captures" captures) (← readPorts "outputs" outputs)
          (.ofList [← readProtocolRegion kinds onFalse, ← readProtocolRegion kinds onTrue])
    | .arr #[.str "choose", .arr participants, captures, .arr arms, outputs] => do
        let pairs ← participants.toList.mapM fun
          | .arr #[role, tag] => return (← readNat "participant" role, ← readNat "tag" tag)
          | other => throw s!"malformed participant {other.render}"
        return .choose (pairs.map (·.1)) (pairs.map (·.2)) (.arm arms.size)
          (← readNats "captures" captures) (← readPorts "outputs" outputs)
          (.ofList (← arms.toList.mapM (readProtocolRegion kinds)))
    | .arr #[.str "case", declaration, .arr participants, captures, .arr arms, outputs] => do
        let pairs ← participants.toList.mapM fun
          | .arr #[role, tag] => return (← readNat "participant" role, ← readNat "tag" tag)
          | other => throw s!"malformed participant {other.render}"
        return .choose (pairs.map (·.1)) (pairs.map (·.2))
          (.alternative (← readNat "variant declaration" declaration) [])
          (← readNats "captures" captures) (← readPorts "outputs" outputs)
          (.ofList (← arms.toList.mapM (readProtocolRegion kinds)))
    | .arr #[.str "apply", callee, roleMap, site, operands] =>
        return .apply (← readProtocol kinds callee) (← readNats "role map" roleMap)
          (← readNat "site" site) (← readNats "operands" operands)
    | other => throw s!"unsupported protocol instruction {other.render}"

  partial def readProtocolRegion (kinds : Kinds) (json : Json) : Read ProtocolRegion := do
    let (instructions, returned) ← regionParts json
    let mut region : ProtocolRegion := .ret returned
    let mut count := instructions.size
    if let some (.arr #[.str "stop", reason]) := instructions.back? then
      region := .stop (← readStop reason)
      count := count - 1
    for index in [0:count] do
      match instructions[count - 1 - index]! with
      | .arr #[.str "block", outputs, body] =>
          region := .block (← readPorts "outputs" outputs) (← readProtocolRegion kinds body) region
      | instruction => region := .step (← readProtocolStep kinds instruction) region
    pure region
end

def readFlags (json : Json) : Read Bool := do
  let flags ← readNat "flags" json
  unless flags < 2 do throw s!"unknown definition flags {flags}"
  pure (flags == 1)

def readAgreement : Json → Read Agreement
  | .arr #[side, ports] => do
      let side ← readNat "agreement side" side
      unless side < 2 do throw s!"side {side} is neither 0 (inputs) nor 1 (outputs)"
      return ⟨side == 1, ← readNats "agreement ports" ports⟩
  | other => throw s!"malformed agreement {other.render}"

/-- A definition of the JSON sequence. -/
inductive Read.Definition where
  | function (function : Function)
  | protocol (protocol : Protocol)

def readDefinition (kinds : Kinds) : Json → Read Read.Definition
  | .arr #[.str "function", flags, inputs, outputs, body] =>
      return .function ⟨← readFlags flags, ← readTypes "inputs" inputs,
        ← readTypes "outputs" outputs, some (← readLocalRegion kinds body)⟩
  | .arr #[.str "opaque", flags, inputs, outputs] =>
      return .function ⟨← readFlags flags, ← readTypes "inputs" inputs,
        ← readTypes "outputs" outputs, none⟩
  | .arr #[.str "protocol", flags, roles, inputs, outputs, agreements, body] =>
      return .protocol ⟨← readFlags flags, ← readNat "roles" roles, ← readPorts "inputs" inputs,
        ← readPorts "outputs" outputs,
        ← (← readArray "agreements" agreements).toList.mapM readAgreement,
        ← readProtocolRegion kinds body⟩
  | other => throw s!"unsupported definition {(other.render.take 80).toString}"

/-- The kind of every definition and its position among the definitions of its kind. -/
def readKinds (definitions : Array Json) : Kinds := Id.run do
  let mut kinds : Kinds := #[]
  let mut functions := 0
  let mut protocols := 0
  for definition in definitions do
    match definition with
    | .arr items =>
        if let some (.str "protocol") := items[0]? then
          kinds := kinds.push (true, protocols)
          protocols := protocols + 1
        else
          kinds := kinds.push (false, functions)
          functions := functions + 1
    | _ =>
        kinds := kinds.push (false, functions)
        functions := functions + 1
  return kinds

def readOperation : Json → Read Operation
  | .arr #[name, statics, kind, inputs, outputs] => do
      let name ← readString "name" name
      if builtinNames.contains name then
        throw s!"operation row {name}: {name} is an operation of the core, not a row of the table"
      return ⟨⟨Name.ofString name, ← readStatics statics⟩,
        ⟨← readTypes "inputs" inputs, ← readTypes "outputs" outputs, ← readKind name kind⟩⟩
  | other => throw s!"malformed operation row {other.render}"

def readUse : Json → Read Use
  | .str "free" => pure .free
  | .str "at_most_once" => pure .atMostOnce
  | .str "exactly_once" => pure .exactlyOnce
  | other => throw s!"unknown use {other.render}"

def readRecord : Json → Read RecordDeclaration
  | .arr #[use, fields] => return ⟨← readUse use, ← readTypes "fields" fields⟩
  | other => throw s!"malformed record declaration {other.render}"

def readVariant (json : Json) : Read VariantDeclaration :=
  return ⟨← readTypes "alternatives" json⟩

def readTypeRow : Json → Read CatalogueRow
  | .arr #[name, statics] =>
      return ⟨Name.ofString (← readString "type constructor" name), ← readStatics statics⟩
  | other => throw s!"malformed type row {other.render}"

/-- The entries of a table that belong to the definitions of one kind. -/
def ofKind {α : Type} (kinds : Kinds) (protocols : Bool) (entries : List α) : List α :=
  (entries.zip kinds.toList).filterMap fun (entry, kind) =>
    if kind.1 == protocols then some entry else none

def readNames (kinds : Kinds) : Json → Read (Option Names)
  | .arr #[] => pure none
  | .arr #[definitions, roles, sites] => do
      let strings (json : Json) : Read (List String) := do
        (← readArray "names" json).toList.mapM (readString "name")
      let definitions ← strings definitions
      let roles ← (← readArray "role names" roles).toList.mapM strings
      let sites ← (← readArray "site names" sites).toList.mapM strings
      unless definitions.length == kinds.size && roles.length == kinds.size &&
          sites.length == kinds.size do
        throw "a table of names does not have one entry per definition"
      return some ⟨ofKind kinds false definitions, ofKind kinds true definitions,
        ofKind kinds true roles, ofKind kinds true sites⟩
  | other => throw s!"malformed names {other.render}"

/-- The `original` program of a package. -/
def readPackage : Json → Read Package
  | .arr #[.str "zkc.core/0", .arr programs, _, _, _, names] => do
      for program in programs do
        if let .arr #[.str "original", types, records, variants, .arr #[], operations,
            .arr definitions] := program then
          let kinds := readKinds definitions
          let read ← definitions.toList.mapM (readDefinition kinds)
          let (records, variants) ← declaredTables
            (← (← readArray "records" records).toList.mapM readRecord)
            (← (← readArray "variants" variants).toList.mapM readVariant)
          return ⟨← (← readArray "types" types).toList.mapM readTypeRow, records, variants,
            ← (← readArray "operations" operations).toList.mapM readOperation,
            read.filterMap fun | .function function => some function | .protocol _ => none,
            read.filterMap fun | .protocol protocol => some protocol | .function _ => none,
            ← readNames kinds names⟩
      throw "the package has no original program without oracle rows"
  | _ => throw "malformed package envelope"

def parsePackage (source : String) : Read Package := do
  readPackage (← Json.parse source)

/-! ## Printing -/

def nats (values : List Nat) : Json := .arr (values.map fun (value : Nat) => Json.num value).toArray

partial def printType : Ty → Json
  | .bool => "bool"
  | .nat => "nat"
  | .fin bound => .arr #["fin", bound]
  | .nominal row => .arr #["nominal", row]
  | .seq element none => .arr #["seq", printType element]
  | .seq element (some size) => .arr #["seq", printType element, size]
  | .tuple components => .arr #["tuple", .arr (components.map printType).toArray]
  | .record declaration _ _ => .arr #["record", declaration]
  | .variant declaration _ => .arr #["variant", declaration]

def printTypes (types : List Ty) : Json := .arr (types.map printType).toArray

def printPorts (ports : List Located) : Json :=
  .arr (ports.map fun port => Json.arr #[printType port.type, port.holder]).toArray

def printStatics (statics : List Static) : Json :=
  .arr (statics.map fun
    | .domain name => Json.arr #["domain", name.toString]
    | .nat value => Json.arr #["nat", value]
    | .type type => Json.arr #["type", printType type]).toArray

/-- The name and the static data of an operation the core owns, as `readBuiltin` reads them. -/
def printBuiltin (operation : Builtin) : Json × Json :=
  let data : Builtin → List Json
    | .seqLength element size | .seqAt element size => [printType (.seq element size)]
    | .seqSlice element size result =>
        [printType (.seq element size), printType (.seq element result)]
    | .seqConcat element left right =>
        [printType (.seq element left), printType (.seq element right)]
    | .seqFill element count | .seqSized element count | .seqMake element count =>
        [printType (.seq element (some count))]
    | .seqUnsized element size => [printType (.seq element (some size))]
    | .natBelow bound | .finToNat bound => [bound]
    | .finWiden bound wider => [bound, wider]
    | .tupleMake components => [printType (.tuple components)]
    | .tupleGet components position => [printType (.tuple components), position]
    | .recordMake declaration => [printType (.record declaration .free [])]
    | .recordGet declaration position => [printType (.record declaration .free []), position]
    | .variantMake declaration position => [printType (.variant declaration []), position]
    | _ => []
  (operation.name, .arr (data operation).toArray)

def printStop : PIR.Stop → Json
  | .reject => "reject" | .abort => "abort" | .exhausted => "exhausted"
  | .incomplete => "incomplete" | .refused => "refused" | .undefined => "undefined"

/-- The two positions of a loop's count: see `readLoopCount`. -/
def printLoopCount : Raw.LoopCount → Json × Json
  | .static count => ("static", count)
  | .runtime none value => (.null, value)
  | .runtime (some maximum) value => (maximum, value)

def printReason : Reason → Json
  | .reject => "reject" | .abort => "abort" | .exhausted => "exhausted" | .refused => "refused"

mutual
  partial def printLocalStep : LocalStep → Json
    | .op row operands => .arr #["op", row, nats operands]
    | .call callee operands => .arr #["call", callee, nats operands]
    | .conditional condition captures outputs onTrue onFalse =>
        .arr #["if", condition, nats captures, printLocalRegion onTrue, printLocalRegion onFalse,
          printTypes outputs]
    | .match declaration value captures outputs arms =>
        .arr #["match", declaration, value, nats captures,
          .arr (arms.toList.map printLocalRegion).toArray, printTypes outputs]
    | .loop count carried captures collected body =>
        let (bound, value) := printLoopCount count
        let parts : Array Json :=
          #["loop", bound, value, nats carried, nats captures, printLocalRegion body]
        .arr (if collected.isEmpty then parts else parts.push (printTypes collected))
    | .guard reason condition => .arr #["guard", printReason reason, condition]
    | .literal (.nat value) => .arr #["literal", .arr #["nat", value]]
    | .literal (.bool value) => .arr #["literal", .arr #["bool", if value then 1 else 0]]
    | .literal (.fin bound value) => .arr #["literal", .arr #["fin", bound, value]]
    | .literal (.nominal row data) => .arr #["literal", .arr #["nominal", row, nats data]]
    | .literal (.bytes data) => .arr #["literal", .arr #["bytes", nats data]]
    | .builtin operation operands =>
        let (name, statics) := printBuiltin operation
        .arr #["builtin", name, statics, nats operands]

  partial def printLocalRegion (region : LocalRegion) : Json := Id.run do
    let mut instructions := #[]
    let mut current := region
    repeat
      match current with
      | .ret values => return .arr #[.arr instructions, nats values]
      | .stop reason => return .arr #[.arr (instructions.push (.arr #["stop", printStop reason])), nats []]
      | .step instruction next =>
          instructions := instructions.push (printLocalStep instruction)
          current := next
      | .block outputs body next =>
          instructions := instructions.push (.arr #["block", printTypes outputs, printLocalRegion body])
          current := next
    return .null
end

mutual
  /-- `functions` is the number of functions: a protocol is printed with its position
  after them. -/
  partial def printProtocolStep (functions : Nat) : ProtocolStep → Json
    | .at role instruction => .arr #["at", role, printLocalStep instruction]
    | .exchange sender receiver site value => .arr #["exchange", sender, receiver, site, value]
    | .draw owner receivers site law operands =>
        .arr #["draw", owner, nats receivers, site, law, nats operands]
    | .sample owner site law operands => .arr #["sample", owner, site, law, nats operands]
    | .repeat participants count carried captures collected body =>
        -- A repeat that collects nothing is written without a list of collected values.
        let (holders, bound) : Json × Json := match count with
          | .static count => (nats participants, .arr #["static", count])
          | .runtime maximum counts =>
              (.arr ((participants.zip counts).map fun (role, count) =>
                Json.arr #[role, count]).toArray, maximum)
        let parts : Array Json := #["repeat", holders, bound, nats carried, nats captures,
          printProtocolRegion functions body]
        .arr (if collected.isEmpty then parts else parts.push (printPorts collected))
    | .choose participants tags tag captures outputs arms =>
        let holders := Json.arr ((participants.zip tags).map fun (role, tag) =>
          Json.arr #[role, tag]).toArray
        match tag, arms.toList with
        | .condition, [onFalse, onTrue] =>
            .arr #["branch", holders, nats captures, printProtocolRegion functions onTrue,
              printProtocolRegion functions onFalse, printPorts outputs]
        | .alternative declaration _, regions =>
            .arr #["case", declaration, holders, nats captures,
              .arr (regions.map (printProtocolRegion functions)).toArray, printPorts outputs]
        | _, regions =>
            .arr #["choose", holders, nats captures,
              .arr (regions.map (printProtocolRegion functions)).toArray, printPorts outputs]
    | .apply callee roleMap site operands =>
        .arr #["apply", functions + callee, nats roleMap, site, nats operands]

  partial def printProtocolRegion (functions : Nat) (region : ProtocolRegion) : Json := Id.run do
    let mut instructions := #[]
    let mut current := region
    repeat
      match current with
      | .ret values => return .arr #[.arr instructions, nats values]
      | .stop reason => return .arr #[.arr (instructions.push (.arr #["stop", printStop reason])), nats []]
      | .step instruction next =>
          instructions := instructions.push (printProtocolStep functions instruction)
          current := next
      | .block outputs body next =>
          instructions := instructions.push
            (.arr #["block", printPorts outputs, printProtocolRegion functions body])
          current := next
    return .null
end

def printFunction (function : Function) : Json :=
  match function.body with
  | some body =>
      .arr #["function", if function.specificationOnly then 1 else 0, printTypes function.inputs,
        printTypes function.outputs, printLocalRegion body]
  | none =>
      .arr #["opaque", if function.specificationOnly then 1 else 0, printTypes function.inputs,
        printTypes function.outputs]

def printProtocol (functions : Nat) (protocol : Protocol) : Json :=
  .arr #["protocol", if protocol.specificationOnly then 1 else 0, protocol.roles,
    printPorts protocol.inputs, printPorts protocol.outputs,
    .arr (protocol.agreements.map fun agreement =>
      Json.arr #[if agreement.overOutputs then 1 else 0, nats agreement.ports]).toArray,
    printProtocolRegion functions protocol.body]

def strings (values : List String) : Json := .arr (values.map Json.str).toArray

def printUse : Use → Json
  | .free => "free" | .atMostOnce => "at_most_once" | .exactlyOnce => "exactly_once"

def printPackage (package : Package) : Json :=
  .arr #["zkc.core/0",
    .arr #[.arr #["original",
      .arr (package.types.map fun row =>
        Json.arr #[row.name.toString, printStatics row.statics]).toArray,
      .arr (package.records.map fun record =>
        Json.arr #[printUse record.use, printTypes record.fields]).toArray,
      .arr (package.variants.map fun variant => printTypes variant.alternatives).toArray,
      .arr #[],
      .arr (package.operations.map fun row =>
        Json.arr #[row.identity.name.toString, printStatics row.identity.statics,
          match row.signature.kind with
          | .pure => "pure"
          | .restricted none => "restricted"
          | .restricted (some domain) => .arr #["restricted", domain]
          | .sampling => "sampling",
          printTypes row.signature.inputs, printTypes row.signature.outputs]).toArray,
      .arr ((package.functions.map printFunction ++
        package.protocols.map (printProtocol package.functions.length)).toArray)]],
    .arr #[], .arr #[], .arr #[],
    match package.names with
    | none => .arr #[]
    | some names =>
        let none := package.functions.map fun _ => strings []
        .arr #[strings (names.functions ++ names.protocols),
          .arr (none ++ names.roles.map strings).toArray,
          .arr (none ++ names.sites.map strings).toArray]]

end Zkc.Core.Raw
