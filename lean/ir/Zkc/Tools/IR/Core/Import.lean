module

public import Zkc.IR.Core.Meaning
public meta import Zkc.IR.Core.Meaning
public meta import Lean.Elab.Command
public meta import Lean.Data.Json.Parser
public meta import Lean.Compiler.NoncomputableAttr

/-! The importer of `zkc.core/0` packages.

`import_core name from "<json>"` reads one stage of a package and adds

- `name.catalogue`: the catalogue identities of the type rows and operation rows, as
  data;
- `name.operations`: the operation table;
- `name.row.«identity»`, per operation row: the variable of the row in the table,
  named by the row's catalogue identity;
- `name.<definition>.definition`, per package definition: the definition, built
  directly as a typed `Region` term;
- `name.<definition>.wellFormed`, per package definition: the proof that the
  definition has no residual violation;
- `name.<definition>`, per package definition: the program up to and including that
  definition, a `Zkc.Core.Program`;
- `name.<definition>.table`, per definition: the equation between the table of the
  program up to the definition and the definition's own meaning followed by the
  table before it;
- `name.<definition>.entry.<callee>`, per definition and earlier definition it calls
  or applies: the equation between the callee's entry in the definition's table and
  the callee's own meaning.

The kernel checks each declaration when it is added: it type-checks a definition,
then decides its residual conditions. Typing fixes operand types and
holders, closed regions, references to earlier definitions and to operation rows
(with the row's signature and kind), authored guard reasons, branch outputs held by
participants, the one type of an agreement's copies, and the prohibition on a
deployed definition using a specification-only one. The residual conditions are
decided by the kernel through the `Definition.violation = none` proof that
`Program.snoc` requires.

The importer reads JSON, infers the types of values, and refuses a package with a
clear message before the kernel sees it. Its checks of the residual conditions call
the model's own condition lists on the package's numbers. When the kernel refuses a
definition, the importer reports the cause: the kernel's account of the ill-typed
term, or the residual condition that the kernel evaluates `Definition.violation`
to.

A row's catalogue identity is its name applied to its static arguments. It is
rendered as `name` or `name(static, …)`, a static as `domain d`, `nat n` or
`type T`, a nominal type as `constructor(static, …)` and a structural type as
`unit`, `bool`, `index`, `array[T]`, `tuple[T, …]` or `variant[T, …]`. Catalogue
names use letters, digits, `.`, `_`, `-` and `/`, so the rendering is injective. No
kernel-evaluated term compares a string.

Options after `with`:
- `kernel_only`: skip every check that the kernel also decides, so that a package
  that violates one reaches the kernel, which refuses it;
- `profile`: log, for every definition, the time of term construction, of the
  kernel's type check, of its decision of the residual conditions, and of the table
  and entry equations.

`fixture "<path>"` compares the embedded package with a JSON file, as JSON values.
`from file "<path>"` reads the package from a file. Paths are relative to the
working directory of the Lean process, the package root under Lake.
-/

public meta section

open Lean Elab Command
open Zkc.Core

namespace Zkc.Tools.Core

/-! ## JSON reading -/

abbrev Read := Except String

def located {α : Type} (what : String) (action : Read α) : Read α :=
  action.mapError fun message => s!"{what}: {message}"

def readArray (what : String) : Json → Read (Array Json)
  | .arr items => pure items
  | other => throw s!"{what}: expected an array, found {other.compress}"

def readString (what : String) : Json → Read String
  | .str value => pure value
  | other => throw s!"{what}: expected a string, found {other.compress}"

def readNat (what : String) : Json → Read Nat
  | .num ⟨mantissa, 0⟩ =>
      if mantissa ≥ 0 then pure mantissa.toNat
      else throw s!"{what}: expected a non-negative integer, found {mantissa}"
  | other => throw s!"{what}: expected a non-negative integer, found {other.compress}"

def readNats (what : String) (json : Json) : Read (List Nat) := do
  (← readArray what json).toList.mapM (readNat what)

def readFields (what : String) (count : Nat) (json : Json) : Read (Array Json) := do
  let items ← readArray what json
  unless items.size == count do
    throw s!"{what}: expected {count} fields, found {items.size}"
  pure items

/-! ## Types -/

partial def readType (nominals : Nat) : Json → Read Ty
  | .str "unit" => pure .unit
  | .str "bool" => pure .bool
  | .str "index" => pure .index
  | .arr #[.str "nominal", row] => do
      let row ← readNat "nominal type row" row
      unless row < nominals do
        throw s!"dangling reference: nominal type row {row} (the type table has {nominals} rows)"
      pure (.nominal row)
  | .arr #[.str "array", element] => return .array (← readType nominals element)
  | .arr #[.str "tuple", .arr components] =>
      return .tuple (← components.toList.mapM (readType nominals))
  | .arr #[.str "variant", .arr alternatives] => do
      match ← alternatives.toList.mapM (readType nominals) with
      | first :: rest => pure (.variant first rest)
      | [] => throw "a variant type has no alternative"
  | .arr #[.str "oracle", _] => throw "oracle handle types are not supported by this importer"
  | other => throw s!"malformed type {other.compress}"

partial def renderTy : Ty → String
  | .unit => "unit"
  | .bool => "bool"
  | .index => "index"
  | .nominal row => s!"nominal({row})"
  | .array element => s!"array({renderTy element})"
  | .tuple components => "tuple(" ++ ", ".intercalate (components.map renderTy) ++ ")"
  | .variant first rest => "variant(" ++ ", ".intercalate ((first :: rest).map renderTy) ++ ")"

/-! ## Decoded package -/

/-- A catalogue name: letters, digits, `.`, `_`, `-` and `/`. -/
def catalogueName (what : String) (json : Json) : Read String := do
  let name ← readString what json
  if name.isEmpty then throw s!"{what}: empty name"
  unless name.all fun c => c.isAlphanum || c == '.' || c == '_' || c == '-' || c == '/' do
    throw s!"{what}: the name {name.quote} uses a character other than letters, digits and . _ - /"
  pure name

/-- A static argument. A type argument names nominal rows below `nominals`. -/
def readStatic (nominals : Nat) : Json → Read Static
  | .arr #[.str "domain", name] => return .domain (← catalogueName "domain" name)
  | .arr #[.str "nat", value] => return .nat (← readNat "nat" value)
  | .arr #[.str "type", type] => return .type (← readType nominals type)
  | other => throw s!"malformed static argument {other.compress}"

def readStatics (nominals : Nat) (json : Json) : Read (List Static) := do
  (← readArray "static arguments" json).toList.mapM (readStatic nominals)

/-- The rendering of a type inside a catalogue identity; `nominal` renders the
nominal rows. -/
partial def renderIdentityType (nominal : Array String) : Ty → String
  | .unit => "unit"
  | .bool => "bool"
  | .index => "index"
  | .nominal row => nominal[row]!
  | .array element => s!"array[{renderIdentityType nominal element}]"
  | .tuple components =>
      "tuple[" ++ ", ".intercalate (components.map (renderIdentityType nominal)) ++ "]"
  | .variant first rest =>
      "variant[" ++ ", ".intercalate ((first :: rest).map (renderIdentityType nominal)) ++ "]"

def renderStatics (nominal : Array String) (statics : List Static) : String :=
  ", ".intercalate <| statics.map fun
    | .domain name => s!"domain {name}"
    | .nat value => s!"nat {value}"
    | .type type => s!"type {renderIdentityType nominal type}"

structure OperationEntry where
  catalogue : CatalogueRow
  /-- The rendered catalogue identity: the local name of the row's constant. -/
  identity : String
  kind : OperationKind
  inputs : List Ty
  outputs : List Ty

/-- One agreement of a package: whether it is over the outputs, and its ports. -/
structure AgreementEntry where
  overOutputs : Bool
  ports : List Nat

inductive Signature where
  | function (inputs outputs : List Ty)
  | protocol (roles : Nat) (inputs outputs : List Located) (agreements : List AgreementEntry)
  deriving Inhabited

structure DefinitionEntry where
  signature : Signature
  specificationOnly : Bool
  body : Json
  deriving Inhabited

structure Names where
  definitions : Array String := #[]
  roles : Array (Array String) := #[]
  sites : Array (Array String) := #[]

structure Decoded where
  stage : String
  nominals : Nat
  types : Array CatalogueRow
  operations : Array OperationEntry
  definitions : Array DefinitionEntry
  names : Names

def stages : List String := ["original", "unfolded", "committed", "constructed"]

def readKind : Json → Read OperationKind
  | .str "pure" => pure .pure
  | .str "partial" => pure .partial
  | .str "sampling" => pure .sampling
  | other => throw s!"unknown operation kind {other.compress}"

/-- A type row: a constructor applied to static arguments that name earlier rows. -/
def readTypeRow (row : Nat) (json : Json) : Read CatalogueRow :=
  located s!"type row {row}" do
    let fields ← readFields "type row" 2 json
    pure { name := ← catalogueName "type constructor" fields[0]!,
           statics := ← readStatics row fields[1]! }

def readOperation (nominals : Nat) (identities : Array String) (row : Nat) (json : Json) :
    Read OperationEntry :=
  located s!"operation row {row}" do
    let fields ← readFields "operation row" 5 json
    let name ← catalogueName "name" fields[0]!
    let statics ← readStatics nominals fields[1]!
    let kind ← readKind fields[2]!
    let inputs ← (← readArray "inputs" fields[3]!).toList.mapM (readType nominals)
    let outputs ← (← readArray "outputs" fields[4]!).toList.mapM (readType nominals)
    if kind == .sampling && outputs.length != 1 then
      throw s!"a sampling law has exactly one output, found {outputs.length}"
    let identity := if statics.isEmpty then name else s!"{name}({renderStatics identities statics})"
    pure { catalogue := { name, statics }, identity, kind, inputs, outputs }

def readPort (nominals : Nat) (json : Json) : Read Located := do
  let fields ← readFields "port" 2 json
  pure ⟨← readType nominals fields[0]!, ← readNat "holder" fields[1]!⟩

def readFlags (json : Json) : Read Bool := do
  let flags ← readNat "flags" json
  unless flags < 2 do throw s!"unknown definition flags {flags}"
  pure (flags == 1)

def readAgreement (inputs outputs : Nat) (index : Nat) (json : Json) : Read AgreementEntry :=
  located s!"agreement {index}" do
    let parts ← readFields "agreement" 2 json
    let side ← readNat "agreement side" parts[0]!
    unless side < 2 do throw s!"side {side} is neither 0 (inputs) nor 1 (outputs)"
    let ports ← readNats "agreement ports" parts[1]!
    if ports.isEmpty then throw "an agreement names at least one port"
    let count := if side == 0 then inputs else outputs
    for port in ports do
      unless port < count do
        throw s!"dangling reference: port {port} (the signature has {count} {if side == 0 then "inputs" else "outputs"})"
    pure { overOutputs := side == 1, ports }

def readDefinition (nominals : Nat) (row : Nat) (json : Json) : Read DefinitionEntry :=
  located s!"definition {row}" do
    let fields ← readArray "definition" json
    let some head := fields[0]? | throw "empty definition"
    match ← readString "definition kind" head with
    | "function" =>
        unless fields.size == 5 do throw "a function has 5 fields"
        let specificationOnly ← readFlags fields[1]!
        let inputs ← (← readArray "inputs" fields[2]!).toList.mapM (readType nominals)
        let outputs ← (← readArray "outputs" fields[3]!).toList.mapM (readType nominals)
        pure { signature := .function inputs outputs, specificationOnly, body := fields[4]! }
    | "protocol" =>
        unless fields.size == 7 do throw "a protocol has 7 fields"
        let specificationOnly ← readFlags fields[1]!
        let roles ← readNat "roles" fields[2]!
        let inputs ← (← readArray "inputs" fields[3]!).toList.mapM (readPort nominals)
        let outputs ← (← readArray "outputs" fields[4]!).toList.mapM (readPort nominals)
        let mut agreements := #[]
        for (agreement, index) in (← readArray "agreements" fields[5]!).zipIdx do
          agreements := agreements.push (← readAgreement inputs.length outputs.length index agreement)
        pure { signature := .protocol roles inputs outputs agreements.toList, specificationOnly,
               body := fields[6]! }
    | "oracle" => throw "computed oracle definitions are not supported by this importer"
    | "relation" => throw "relation definitions are not supported by this importer"
    | other => throw s!"unknown definition kind {other}"

/-- The side table of names: empty, or the definition names, the role names of every
definition and the site names of every definition. A definition's role names are
absent or one per role; its site names are checked against its sites when its body
is read. -/
def readNames (definitions : Array DefinitionEntry) (json : Json) : Read Names := do
  let parts ← readArray "names" json
  if parts.isEmpty then return {}
  unless parts.size == 3 do
    throw "expected no table or three tables: definition names, role names, site names"
  let strings (what : String) (json : Json) : Read (Array String) := do
    (← readArray what json).mapM (readString what)
  let names ← strings "definition names" parts[0]!
  let roles ← (← readArray "role names" parts[1]!).mapM (strings "role names")
  let sites ← (← readArray "site names" parts[2]!).mapM (strings "site names")
  for (what, size) in [("definition names", names.size), ("role names", roles.size),
      ("site names", sites.size)] do
    unless size == definitions.size do
      throw s!"{what}: {size} entries for {definitions.size} definitions"
  for (entry, row) in definitions.zipIdx do
    let expected := match entry.signature with
      | .protocol roles .. => roles
      | .function .. => 0
    unless roles[row]!.isEmpty || roles[row]!.size == expected do
      throw s!"role names: {roles[row]!.size} names for the {expected} roles of definition {row}"
  pure { definitions := names, roles, sites }

def readPackage (stage : String) (json : Json) : Read Decoded := do
  unless stages.contains stage do
    throw s!"unknown stage {stage}; expected one of {stages}"
  let envelope ← readFields "package" 6 json
  let format ← readString "format" envelope[0]!
  unless format == "zkc.core/0" do throw s!"unknown format {format}; expected zkc.core/0"
  for (field, index) in [("contracts", 2), ("proof", 3), ("parameters", 4)] do
    discard <| readArray field envelope[index]!
  let programs ← readArray "programs" envelope[1]!
  let mut selected : Option (Array Json) := none
  for program in programs do
    let fields ← readFields "program" 5 program
    let programStage ← readString "stage" fields[0]!
    unless stages.contains programStage do
      throw s!"unknown stage {programStage}; expected one of {stages}"
    if programStage == stage then
      if selected.isSome then throw s!"two programs of stage {stage}"
      selected := some fields
  let some fields := selected | throw s!"the package has no program of stage {stage}"
  let mut types := #[]
  let mut typeIdentities := #[]
  for (json, row) in (← readArray "types" fields[1]!).zipIdx do
    let entry ← readTypeRow row json
    types := types.push entry
    typeIdentities := typeIdentities.push s!"{entry.name}({renderStatics typeIdentities entry.statics})"
  let nominals := types.size
  unless (← readArray "oracles" fields[2]!).isEmpty do
    throw "oracle rows are not supported by this importer"
  let mut operations : Array OperationEntry := #[]
  for (json, row) in (← readArray "operations" fields[3]!).zipIdx do
    let entry ← readOperation nominals typeIdentities row json
    if let some earlier := operations.findIdx? (·.identity == entry.identity) then
      throw s!"operation rows {earlier} and {row} have one catalogue identity, {entry.identity}"
    operations := operations.push entry
  let mut definitions := #[]
  for (json, row) in (← readArray "definitions" fields[4]!).zipIdx do
    definitions := definitions.push (← readDefinition nominals row json)
  let names ← located "names" (readNames definitions envelope[5]!)
  pure { stage, nominals, types, operations, definitions, names }

/-! ## Terms -/

def nat (value : Nat) : Expr := mkNatLit value

def bool (value : Bool) : Expr := toExpr value

def listOf (element : Expr) (items : List Expr) : Expr :=
  items.foldr (fun item rest => mkApp3 (mkConst ``List.cons [Level.zero]) element item rest)
    (mkApp (mkConst ``List.nil [Level.zero]) element)

def tyType : Expr := mkConst ``Zkc.Core.Ty
def locatedType : Expr := mkConst ``Zkc.Core.Located
def headerType : Expr := mkConst ``Zkc.Core.Header
def signatureType : Expr := mkConst ``Zkc.Core.OperationSignature

def stopTerm : PIR.Stop → Expr
  | .reject => mkConst ``PIR.Stop.reject
  | .abort => mkConst ``PIR.Stop.abort
  | .exhausted => mkConst ``PIR.Stop.exhausted
  | .incomplete => mkConst ``PIR.Stop.incomplete
  | .refused => mkConst ``PIR.Stop.refused

def kindTerm : OperationKind → Expr
  | .pure => mkConst ``Zkc.Core.OperationKind.pure
  | .partial => mkConst ``Zkc.Core.OperationKind.partial
  | .sampling => mkConst ``Zkc.Core.OperationKind.sampling

def renderKind : OperationKind → String
  | .pure => "pure"
  | .partial => "partial"
  | .sampling => "sampling"

def reasonTerm : Reason → Expr
  | .reject => mkConst ``Zkc.Core.Reason.reject
  | .abort => mkConst ``Zkc.Core.Reason.abort
  | .exhausted => mkConst ``Zkc.Core.Reason.exhausted
  | .refused => mkConst ``Zkc.Core.Reason.refused

/-- The reason of a `stop`. The reserved reason has a term, which the residual
conditions refuse. -/
def readStop : Json → Read PIR.Stop
  | .str "reject" => pure .reject
  | .str "abort" => pure .abort
  | .str "exhausted" => pure .exhausted
  | .str "incomplete" => pure .incomplete
  | .str "refused" => pure .refused
  | other => throw s!"unknown stop reason {other.compress}"

/-- The reason of a `guard`: an authored reason. The reserved reason has no term. -/
def readReason : Json → Read Reason
  | .str "reject" => pure .reject
  | .str "abort" => pure .abort
  | .str "exhausted" => pure .exhausted
  | .str "refused" => pure .refused
  | .str "incomplete" =>
      throw "a guard names an authored reason; incomplete is reserved for a side whose roles disagree"
  | other => throw s!"unknown stop reason {other.compress}"

def proofTrue : Expr := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)
def proofFalse : Expr := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.false)

def verdictType : Expr := mkApp (mkConst ``Option [Level.zero]) (mkConst ``Zkc.Core.Violation)

def noViolation : Expr := mkApp (mkConst ``Option.none [Level.zero]) (mkConst ``Zkc.Core.Violation)

/-- The proof that a definition has no residual violation, when the kernel evaluates
`Definition.violation` to `none`. -/
def proofWellFormed : Expr := mkApp2 (mkConst ``Eq.refl [Level.one]) verdictType noViolation

/-- The residual conditions in words. The importer's refusals and its reports of the
kernel's refusals share them. -/
def describe : Violation → String
  | .noRole => "a protocol has no role"
  | .roleOutOfRange => "a role is not below the role count"
  | .noParticipant => "a repeat or branch has no participant"
  | .repeatedParticipant => "a repeat or branch lists a participant twice"
  | .roleOutsideParticipants =>
      "an operation inside a repeat or branch names a role that is not a participant"
  | .valueOutsideParticipants =>
      "a value that enters or leaves a repeat or branch is held by a role that is not a participant"
  | .exchangeToSelf => "the sender of an exchange is its receiver"
  | .receiversNotIncreasing => "the receivers of a draw do not increase strictly"
  | .ownerReceives => "the owner of a draw is one of its receivers"
  | .roleMapLength => "a role map does not have one entry per formal role"
  | .roleMapNotInjective => "a role map sends two formal roles to one role"
  | .siteGap => "the sites of a definition are not numbered from 0 without gaps"
  | .repeatedSite => "two operations of a definition share a site"
  | .protocolStop => "a protocol region contains a stop"
  | .reservedReason => "a stop names the reserved reason incomplete"
  | .agreementHolders => "two copies of an agreement have one holder"
  | .agreementPorts => "the agreements of a signature name a port twice"

def violations : List (Name × Violation) :=
  [(``Violation.noRole, .noRole), (``Violation.roleOutOfRange, .roleOutOfRange),
   (``Violation.noParticipant, .noParticipant),
   (``Violation.repeatedParticipant, .repeatedParticipant),
   (``Violation.roleOutsideParticipants, .roleOutsideParticipants),
   (``Violation.valueOutsideParticipants, .valueOutsideParticipants),
   (``Violation.exchangeToSelf, .exchangeToSelf),
   (``Violation.receiversNotIncreasing, .receiversNotIncreasing),
   (``Violation.ownerReceives, .ownerReceives), (``Violation.roleMapLength, .roleMapLength),
   (``Violation.roleMapNotInjective, .roleMapNotInjective), (``Violation.siteGap, .siteGap),
   (``Violation.repeatedSite, .repeatedSite), (``Violation.protocolStop, .protocolStop),
   (``Violation.reservedReason, .reservedReason),
   (``Violation.agreementHolders, .agreementHolders),
   (``Violation.agreementPorts, .agreementPorts)]

/-- Kernel terms of types, shared through a cache so that the term is a DAG. -/
structure Terms where
  types : Std.HashMap String Expr := {}

abbrev Build := StateT Terms Read

def tyKey : Ty → String := renderTy

partial def tyTermRaw : Ty → Build Expr
  | .unit => pure (mkConst ``Zkc.Core.Ty.unit)
  | .bool => pure (mkConst ``Zkc.Core.Ty.bool)
  | .index => pure (mkConst ``Zkc.Core.Ty.index)
  | .nominal row => pure (mkApp (mkConst ``Zkc.Core.Ty.nominal) (nat row))
  | .array element => return mkApp (mkConst ``Zkc.Core.Ty.array) (← tyTerm element)
  | .tuple components =>
      return mkApp (mkConst ``Zkc.Core.Ty.tuple) (listOf tyType (← components.mapM tyTerm))
  | .variant first rest =>
      return mkApp2 (mkConst ``Zkc.Core.Ty.variant) (← tyTerm first)
        (listOf tyType (← rest.mapM tyTerm))
where
  tyTerm (type : Ty) : Build Expr := do
    let key := tyKey type
    if let some term := (← get).types[key]? then return term
    let term ← tyTermRaw type
    modify fun terms => { terms with types := terms.types.insert key term }
    pure term

def tyTerm (type : Ty) : Build Expr := tyTermRaw.tyTerm type

def locatedTerm (value : Located) : Build Expr := do
  let key := s!"{tyKey value.type}@{value.holder}"
  if let some term := (← get).types[key]? then return term
  let term := mkApp2 (mkConst ``Zkc.Core.Located.mk) (← tyTerm value.type) (nat value.holder)
  modify fun terms => { terms with types := terms.types.insert key term }
  pure term

def tysTerm (types : List Ty) : Build Expr := return listOf tyType (← types.mapM tyTerm)

def locatedsTerm (types : List Located) : Build Expr :=
  return listOf locatedType (← types.mapM locatedTerm)

def natsTerm (values : List Nat) : Expr := listOf (mkConst ``Nat) (values.map nat)

/-- The variable of position `index` of a list term: `items` are the element terms
and `suffixes[i]` the list term from position `i`. -/
def listVar (element : Expr) (items suffixes : Array Expr) (index : Nat) : Expr := Id.run do
  let mut term := mkApp3 (mkConst ``Zkc.Source.Var.here) element suffixes[index + 1]! items[index]!
  for outer in (List.range index).reverse do
    term := mkApp5 (mkConst ``Zkc.Source.Var.there) element suffixes[outer + 1]! items[index]!
      items[outer]! term
  term

/-- The list term from every position of a list, the empty list last. -/
def listSuffixes (element : Expr) (items : Array Expr) : Array Expr := Id.run do
  let mut suffixes := #[listOf element []]
  for item in items.reverse do
    suffixes := suffixes.push (mkApp3 (mkConst ``List.cons [Level.zero]) element item suffixes.back!)
  suffixes.reverse

/-- The agreements over one list of ports. The declared type of an agreement is the
type of its first port; a copy of another type is ill typed. -/
def agreementsTerm (ports : List Located) (agreements : List AgreementEntry) : Build Expr := do
  let items := (← ports.mapM locatedTerm).toArray
  let suffixes := listSuffixes locatedType items
  let portsTerm := suffixes[0]!
  let mut terms := #[]
  for agreement in agreements do
    let type := (ports[agreement.ports.head!]!).type
    let typeTerm ← tyTerm type
    let copies := agreement.ports.map fun port =>
      mkApp4 (mkConst ``Zkc.Core.Copy.mk) portsTerm typeTerm (nat (ports[port]!).holder)
        (listVar locatedType items suffixes port)
    terms := terms.push (mkApp3 (mkConst ``Zkc.Core.Agreement.mk) portsTerm typeTerm
      (listOf (mkApp2 (mkConst ``Zkc.Core.Copy) portsTerm typeTerm) copies))
  pure (listOf (mkApp (mkConst ``Zkc.Core.Agreement) portsTerm) terms.toList)

/-- The agreements of a protocol's signature. -/
def signatureAgreements (inputs outputs : List Located) (agreements : List AgreementEntry) :
    Build Expr := do
  return mkApp4 (mkConst ``Zkc.Core.Agreements.mk) (← locatedsTerm inputs) (← locatedsTerm outputs)
    (← agreementsTerm inputs (agreements.filter (!·.overOutputs)))
    (← agreementsTerm outputs (agreements.filter (·.overOutputs)))

def headerTerm (header : Signature) (specificationOnly : Bool) : Build Expr := do
  match header with
  | .function inputs outputs =>
      return mkApp3 (mkConst ``Zkc.Core.Header.function) (← tysTerm inputs) (← tysTerm outputs)
        (bool specificationOnly)
  | .protocol roles inputs outputs agreements =>
      return mkApp5 (mkConst ``Zkc.Core.Header.protocol) (nat roles) (← locatedsTerm inputs)
        (← locatedsTerm outputs) (← signatureAgreements inputs outputs agreements)
        (bool specificationOnly)

/-! ## The catalogue -/

def staticTerm : Static → Build Expr
  | .domain name => pure (mkApp (mkConst ``Zkc.Core.Static.domain) (mkStrLit name))
  | .nat value => pure (mkApp (mkConst ``Zkc.Core.Static.nat) (nat value))
  | .type type => return mkApp (mkConst ``Zkc.Core.Static.type) (← tyTerm type)

def catalogueRowTerm (row : CatalogueRow) : Build Expr := do
  return mkApp2 (mkConst ``Zkc.Core.CatalogueRow.mk) (mkStrLit row.name)
    (listOf (mkConst ``Zkc.Core.Static) (← row.statics.mapM staticTerm))

def catalogueTerm (decoded : Decoded) : Build Expr := do
  let rowType := mkConst ``Zkc.Core.CatalogueRow
  return mkApp2 (mkConst ``Zkc.Core.Catalogue.mk)
    (listOf rowType (← decoded.types.toList.mapM catalogueRowTerm))
    (listOf rowType (← decoded.operations.toList.mapM fun entry => catalogueRowTerm entry.catalogue))

/-! ## Scopes: typed contexts of a region

The values of a region are numbered as in the package: inputs first, then results.
The Lean context lists them most recent first, the first result of an operation
before its later results. A slot records the context list that starts at it, so
that every variable's implicit context arguments are shared subterms. -/

structure Slot where
  type : Ty
  holder : Option Nat
  typeTerm : Expr
  suffix : Expr
  deriving Inhabited

structure Scope where
  element : Expr
  nil : Expr
  slots : Array Slot := #[]
  positions : Array Nat := #[]

def Scope.create (element : Expr) : Scope :=
  { element, nil := mkApp (mkConst ``List.nil [Level.zero]) element }

def Scope.context (scope : Scope) : Expr :=
  match scope.slots.back? with
  | some slot => slot.suffix
  | none => scope.nil

def Scope.size (scope : Scope) : Nat := scope.positions.size

/-- Bind values in order: the first becomes the most recent. -/
def Scope.push (scope : Scope) (values : List (Ty × Option Nat × Expr)) : Scope := Id.run do
  let base := scope.slots.size
  let count := values.length
  let mut slots := scope.slots
  for (type, holder, typeTerm) in values.reverse do
    let tail := match slots.back? with
      | some slot => slot.suffix
      | none => scope.nil
    let suffix := mkApp3 (mkConst ``List.cons [Level.zero]) scope.element typeTerm tail
    slots := slots.push { type, holder, typeTerm, suffix }
  let positions := (List.range count).foldl (fun positions index =>
    positions.push (base + (count - 1 - index))) scope.positions
  { scope with slots, positions }

def Scope.slot (scope : Scope) (value : Nat) : Read Slot := do
  let some position := scope.positions[value]?
    | throw s!"dangling reference: value {value} (the context has {scope.size} values)"
  pure scope.slots[position]!

def Scope.tail (scope : Scope) (position : Nat) : Expr :=
  if position == 0 then scope.nil else scope.slots[position - 1]!.suffix

/-- The variable of a package value: `there` once for every more recent value. -/
def Scope.var (scope : Scope) (value : Nat) : Read Expr := do
  let some position := scope.positions[value]?
    | throw s!"dangling reference: value {value} (the context has {scope.size} values)"
  let target := scope.slots[position]!
  let mut term := mkApp3 (mkConst ``Zkc.Source.Var.here) scope.element (scope.tail position)
    target.typeTerm
  for outer in [position + 1:scope.slots.size] do
    term := mkApp5 (mkConst ``Zkc.Source.Var.there) scope.element (scope.tail outer)
      target.typeTerm scope.slots[outer]!.typeTerm term
  pure term

/-- `Operands Γ types` for the given values, typed by the values' own types. -/
def Scope.operands (scope : Scope) (values : List Nat) : Read Expr := do
  let context := scope.context
  let family := mkApp2 (mkConst ``Zkc.Source.Var) scope.element context
  let mut term := mkApp2 (mkConst ``Zkc.Source.Values.nil) scope.element family
  let mut types := scope.nil
  for value in values.reverse do
    let slot ← scope.slot value
    term := mkApp6 (mkConst ``Zkc.Source.Values.cons) scope.element family slot.typeTerm types
      (← scope.var value) term
    types := mkApp3 (mkConst ``List.cons [Level.zero]) scope.element slot.typeTerm types
  pure term

/-! ## The operation table -/

/-- The operation table as a kernel term, with the list starting at every row, so
that a row variable's implicit context arguments are shared subterms. -/
structure Table where
  rows : Array Expr
  suffixes : Array Expr

def tableOf (operations : Array OperationEntry) : Build Table := do
  let mut rows := #[]
  for entry in operations do
    rows := rows.push (mkApp3 (mkConst ``Zkc.Core.OperationSignature.mk) (← tysTerm entry.inputs)
      (← tysTerm entry.outputs) (kindTerm entry.kind))
  pure { rows, suffixes := listSuffixes signatureType rows }

/-- The variable of a row in the table. -/
def Table.var (table : Table) (row : Nat) : Expr :=
  listVar signatureType table.rows table.suffixes row

/-! ## Definitions -/

structure Context where
  decoded : Decoded
  /-- The operation table constant. -/
  operations : Expr
  /-- The constants of the operation rows: each row's variable into the table. -/
  rows : Array Expr
  /-- The definition being built, its row number. -/
  definition : Nat
  definitionName : String
  roles : Nat
  /-- The participants of the enclosing `repeat` or `branch`, if there is one. -/
  enclosing : Option (List Nat)
  deployed : Bool
  /-- The importer's checks of what the kernel also decides; off, a violation reaches
  the kernel. -/
  checked : Bool
  /-- `headerLists[j]` is the list of the headers of rows `j-1, …, 0`. -/
  headerLists : Array Expr
  headerTerms : Array Expr
  /-- The agreements of the earlier protocols' signatures. -/
  agreementTerms : Array Expr

def Context.headers (context : Context) : Expr := context.headerLists[context.definition]!

def Context.localDialect (context : Context) : Expr :=
  mkApp3 (mkConst ``Zkc.Core.LocalDialect) context.operations context.headers (bool context.deployed)

def Context.protocolDialect (context : Context) : Expr :=
  mkApp3 (mkConst ``Zkc.Core.ProtocolDialect) context.operations context.headers
    (bool context.deployed)

/-- The variable of an earlier definition among the headers of the definitions before
`definition`. -/
def calleeVar (headerLists headerTerms : Array Expr) (definition row : Nat) : Expr := Id.run do
  let header := headerTerms[row]!
  let mut term := mkApp3 (mkConst ``Zkc.Source.Var.here) headerType headerLists[row]! header
  for outer in [row + 1:definition] do
    term := mkApp5 (mkConst ``Zkc.Source.Var.there) headerType headerLists[outer]! header
      headerTerms[outer]! term
  term

/-- The variable of an earlier definition in the current headers. -/
def Context.callee (context : Context) (row : Nat) : Read Expr := do
  unless row < context.definition do
    throw s!"dangling reference: definition {row} is not an earlier definition"
  pure (calleeVar context.headerLists context.headerTerms context.definition row)

def Context.roleName (context : Context) (role : Nat) : String :=
  match context.decoded.names.roles[context.definition]? >>= (·[role]?) with
  | some name => s!"{role} ({name})"
  | none => toString role

/-- Where an operation stands: the role count and the enclosing participants. -/
def Context.place (context : Context) : String :=
  match context.enclosing with
  | some participants => s!"{context.roles} roles, participants {participants}"
  | none => s!"{context.roles} roles"

/-- Refuse when one of the model's residual conditions fails. With `kernel_only` the
kernel decides alone. -/
def Context.require (context : Context) (conditions : List (Bool × Violation)) (detail : String) :
    Read Unit := do
  if context.checked then
    if let some violation := firstViolation conditions then
      throw s!"{describe violation} ({detail})"

/-- The roles an operation names are below the role count and, inside a `repeat` or
`branch`, participants. -/
def Context.acting (context : Context) (acting : List Nat) : Read Unit :=
  context.require (actingRoles context.roles context.enclosing acting)
    s!"roles {acting}; {context.place}"

/-- Check one operand against its expected type and, in a protocol, holder. -/
def Context.checkOperand (context : Context) (scope : Scope) (index : Nat) (value : Nat)
    (type : Ty) (holder : Option Nat) : Read Unit := do
  let slot ← scope.slot value
  unless context.checked do return
  unless slot.type == type do
    throw s!"wrong type: operand {index} (value {value}) has type {renderTy slot.type}, expected {renderTy type}"
  match holder, slot.holder with
  | some expected, some actual =>
      unless expected == actual do
        throw s!"wrong holder: operand {index} (value {value}) is held by role {context.roleName actual}, expected role {context.roleName expected}"
  | _, _ => pure ()

def Context.checkOperands (context : Context) (scope : Scope) (values : List Nat)
    (types : List Ty) (holders : List (Option Nat)) : Read Unit := do
  unless values.length == types.length || !context.checked do
    throw s!"expected {types.length} operands, found {values.length}"
  for ((value, type), (holder, index)) in (values.zip types).zip (holders.zip (List.range values.length)) do
    context.checkOperand scope index value type holder

def Context.checkLocated (context : Context) (scope : Scope) (values : List Nat)
    (types : List Located) : Read Unit :=
  context.checkOperands scope values (types.map (·.type)) (types.map (some ·.holder))

def Context.operation (context : Context) (row : Nat) : Read OperationEntry := do
  let some entry := context.decoded.operations[row]?
    | throw s!"dangling reference: operation row {row} (the table has {context.decoded.operations.size} rows)"
  pure entry

/-- A sampling row used by `draw` or `sample`: its inputs and its one output. -/
def Context.law (context : Context) (row : Nat) : Read (List Ty × Ty) := do
  let entry ← context.operation row
  if context.checked then
    unless entry.kind == .sampling do
      throw s!"operation row {row} ({entry.identity}) is {renderKind entry.kind}, not a sampling law"
  match entry.outputs with
  | [output] => pure (entry.inputs, output)
  | _ => throw s!"operation row {row} ({entry.identity}) has {entry.outputs.length} outputs and cannot be used as a sampling law"

def Context.permitted (context : Context) (callee : Nat) : Read Unit := do
  let entry := context.decoded.definitions[callee]!
  if context.checked && context.deployed && entry.specificationOnly then
    throw s!"the deployed definition {context.definitionName} uses the specification-only definition {callee}"

/-- The last instruction of a region is `stop`. -/
def regionStops (json : Json) : Bool :=
  match json with
  | .arr #[.arr instructions, _] =>
      match instructions.back? with
      | some (.arr items) => items[0]? == some (.str "stop")
      | _ => false
  | _ => false

/-- The participants of a `repeat` or `branch` with the values that hold their
counts or conditions. -/
def readParticipants (pairs : Array Json) : Read (List Nat × List Nat) := do
  let mut roles := #[]
  let mut operands := #[]
  for pair in pairs do
    let parts ← readFields "participant" 2 pair
    roles := roles.push (← readNat "participant" parts[0]!)
    operands := operands.push (← readNat "participant value" parts[1]!)
  pure (roles.toList, operands.toList)

/-- What the body of a definition uses. -/
structure Uses where
  /-- The sites of the definition, in order of occurrence. -/
  sites : Array Nat := #[]
  /-- The earlier definitions that the definition calls or applies. -/
  callees : Array Nat := #[]

structure Built where
  term : Expr
  outputs : List Ty
  stops : Bool

structure BuiltProtocol where
  term : Expr
  outputs : List Located

abbrev Builder := StateT Uses Build

def lift {α : Type} (action : Read α) : Builder α := fun uses terms => do
  let value ← action
  pure ((value, uses), terms)

def build {α : Type} (action : Build α) : Builder α := StateT.lift action

/-- Prefix the message of a refusal with its location. -/
def prefixed {α : Type} (where_ : String) (action : Builder α) : Builder α := fun uses terms =>
  (action uses terms).mapError fun message => s!"{where_}: {message}"

def useSite (site : Nat) : Builder Unit :=
  modify fun uses => { uses with sites := uses.sites.push site }

def useCallee (row : Nat) : Builder Unit :=
  modify fun uses =>
    if uses.callees.contains row then uses else { uses with callees := uses.callees.push row }

def regionTerm (dialect : Expr) (types : List (Expr × Expr × Expr × Expr)) (last : Expr)
    (output : Expr) : Expr :=
  types.foldr (fun (context, op, operands, bodies) next =>
    mkApp7 (mkConst ``Zkc.Source.Region.letOp) dialect context output op operands bodies next) last

def regionsNil (dialect : Expr) : Expr := mkApp (mkConst ``Zkc.Source.Regions.nil) dialect

def regionsCons (dialect element : Expr) (inputs outputs : Expr) (rest : List (Expr × Expr))
    (body tail : Expr) : Expr :=
  let pair := mkConst ``Prod.mk [Level.zero, Level.zero]
  let listType := mkApp (mkConst ``List [Level.zero]) element
  let restTerm := listOf (mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) listType listType)
    (rest.map fun (a, b) => mkApp4 pair listType listType a b)
  mkApp6 (mkConst ``Zkc.Source.Regions.cons) dialect inputs outputs restTerm body tail

/-- A `stop` as the last instruction of a region: its reason. -/
def readFinalStop (instructions : Array Json) (index : Nat) (items : Array Json) :
    Read (Option PIR.Stop) := do
  unless items[0]? == some (.str "stop") do return none
  unless index + 1 == instructions.size do
    throw s!"instruction {index}: stop must be the last instruction of its region"
  unless items.size == 2 do throw s!"instruction {index}: malformed stop"
  some <$> readStop items[1]!

/-- One local instruction: the operation, its nested local regions, its operands,
their expected types and the result types. -/
structure LocalStep where
  op : Expr
  bodies : Expr
  operands : List Nat
  inputs : List Ty
  results : List Ty

mutual
  /-- A local region with the given inputs; outputs given or inferred. -/
  partial def buildLocal (context : Context) (inputs : List Ty) (expected : Option (List Ty))
      (json : Json) : Builder Built := do
    let parts ← lift (readFields "region" 2 json)
    let instructions ← lift (readArray "instructions" parts[0]!)
    let returned ← lift (readNats "returned values" parts[1]!)
    let dialect := context.localDialect
    let mut scope := Scope.create tyType
    let inputTerms ← build (inputs.mapM tyTerm)
    scope := scope.push ((inputs.zip inputTerms).map fun (type, term) => (type, none, term))
    let mut nodes := #[]
    let mut stop := none
    for (instruction, index) in instructions.zipIdx do
      let items ← lift (readArray "instruction" instruction)
      if let some reason ← lift (readFinalStop instructions index items) then
        lift (located s!"instruction {index}"
          (context.require [(authoredStop reason, .reservedReason)] "stop"))
        stop := some reason
        continue
      let step ← prefixed s!"instruction {index}" (localStep context scope items)
      lift (located s!"instruction {index}" (context.checkOperands scope step.operands step.inputs
        (step.operands.map fun _ => none)))
      let operands ← lift (located s!"instruction {index}" (scope.operands step.operands))
      nodes := nodes.push (scope.context, step.op, operands, step.bodies)
      let resultTerms ← build (step.results.mapM tyTerm)
      scope := scope.push ((step.results.zip resultTerms).map fun (type, term) => (type, none, term))
    let outputs ← match stop, expected with
      | _, some outputs => pure outputs
      | some _, none => pure []
      | none, none => lift (returned.mapM fun value => return (← scope.slot value).type)
    let outputTerm ← build (tysTerm outputs)
    let last ← match stop with
      | some reason =>
          unless returned.isEmpty do throw "a region ending in stop returns no values"
          pure (mkApp4 (mkConst ``Zkc.Source.Region.stop) dialect scope.context outputTerm
            (stopTerm reason))
      | none => do
          lift (located "returned values" (context.checkOperands scope returned outputs
            (returned.map fun _ => none)))
          pure (mkApp4 (mkConst ``Zkc.Source.Region.ret) dialect scope.context outputTerm
            (← lift (scope.operands returned)))
    pure { term := regionTerm dialect nodes.toList last outputTerm, outputs, stops := stop.isSome }

  /-- One local instruction over a context of local or protocol values. -/
  partial def localStep (context : Context) (scope : Scope) (items : Array Json) :
      Builder LocalStep := do
    let operations := context.operations
    let headers := context.headers
    let deployed := bool context.deployed
    let some (Json.str head) := items[0]? | throw "malformed instruction"
    let typeOf (value : Nat) : Read Ty := return (← scope.slot value).type
    match head with
    | "op" => do
        unless items.size == 3 do throw "malformed op"
        let row ← lift (readNat "operation row" items[1]!)
        let entry ← lift (context.operation row)
        if context.checked && entry.kind == .sampling then
          throw s!"operation row {row} ({entry.identity}) is a sampling law, not an operation"
        let op := mkApp8 (mkConst ``Zkc.Core.LocalOp.op) operations headers deployed
          (← build (tysTerm entry.inputs)) (← build (tysTerm entry.outputs)) (kindTerm entry.kind)
          context.rows[row]! proofTrue
        pure { op, bodies := regionsNil context.localDialect,
               operands := ← lift (readNats "operands" items[2]!),
               inputs := entry.inputs, results := entry.outputs }
    | "call" => do
        unless items.size == 3 do throw "malformed call"
        let row ← lift (readNat "callee" items[1]!)
        let callee ← lift (context.callee row)
        let entry := context.decoded.definitions[row]!
        let .function inputs outputs := entry.signature
          | throw s!"call of definition {row}, which is not a function"
        lift (context.permitted row)
        useCallee row
        let op := mkApp8 (mkConst ``Zkc.Core.LocalOp.call) operations headers deployed
          (← build (tysTerm inputs)) (← build (tysTerm outputs))
          (bool entry.specificationOnly) callee proofFalse
        pure { op, bodies := regionsNil context.localDialect,
               operands := ← lift (readNats "operands" items[2]!), inputs, results := outputs }
    | "if" => do
        unless items.size == 5 do throw "malformed if"
        let condition ← lift (readNat "condition" items[1]!)
        let captures ← lift (readNats "captures" items[2]!)
        let captureTypes ← lift (captures.mapM typeOf)
        let (onTrue, onFalse) ← if regionStops items[3]! && !regionStops items[4]! then do
            let onFalse ← buildLocal context captureTypes none items[4]!
            let onTrue ← buildLocal context captureTypes (some onFalse.outputs) items[3]!
            pure (onTrue, onFalse)
          else do
            let onTrue ← buildLocal context captureTypes none items[3]!
            let onFalse ← buildLocal context captureTypes (some onTrue.outputs) items[4]!
            pure (onTrue, onFalse)
        let outputs := onTrue.outputs
        let capturesTerm ← build (tysTerm captureTypes)
        let outputsTerm ← build (tysTerm outputs)
        let dialect := context.localDialect
        let bodies := regionsCons dialect tyType capturesTerm outputsTerm [(capturesTerm, outputsTerm)]
          onTrue.term (regionsCons dialect tyType capturesTerm outputsTerm [] onFalse.term
            (regionsNil dialect))
        pure { op := mkApp5 (mkConst ``Zkc.Core.LocalOp.conditional) operations headers deployed
                 capturesTerm outputsTerm,
               bodies, operands := condition :: captures, inputs := .bool :: captureTypes,
               results := outputs }
    | "loop" => do
        unless items.size == 6 do throw "malformed loop"
        let maximum ← lift (readNat "maximum" items[1]!)
        let count ← lift (readNat "count" items[2]!)
        let carried ← lift (readNats "carried" items[3]!)
        let captures ← lift (readNats "captures" items[4]!)
        let carriedTypes ← lift (carried.mapM typeOf)
        let captureTypes ← lift (captures.mapM typeOf)
        let regionInputs := .index :: (carriedTypes ++ captureTypes)
        let body ← buildLocal context regionInputs (some carriedTypes) items[5]!
        let carriedTerm ← build (tysTerm carriedTypes)
        let capturesTerm ← build (tysTerm captureTypes)
        let dialect := context.localDialect
        let bodies := regionsCons dialect tyType (← build (tysTerm regionInputs))
          carriedTerm [] body.term (regionsNil dialect)
        pure { op := mkApp6 (mkConst ``Zkc.Core.LocalOp.loop) operations headers deployed
                 (nat maximum) carriedTerm capturesTerm,
               bodies, operands := count :: (carried ++ captures),
               inputs := .index :: (carriedTypes ++ captureTypes), results := carriedTypes }
    | "guard" => do
        unless items.size == 3 do throw "malformed guard"
        let reason ← lift (readReason items[1]!)
        pure { op := mkApp4 (mkConst ``Zkc.Core.LocalOp.guard) operations headers deployed
                 (reasonTerm reason),
               bodies := regionsNil context.localDialect,
               operands := [← lift (readNat "condition" items[2]!)], inputs := [.bool], results := [] }
    | "match" => throw "match is not supported by this importer"
    | other => throw s!"unknown local instruction {other}"
end

mutual
  /-- A protocol region with the given inputs; outputs given or inferred. -/
  partial def buildProtocol (context : Context) (inputs : List Located)
      (expected : Option (List Located)) (json : Json) : Builder BuiltProtocol := do
    let parts ← lift (readFields "region" 2 json)
    let instructions ← lift (readArray "instructions" parts[0]!)
    let returned ← lift (readNats "returned values" parts[1]!)
    let dialect := context.protocolDialect
    let mut scope := Scope.create locatedType
    let inputTerms ← build (inputs.mapM locatedTerm)
    scope := scope.push ((inputs.zip inputTerms).map fun (value, term) =>
      (value.type, some value.holder, term))
    let mut nodes := #[]
    let mut stop := none
    for (instruction, index) in instructions.zipIdx do
      let items ← lift (readArray "instruction" instruction)
      if let some reason ← lift (readFinalStop instructions index items) then
        -- A protocol region has no `stop`. The term exists, so that the kernel can
        -- refuse it when it decides alone.
        lift (located s!"instruction {index}" (context.require [(false, .protocolStop)] "stop"))
        stop := some reason
        continue
      let (op, bodies, operands, results) ←
        prefixed s!"instruction {index}" (protocolStep context scope items)
      let operandsTerm ← lift (located s!"instruction {index}" (scope.operands operands))
      nodes := nodes.push (scope.context, op, operandsTerm, bodies)
      let resultTerms ← build (results.mapM locatedTerm)
      scope := scope.push ((results.zip resultTerms).map fun (value, term) =>
        (value.type, some value.holder, term))
    let outputs ← match stop, expected with
      | _, some outputs => pure outputs
      | some _, none => pure []
      | none, none => lift (returned.mapM fun value => do
          let slot ← scope.slot value
          pure ⟨slot.type, slot.holder.getD 0⟩)
    let outputTerm ← build (locatedsTerm outputs)
    let last ← match stop with
      | some reason =>
          unless returned.isEmpty do throw "a region ending in stop returns no values"
          pure (mkApp4 (mkConst ``Zkc.Source.Region.stop) dialect scope.context outputTerm
            (stopTerm reason))
      | none => do
          lift (located "returned values" (context.checkLocated scope returned outputs))
          pure (mkApp4 (mkConst ``Zkc.Source.Region.ret) dialect scope.context outputTerm
            (← lift (scope.operands returned)))
    pure { term := regionTerm dialect nodes.toList last outputTerm, outputs }

  /-- One protocol instruction: operation, nested regions, operands and result types. -/
  partial def protocolStep (context : Context) (scope : Scope) (items : Array Json) :
      Builder (Expr × Expr × List Nat × List Located) := do
    let operations := context.operations
    let headers := context.headers
    let deployed := bool context.deployed
    let dialect := context.protocolDialect
    let some (Json.str head) := items[0]? | throw "malformed instruction"
    let locatedOf (value : Nat) : Read Located := do
      let slot ← scope.slot value
      pure ⟨slot.type, slot.holder.getD 0⟩
    match head with
    | "at" => do
        unless items.size == 3 do throw "malformed at"
        let role ← lift (readNat "role" items[1]!)
        lift (context.acting [role])
        let inner ← lift (readArray "local instruction" items[2]!)
        if inner[0]? == some (.str "stop") then throw "stop is not an operation that a role performs"
        let step ← localStep context scope inner
        lift (context.checkOperands scope step.operands step.inputs
          (step.operands.map fun _ => some role))
        let op := mkApp6 (mkConst ``Zkc.Core.ProtocolOp.at) operations headers deployed (nat role)
          step.op step.bodies
        pure (op, regionsNil dialect, step.operands, step.results.map fun type => ⟨type, role⟩)
    | "exchange" => do
        unless items.size == 5 do throw "malformed exchange"
        let sender ← lift (readNat "sender" items[1]!)
        let receiver ← lift (readNat "receiver" items[2]!)
        let site ← lift (readNat "site" items[3]!)
        let value ← lift (readNat "value" items[4]!)
        lift (context.acting [sender, receiver])
        lift (context.require (exchangeConditions sender receiver) s!"role {sender}")
        useSite site
        let type := (← lift (scope.slot value)).type
        lift (context.checkOperands scope [value] [type] [some sender])
        let op := mkApp7 (mkConst ``Zkc.Core.ProtocolOp.exchange) operations headers deployed
          (nat sender) (nat receiver) (nat site) (← build (tyTerm type))
        pure (op, regionsNil dialect, [value], [⟨type, receiver⟩])
    | "draw" => do
        unless items.size == 6 do throw "malformed draw"
        let owner ← lift (readNat "owner" items[1]!)
        let receivers ← lift (readNats "receivers" items[2]!)
        let site ← lift (readNat "site" items[3]!)
        let row ← lift (readNat "law" items[4]!)
        let (inputs, output) ← lift (context.law row)
        let operands ← lift (readNats "operands" items[5]!)
        lift (context.acting (owner :: receivers))
        lift (context.require (drawConditions owner receivers)
          s!"owner {owner}, receivers {receivers}")
        useSite site
        lift (context.checkOperands scope operands inputs (operands.map fun _ => some owner))
        let op := mkApp9 (mkConst ``Zkc.Core.ProtocolOp.draw) operations headers deployed (nat owner)
          (natsTerm receivers) (nat site) (← build (tysTerm inputs)) (← build (tyTerm output))
          context.rows[row]!
        pure (op, regionsNil dialect, operands,
          ⟨output, owner⟩ :: receivers.map fun receiver => ⟨output, receiver⟩)
    | "sample" => do
        unless items.size == 5 do throw "malformed sample"
        let owner ← lift (readNat "owner" items[1]!)
        let site ← lift (readNat "site" items[2]!)
        let row ← lift (readNat "law" items[3]!)
        let (inputs, output) ← lift (context.law row)
        let operands ← lift (readNats "operands" items[4]!)
        lift (context.acting [owner])
        useSite site
        lift (context.checkOperands scope operands inputs (operands.map fun _ => some owner))
        let op := mkApp8 (mkConst ``Zkc.Core.ProtocolOp.sample) operations headers deployed
          (nat owner) (nat site) (← build (tysTerm inputs)) (← build (tyTerm output))
          context.rows[row]!
        pure (op, regionsNil dialect, operands, [⟨output, owner⟩])
    | "repeat" => do
        unless items.size == 6 do throw "malformed repeat"
        let maximum ← lift (readNat "maximum" items[2]!)
        let carried ← lift (readNats "carried" items[3]!)
        let captures ← lift (readNats "captures" items[4]!)
        let carriedTypes ← lift (carried.mapM locatedOf)
        let captureTypes ← lift (captures.mapM locatedOf)
        let (roles, counts) ← lift (readParticipants (← lift (readArray "participants" items[1]!)))
        lift (context.acting roles)
        lift (context.require (participantConditions roles (carriedTypes ++ captureTypes))
          s!"participants {roles}")
        lift (context.checkOperands scope counts (counts.map fun _ => .index) (roles.map some))
        let body ← buildProtocol { context with enclosing := some roles }
          (carriedTypes ++ captureTypes) (some carriedTypes) items[5]!
        let carriedTerm ← build (locatedsTerm carriedTypes)
        let capturesTerm ← build (locatedsTerm captureTypes)
        let op := mkApp7 (mkConst ``Zkc.Core.ProtocolOp.repeat) operations headers deployed
          (natsTerm roles) (nat maximum) carriedTerm capturesTerm
        let bodies := regionsCons dialect locatedType
          (← build (locatedsTerm (carriedTypes ++ captureTypes))) carriedTerm [] body.term
          (regionsNil dialect)
        pure (op, bodies, counts ++ carried ++ captures, carriedTypes)
    | "branch" => do
        unless items.size == 5 do throw "malformed branch"
        let captures ← lift (readNats "captures" items[2]!)
        let captureTypes ← lift (captures.mapM locatedOf)
        let (roles, conditions) ← lift (readParticipants
          (← lift (readArray "participants" items[1]!)))
        lift (context.acting roles)
        lift (context.require (participantConditions roles captureTypes) s!"participants {roles}")
        lift (context.checkOperands scope conditions (conditions.map fun _ => .bool) (roles.map some))
        let inner := { context with enclosing := some roles }
        let onTrue ← buildProtocol inner captureTypes none items[3]!
        let outputs := onTrue.outputs
        if context.checked && !Located.heldBy roles outputs then
          throw s!"wrong holder: a branch output is held by a role that is not a participant (holders {outputs.map (·.holder)}, participants {roles})"
        let onFalse ← buildProtocol inner captureTypes (some outputs) items[4]!
        let capturesTerm ← build (locatedsTerm captureTypes)
        let outputsTerm ← build (locatedsTerm outputs)
        let op := mkApp7 (mkConst ``Zkc.Core.ProtocolOp.branch) operations headers deployed
          (natsTerm roles) capturesTerm outputsTerm proofTrue
        let bodies := regionsCons dialect locatedType capturesTerm outputsTerm
          [(capturesTerm, outputsTerm)] onTrue.term
          (regionsCons dialect locatedType capturesTerm outputsTerm [] onFalse.term (regionsNil dialect))
        pure (op, bodies, conditions ++ captures, outputs)
    | "apply" => do
        unless items.size == 5 do throw "malformed apply"
        let row ← lift (readNat "callee" items[1]!)
        let roleMap ← lift (readNats "role map" items[2]!)
        let site ← lift (readNat "site" items[3]!)
        let operands ← lift (readNats "operands" items[4]!)
        let callee ← lift (context.callee row)
        let entry := context.decoded.definitions[row]!
        let .protocol roles inputs outputs _ := entry.signature
          | throw s!"apply of definition {row}, which is not a protocol"
        lift (context.acting roleMap)
        lift (context.require (roleMapConditions roles roleMap)
          s!"role map {roleMap} for a protocol of {roles} roles")
        lift (context.permitted row)
        useSite site
        useCallee row
        let rename := Located.rename roleMap
        lift (context.checkLocated scope operands (inputs.map rename))
        let op := mkAppN (mkConst ``Zkc.Core.ProtocolOp.apply) #[operations, headers, deployed,
          nat roles, ← build (locatedsTerm inputs), ← build (locatedsTerm outputs),
          context.agreementTerms[row]!, bool entry.specificationOnly, callee, natsTerm roleMap,
          nat site, proofFalse]
        pure (op, regionsNil dialect, operands, outputs.map rename)
    | "oracle_send" | "oracle_compute" | "oracle_read" =>
        throw s!"{head} is not supported by this importer"
    | other => throw s!"unknown protocol instruction {other}"
end

/-- The importer's checks of a signature's agreements over one list of ports: one
type, by typing, and the model's conditions on holders and ports. -/
def Context.checkAgreements (context : Context) (ports : List Located)
    (agreements : List AgreementEntry) : Read Unit := do
  unless context.checked do return
  for agreement in agreements do
    let type := (ports[agreement.ports.head!]!).type
    for port in agreement.ports do
      unless (ports[port]!).type == type do
        throw s!"wrong type: an agreement names ports of types {renderTy type} and {renderTy (ports[port]!).type} (ports {agreement.ports})"
  context.require
    (copyConditions (agreements.map fun agreement => agreement.ports.map fun port =>
        (ports[port]!).holder) (agreements.flatMap (·.ports)))
    s!"agreements {agreements.map (·.ports)}"

/-- The typed definition term of a package definition, and the agreements of its
signature. -/
def definitionTerm (context : Context) (entry : DefinitionEntry) : Builder (Expr × Expr) := do
  let headers := context.headers
  match entry.signature with
  | .function inputs outputs =>
      let body ← buildLocal context inputs (some outputs) entry.body
      let term := mkApp6 (mkConst ``Zkc.Core.Definition.function) context.operations headers
        (← build (tysTerm inputs)) (← build (tysTerm outputs)) (bool entry.specificationOnly)
        body.term
      pure (term, default)
  | .protocol roles inputs outputs agreements =>
      lift (context.require (portConditions roles (inputs ++ outputs))
        s!"{roles} roles, port holders {(inputs ++ outputs).map (·.holder)}")
      lift (context.checkAgreements inputs (agreements.filter (!·.overOutputs)))
      lift (context.checkAgreements outputs (agreements.filter (·.overOutputs)))
      let agreementsTerm ← build (signatureAgreements inputs outputs agreements)
      let body ← buildProtocol context inputs (some outputs) entry.body
      let sites := (← get).sites.toList
      if context.checked then
        if let some violation := sitesViolation sites then
          throw s!"{describe violation} (sites in order of occurrence: {sites})"
      let term := mkApp8 (mkConst ``Zkc.Core.Definition.protocol) context.operations headers
        (← build (locatedsTerm inputs)) (← build (locatedsTerm outputs)) (nat roles)
        agreementsTerm (bool entry.specificationOnly) body.term
      pure (term, agreementsTerm)

/-! ## The command -/

structure Settings where
  stage : String := "original"
  checked : Bool := true
  profile : Bool := false

/-- The local names that the importer gives its own declarations. -/
def reservedNames : List Name := [`catalogue, `operations, `row]

def definitionName (decoded : Decoded) (row : Nat) : Name :=
  match decoded.names.definitions[row]? with
  | some name => if name.isEmpty then Name.mkSimple s!"definition{row}" else Name.mkSimple name
  | none => Name.mkSimple s!"definition{row}"

/-- The number of instructions of a region, nested regions included. It counts any
two-element array of arrays inside an instruction as a region, so it may overcount;
it only sizes the kernel's recursion limit. -/
partial def instructionCount : Json → Nat
  | .arr #[.arr instructions, _] => instructions.foldl (fun total instruction =>
      total + 1 + match instruction with
        | .arr items => items.foldl (fun nested item => nested + nestedCount item) 0
        | _ => 0) 0
  | _ => 0
where
  nestedCount : Json → Nat
    | json@(.arr #[.arr _, .arr _]) => instructionCount json
    | .arr items => items.foldl (fun total item => total + nestedCount item) 0
    | _ => 0

/-- Run with a recursion limit that grows with `depth`. The kernel's recursion
follows the nesting of a term: of a region's operations, of an operation table's
rows, of a row variable's position. -/
def withDepth {α : Type} (depth : Nat) (action : CoreM α) : CoreM α :=
  withOptions (fun options => maxRecDepth.set (Elab.async.set options false)
    (max (maxRecDepth.get options) (16 * depth + 512))) action

/-- Add a declaration, checked by the kernel now. -/
def addChecked (declaration : Declaration) (depth : Nat := 0) : CoreM Unit :=
  withDepth depth (addDecl declaration (forceExpose := true))

/-- Add a definition. The catalogue is compiled, so that a tool may evaluate it. The
operation table, a row variable and a program are not: their terms repeat the lists
they are typed over, and nothing executes them. -/
def addDefinition (name : Name) (type value : Expr) (depth : Nat := 0) (compile : Bool := false) :
    CoreM Unit := do
  let declaration := Declaration.defnDecl {
    name, levelParams := [], type := type, value := value,
    hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe }
  addChecked declaration depth
  if compile then withDepth depth (compileDecl declaration)
  else modifyEnv (addNoncomputable · name)

/-- The residual condition that the kernel evaluates `Definition.violation` to, when
it refuses a well-typed definition. -/
def explainViolation (violation : Expr) (error : Exception) : CoreM MessageData := do
  let env ← getEnv
  let evaluated := do
    let verdict ← Kernel.whnf env {} violation
    if verdict.isAppOfArity ``Option.some 2 then Kernel.whnf env {} verdict.appArg!
    else pure verdict
  match evaluated with
  | .ok found =>
      match found.constName? >>= fun name => violations.lookup name with
      | some violation =>
          return m!"residual condition {found.constName!.getString!}: {describe violation}"
      | none => return m!"an unexpected cause: {error.toMessageData}"
  | .error _ => return m!"an unexpected cause: {error.toMessageData}"

/-- The terms of the imported definitions that the table and entry equations name. -/
structure Imported where
  operations : Expr
  /-- `headerLists[j]` is the list of the headers of rows `j-1, …, 0`. -/
  headerLists : Array Expr
  headerTerms : Array Expr
  /-- The definition constants, the proofs of their residual conditions and the
  program constants, one per definition. -/
  definitions : Array Expr
  wellFormed : Array Expr
  programs : Array Expr
  /-- The names of the table equations, one per definition. -/
  tables : Array Name

/-- The program of the definitions before `row`. -/
def Imported.previous (imported : Imported) (row : Nat) : Expr :=
  if row == 0 then mkApp (mkConst ``Zkc.Core.Program.nil) imported.operations
  else imported.programs[row - 1]!

/-- The table of the program up to definition `row`; of no definition for `none`. -/
def Imported.table (imported : Imported) (model : Expr) (row : Nat) : Expr :=
  mkApp4 (mkConst ``Zkc.Core.Program.table) model imported.operations
    imported.headerLists[row + 1]! imported.programs[row]!

/-- The table of the definitions before `row`. -/
def Imported.before (imported : Imported) (model : Expr) (row : Nat) : Expr :=
  mkApp4 (mkConst ``Zkc.Core.Program.table) model imported.operations imported.headerLists[row]!
    (imported.previous row)

def Imported.meaning (imported : Imported) (model : Expr) (row : Nat) : Expr :=
  mkApp5 (mkConst ``Zkc.Core.Program.meaning) model imported.operations imported.headerLists[row]!
    imported.headerTerms[row]! imported.programs[row]!

def meaningFamily (model : Expr) : Expr := mkApp (mkConst ``Zkc.Core.Header.Meaning) model

def modelBinder (body : Expr) (lambda : Bool) : Expr :=
  if lambda then mkLambda `model .default (mkConst ``Zkc.Core.Model) body
  else mkForall `model .default (mkConst ``Zkc.Core.Model) body

/-- The table equation of definition `row`, already among `imported.programs`: its
table is its own meaning followed by the table of the definitions before it. The
kernel checks it by unfolding the program's constant once. -/
def tableEquation (imported : Imported) (row : Nat) : Expr × Expr :=
  let model := mkBVar 0
  let headers := imported.headerLists[row]!
  let header := imported.headerTerms[row]!
  let extended := imported.headerLists[row + 1]!
  let program := imported.programs[row]!
  let tableType := mkApp3 (mkConst ``Zkc.Source.Values) headerType (meaningFamily model) extended
  let unfolded := mkApp6 (mkConst ``Zkc.Source.Values.cons) headerType (meaningFamily model) header
    headers (imported.meaning model row) (imported.before model row)
  let proof := mkAppN (mkConst ``Zkc.Core.Program.table_unfold) #[model, imported.operations,
    headers, header, program, imported.previous row, imported.definitions[row]!,
    imported.wellFormed[row]!,
    mkApp2 (mkConst ``Eq.refl [Level.one])
      (mkApp2 (mkConst ``Zkc.Core.Program) imported.operations extended) program]
  (modelBinder (mkApp3 (mkConst ``Eq [Level.one]) tableType (imported.table model row) unfolded)
      false,
   modelBinder proof true)

/-- The entry equation of definition `row` for its callee: the callee's entry in the
table of the definitions before `row` is the callee's own meaning. Its proof walks
the table equations up to `row - 1`, from the callee or, when an earlier definition
`start.1` has an entry equation `start.2` for the same callee, from that equation.
The kernel unfolds no table. -/
def entryEquation (imported : Imported) (row callee : Nat) (start : Option (Nat × Name)) :
    Expr × Expr := Id.run do
  let model := mkBVar 0
  let calleeHeader := imported.headerTerms[callee]!
  let meaning := imported.meaning model callee
  let unfolded (at_ : Nat) : Expr := mkApp (mkConst imported.tables[at_]!) model
  -- The position and the proof for the table of the definitions before `first`.
  let (first, initialPosition, initialProof) := match start with
    | some (earlier, equation) =>
        (earlier, calleeVar imported.headerLists imported.headerTerms earlier callee,
          mkApp (mkConst equation) model)
    | none =>
        (callee + 1,
          mkApp3 (mkConst ``Zkc.Source.Var.here) headerType imported.headerLists[callee]!
            calleeHeader,
          mkAppN (mkConst ``Zkc.Core.Program.entry_here) #[model, imported.headerLists[callee]!,
            calleeHeader, imported.table model callee, meaning, imported.before model callee,
            unfolded callee])
  let mut position := initialPosition
  let mut proof := initialProof
  for later in [first:row] do
    proof := mkAppN (mkConst ``Zkc.Core.Program.entry_there) #[model, imported.headerLists[later]!,
      imported.headerTerms[later]!, calleeHeader, imported.table model later,
      imported.meaning model later, imported.before model later, position, meaning,
      unfolded later, proof]
    position := mkApp5 (mkConst ``Zkc.Source.Var.there) headerType imported.headerLists[later]!
      calleeHeader imported.headerTerms[later]! position
  let entry := mkApp6 (mkConst ``Zkc.Source.Values.get) headerType (meaningFamily model)
    imported.headerLists[row]! calleeHeader (imported.before model row) position
  let statement := mkApp3 (mkConst ``Eq [Level.one])
    (mkApp (meaningFamily model) calleeHeader) entry meaning
  (modelBinder statement false, modelBinder proof true)

/-- Add the catalogue, the operation table, the row constants and, per package
definition, its declarations with its table and entry equations, each checked by the
kernel. -/
def addPackage (name : Name) (source : String) (settings : Settings) : CommandElabM Unit := do
  let json ← match Json.parse source with
    | .ok json => pure json
    | .error message => throwError "malformed JSON: {message}"
  let decoded ← match readPackage settings.stage json with
    | .ok decoded => pure decoded
    | .error message => throwError "refused package: {message}"
  let run {α : Type} (action : Build α) (terms : Terms) : CommandElabM (α × Terms) :=
    match action.run terms with
    | .ok result => pure result
    | .error message => throwError "refused package: {message}"
  let (catalogue, terms) ← run (catalogueTerm decoded) {}
  liftCoreM <| addDefinition (name ++ `catalogue) (mkConst ``Zkc.Core.Catalogue) catalogue
    (decoded.types.size + decoded.operations.size) (compile := true)
  let (table, terms) ← run (tableOf decoded.operations) terms
  let mut terms := terms
  let operationsName := name ++ `operations
  try
    liftCoreM <| addDefinition operationsName
      (mkApp (mkConst ``List [Level.zero]) signatureType) table.suffixes[0]! decoded.operations.size
  catch error =>
    throwError "the kernel refused the operation table: {error.toMessageData}"
  let operations := mkConst operationsName
  let mut rows := #[]
  for (entry, row) in decoded.operations.zipIdx do
    let rowName := name ++ `row ++ Name.mkSimple entry.identity
    try
      liftCoreM <| addDefinition rowName
        (mkApp3 (mkConst ``Zkc.Source.Var) signatureType operations table.rows[row]!)
        (table.var row) row
    catch error =>
      throwError "the kernel refused operation row {row} ({entry.identity}): {error.toMessageData}"
    rows := rows.push (mkConst rowName)
  let mut headerLists := #[listOf headerType []]
  let mut headerTerms := #[]
  let mut agreementTerms := #[]
  let mut definitions := #[]
  let mut wellFormed := #[]
  let mut programs := #[]
  let mut tables := #[]
  -- The latest entry equation of every callee: the definition that has it, and its name.
  let mut entries : Std.HashMap Nat (Nat × Name) := {}
  let mut previous := mkApp (mkConst ``Zkc.Core.Program.nil) operations
  let mut used : Std.HashMap Name Unit := {}
  for (entry, row) in decoded.definitions.zipIdx do
    let localName := definitionName decoded row
    if used.contains localName then
      throwError "refused package: two definitions would be named {localName}"
    if reservedNames.contains localName then
      throwError "refused package: the definition name {localName} is reserved for the importer's declarations"
    used := used.insert localName ()
    let declName := name ++ localName
    let roles := match entry.signature with
      | .protocol roles .. => roles
      | .function .. => 0
    let context : Context := {
      decoded, operations, rows, definition := row, definitionName := s!"{row} ({localName})",
      roles, enclosing := none, deployed := !entry.specificationOnly,
      checked := settings.checked, headerLists, headerTerms, agreementTerms }
    let started ← IO.monoNanosNow
    let built := ((definitionTerm context entry).run {}).run terms
    let (((definition, agreements), uses), nextTerms) ← match built with
      | .ok result => pure result
      | .error message => throwError "refused definition {row} ({localName}): {message}"
    let (header, nextTerms) ← match (headerTerm entry.signature entry.specificationOnly).run nextTerms with
      | .ok result => pure result
      | .error message => throwError "refused definition {row} ({localName}): {message}"
    terms := nextTerms
    if let some siteNames := decoded.names.sites[row]? then
      unless siteNames.isEmpty || siteNames.size == uses.sites.size do
        throwError "refused definition {row} ({localName}): site names: {siteNames.size} names for {uses.sites.size} sites"
    let headers := headerLists[row]!
    let extended := mkApp3 (mkConst ``List.cons [Level.zero]) headerType header headers
    let built ← IO.monoNanosNow
    -- The kernel type-checks the definition, then decides the residual conditions by
    -- evaluating `Definition.violation` in the statement of `wellFormed`, the proof
    -- that `Program.snoc` takes.
    let definitionConstant := declName ++ `definition
    try
      liftCoreM <| addDefinition definitionConstant
        (mkApp3 (mkConst ``Zkc.Core.Definition) operations headers header) definition
        (instructionCount entry.body)
    catch error =>
      throwError "the kernel refused definition {row} ({localName}): typing: {error.toMessageData}"
    let typed ← IO.monoNanosNow
    let violation := mkApp4 (mkConst ``Zkc.Core.Definition.violation) operations headers header
      (mkConst definitionConstant)
    let wellFormedName := declName ++ `wellFormed
    try
      liftCoreM <| addChecked (Declaration.thmDecl {
        name := wellFormedName, levelParams := [],
        type := mkApp3 (mkConst ``Eq [Level.one]) verdictType violation noViolation,
        value := proofWellFormed }) (instructionCount entry.body)
    catch error =>
      let cause ← liftCoreM <| explainViolation violation error
      throwError "the kernel refused definition {row} ({localName}): {cause}"
    try
      liftCoreM <| addDefinition declName (mkApp2 (mkConst ``Zkc.Core.Program) operations extended)
        (mkAppN (mkConst ``Zkc.Core.Program.snoc) #[operations, headers, header, previous,
          mkConst definitionConstant, mkConst wellFormedName])
    catch error =>
      throwError "the kernel refused the program of definition {row} ({localName}): {error.toMessageData}"
    let checked ← IO.monoNanosNow
    headerTerms := headerTerms.push header
    headerLists := headerLists.push extended
    agreementTerms := agreementTerms.push agreements
    definitions := definitions.push (mkConst definitionConstant)
    wellFormed := wellFormed.push (mkConst wellFormedName)
    programs := programs.push (mkConst declName)
    tables := tables.push (declName ++ `table)
    previous := mkConst declName
    -- The table equation of the definition, and its entry equations, one per callee
    -- it uses.
    let imported : Imported := {
      operations, headerLists, headerTerms, definitions, wellFormed, programs, tables }
    let addEquation (equationName : Name) (equation : Expr × Expr) : CommandElabM Unit := do
      try
        liftCoreM <| addChecked (Declaration.thmDecl {
          name := equationName, levelParams := [], type := equation.1, value := equation.2 })
          (row + 32)
      catch error =>
        throwError "the kernel refused the equation {equationName} of definition {row} ({localName}): {error.toMessageData}"
    addEquation (declName ++ `table) (tableEquation imported row)
    let tabled ← IO.monoNanosNow
    for callee in uses.callees.qsort (· < ·) do
      let equationName := declName ++ `entry ++ definitionName decoded callee
      addEquation equationName (entryEquation imported row callee entries[callee]?)
      entries := entries.insert callee (row, equationName)
    let finished ← IO.monoNanosNow
    if settings.profile then
      let milliseconds (duration : Nat) : Nat := duration / 1000000
      logInfo m!"core import {declName}: term construction {milliseconds (built - started)} ms, kernel: typing {milliseconds (typed - built)} ms, residual conditions {milliseconds (checked - typed)} ms, table equation {milliseconds (tabled - checked)} ms, {uses.callees.size} entry equations {milliseconds (finished - tabled)} ms"

/-- Import a package. A refusal, by the importer or by the kernel, leaves the
environment as it was: no declaration of a partly imported package remains. -/
def importPackage (name : Name) (source : String) (settings : Settings) : CommandElabM Unit := do
  let before ← getEnv
  try
    addPackage name source settings
  catch error =>
    setEnv before
    throw error

/-- Equal JSON values, ignoring whitespace and object member order. -/
def sameJson (left right : String) : Except String Bool := do
  let left ← Json.parse left
  let right ← Json.parse right
  pure (left == right)

/-- `import_core name [stage "s"] [with option, …] from "<json>" [fixture "<path>"]`. -/
syntax (name := importCore) "import_core " ident (&" stage " str)? (" with " ident,+)?
  " from " str (&" fixture " str)? : command

/-- `import_core name [stage "s"] [with option, …] from file "<path>"`. -/
syntax (name := importCoreFile) "import_core " ident (&" stage " str)? (" with " ident,+)?
  " from " &"file " str : command

def settingsOf (stage : Option (TSyntax `str)) (options : Array Ident) : CommandElabM Settings := do
  let mut settings : Settings := {}
  if let some stage := stage then settings := { settings with stage := stage.getString }
  for option in options do
    match option.getId with
    | `kernel_only => settings := { settings with checked := false }
    | `profile => settings := { settings with profile := true }
    | other => throwErrorAt option "unknown import option {other}; expected kernel_only or profile"
  pure settings

elab_rules : command
  | `(import_core $name:ident $[stage $stage]? $[with $options,*]? from $source:str
        $[fixture $fixture]?) => do
      let settings ← settingsOf stage (options.map (·.getElems) |>.getD #[])
      let text := source.getString
      if let some fixture := fixture then
        let path := fixture.getString
        match sameJson text (← IO.FS.readFile path) with
        | .ok true => pure ()
        | .ok false => throwErrorAt fixture "the embedded package differs from {path}"
        | .error message => throwErrorAt fixture "malformed JSON in the comparison with {path}: {message}"
      importPackage name.getId text settings
  | `(import_core $name:ident $[stage $stage]? $[with $options,*]? from file $path:str) => do
      let settings ← settingsOf stage (options.map (·.getElems) |>.getD #[])
      importPackage name.getId (← IO.FS.readFile path.getString) settings

end Zkc.Tools.Core
