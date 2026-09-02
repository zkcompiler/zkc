import Lean.Data.Json
import M0.Datum
import M0.PCGraph

/-!
# Transport between the runner and the Lean executable

The K1 oracle's JSON value transport
(`evaluation/k1-executable-foundations/oracle/CONTRACT.md` Section 3) carries a
datum as `{"tag": ...}` objects with decimal strings for naturals, integers,
ordinals, and cases, and lowercase hexadecimal for bytes. JSON is transport,
not the identity encoding; nothing here is part of the kernel definitions,
and this module is the only one that imports the Lean JSON library.
-/

namespace M0.Transport

open Lean

/-- Parse lowercase or uppercase hexadecimal into octets. -/
def octetsOfHex (s : String) : Except String (List Octet) := do
  let digit (c : Char) : Except String Nat :=
    if c.isDigit then pure (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c && c ≤ 'F' then pure (c.toNat - 'A'.toNat + 10)
    else throw s!"not a hexadecimal digit: {c}"
  let rec go : List Char → Except String (List Octet)
    | [] => pure []
    | [_] => throw "odd-length hexadecimal string"
    | hi :: lo :: rest => do
      let h ← digit hi
      let l ← digit lo
      let tail ← go rest
      pure ((h * 16 + l) :: tail)
  go s.toList

/-- Render octets as lowercase hexadecimal. -/
def hexOfOctets (bs : List Octet) : String :=
  let digits := "0123456789abcdef".toList
  String.ofList (bs.flatMap fun b => [digits.getD (b / 16) '?', digits.getD (b % 16) '?'])

/-- A canonical decimal string: no sign, no leading zero, no whitespace. -/
def natOfDecimal (s : String) : Except String Nat :=
  if s.isEmpty then throw "empty decimal"
  else if s.length > 1 && s.front = '0' then throw s!"leading zero in decimal {s}"
  else match s.toNat? with
    | some n => pure n
    | none => throw s!"not a canonical decimal: {s}"

/-- A canonical signed decimal string; negative zero is refused. -/
def intOfDecimal (s : String) : Except String Int :=
  if s.front = '-' then do
    let n ← natOfDecimal (String.ofList (s.toList.drop 1))
    if n = 0 then throw "negative zero" else pure (-(n : Int))
  else do
    let n ← natOfDecimal s
    pure (n : Int)

private def field (j : Json) (name : String) : Except String Json :=
  match j.getObjVal? name with
  | .ok v => pure v
  | .error e => throw s!"missing field {name}: {e}"

private def stringField (j : Json) (name : String) : Except String String := do
  match (← field j name) with
  | .str s => pure s
  | _ => throw s!"field {name} is not a string"

private def arrayField (j : Json) (name : String) : Except String (Array Json) := do
  match (← field j name) with
  | .arr a => pure a
  | _ => throw s!"field {name} is not an array"

/-- The oracle's JSON value transport, read into a datum. -/
partial def datumOfJson (j : Json) : Except String Datum := do
  match (← stringField j "tag") with
  | "unit" => pure .unit
  | "bool" =>
    match (← field j "value") with
    | .bool b => pure (.bool b)
    | _ => throw "bool value is not a JSON boolean"
  | "nat" => pure (.nat (← natOfDecimal (← stringField j "value")))
  | "int" => pure (.int (← intOfDecimal (← stringField j "value")))
  | "bytes" => pure (.bytes (← octetsOfHex (← stringField j "value")))
  | "symbol" =>
    let s ← stringField j "value"
    pure (.symbol (s.toUTF8.toList.map UInt8.toNat))
  | "seq" =>
    let items ← arrayField j "items"
    pure (.seq (← items.toList.mapM datumOfJson))
  | "record" =>
    let fields ← arrayField j "fields"
    let fs ← fields.toList.mapM fun f => do
      let o ← natOfDecimal (← stringField f "ordinal")
      let v ← datumOfJson (← field f "value")
      pure (o, v)
    pure (.record fs)
  | "variant" =>
    let c ← natOfDecimal (← stringField j "case")
    let v ← datumOfJson (← field j "value")
    pure (.variant c v)
  | other => throw s!"unknown transport tag {other}"

/-- A `PCClass` by its Section 11 name. -/
def classOfName : String → Except String PCClass
  | "StaticPublic" => pure .staticPublic
  | "PublicHistory" => pure .publicHistory
  | "VerifierPrivate" => pure .verifierPrivate
  | "Invalid" => pure .invalid
  | other => throw s!"unknown PCClass name {other}"

def nameOfClass : PCClass → String
  | .staticPublic => "StaticPublic"
  | .publicHistory => "PublicHistory"
  | .verifierPrivate => "VerifierPrivate"
  | .invalid => "Invalid"

private def natArray (j : Json) : Except String (List Nat) := do
  match j with
  | .arr a => a.toList.mapM fun v =>
      match v.getNat? with
      | .ok n => pure n
      | .error e => throw s!"not a natural number: {e}"
  | _ => throw "not an array"

private def natField (j : Json) (name : String) : Except String Nat := do
  match (← field j name).getNat? with
  | .ok n => pure n
  | .error e => throw s!"field {name} is not a natural number: {e}"

/-- One exported node: tag, reference arguments, and its canonical body. -/
structure NodeRow where
  tag : Nat
  args : List Nat
  key : List Octet

def nodeRowOfJson (j : Json) : Except String NodeRow := do
  pure {
    tag := ← natField j "tag"
    args := ← natArray (← field j "args")
    key := ← octetsOfHex (← stringField j "key")
  }

/-- One exported transfer kind. -/
def transferOfJson (j : Json) : Except String Transfer := do
  match (← stringField j "kind") with
  | "constant" => pure (.constant (← classOfName (← stringField j "class")))
  | "join-incoming" => pure .joinIncoming
  | "publish-join-incoming" => pure .publishJoinIncoming
  | "publish-of" => pure (.publishOf (← natField j "node"))
  | "join-of" => pure (.joinOf (← natArray (← field j "nodes")))
  | "challenge" =>
    pure (.challenge (← natField j "activity")
      (← natArray (← field j "conditions")) (← natArray (← field j "priors")))
  | other => throw s!"unknown transfer kind {other}"

/-- One exported carrier table. -/
structure CarrierTable where
  carrier : String
  nodes : Array NodeRow
  edges : List (Nat × Nat)
  transfers : Array Transfer
  expectedOrder : List Nat
  expectedClasses : List PCClass

def carrierOfJson (j : Json) : Except String CarrierTable := do
  let nodes ← (← arrayField j "nodes").mapM nodeRowOfJson
  let edges ← (← arrayField j "edges").toList.mapM fun e => do
    match (← natArray e) with
    | [s, t] => pure (s, t)
    | _ => throw "edge is not a pair"
  let transfers ← (← arrayField j "transfers").mapM transferOfJson
  let expectedOrder ← natArray (← field j "expected_order")
  let expectedClasses ← (← arrayField j "expected_classes").toList.mapM fun c =>
    match c with
    | .str s => classOfName s
    | _ => throw "expected class is not a string"
  pure { carrier := ← stringField j "carrier", nodes, edges, transfers, expectedOrder, expectedClasses }

/-! M1 transports canonical source bytes separately from D1 expected outputs. -/

def pcNodeOfJson (j : Json) : Except String PCNode := do
  match ← natArray j with
  | tag :: args =>
      match PCNode.ofTagArgs tag args with
      | some node => pure node
      | none => throw "PCNode has an unknown tag or arity"
  | [] => throw "PCNode is empty"

def pcNodesOfJson (j : Json) : Except String (List PCNode) := do
  match j with
  | .arr rows => rows.toList.mapM pcNodeOfJson
  | _ => throw "PCNode table is not an array"

def pcEdgeOfJson (j : Json) : Except String PCEdge := do
  match j with
  | .arr rows =>
      match rows.toList with
      | [source, target] => pure (← pcNodeOfJson source, ← pcNodeOfJson target)
      | _ => throw "PC edge is not a pair"
  | _ => throw "PC edge is not an array"

def pcEdgesOfJson (j : Json) : Except String (List PCEdge) := do
  match j with
  | .arr rows => rows.toList.mapM pcEdgeOfJson
  | _ => throw "PC edge table is not an array"

def classOfOrdinal : Nat → Except String PCClass
  | 0 => pure .staticPublic
  | 1 => pure .publicHistory
  | 2 => pure .verifierPrivate
  | 3 => pure .invalid
  | other => throw s!"unknown PCClass ordinal {other}"

def classRowOfJson (j : Json) : Except String (PCNode × PCClass) := do
  match j with
  | .arr rows =>
      match rows.toList with
      | [node, clsJson] =>
          pure (← pcNodeOfJson node, ← classOfOrdinal (← clsJson.getNat?.mapError toString))
      | _ => throw "class row is not a pair"
  | _ => throw "class row is not an array"

def classRowsOfJson (j : Json) : Except String (List (PCNode × PCClass)) := do
  match j with
  | .arr rows => rows.toList.mapM classRowOfJson
  | _ => throw "class table is not an array"

def coneRowOfJson (j : Json) : Except String (Nat × List PCNode) := do
  match j with
  | .arr rows =>
      match rows.toList with
      | [oracle, nodes] => pure (← oracle.getNat?.mapError toString, ← pcNodesOfJson nodes)
      | _ => throw "logical-cone row is not a pair"
  | _ => throw "logical-cone row is not an array"

def coneRowsOfJson (j : Json) : Except String (List (Nat × List PCNode)) := do
  match j with
  | .arr rows => rows.toList.mapM coneRowOfJson
  | _ => throw "logical-cone table is not an array"

structure ExpectedGraph where
  nodes : List PCNode
  edges : List PCEdge
  order : List PCNode
  classes : List (PCNode × PCClass)
  sinks : List PCNode
  acceptanceSinks : List PCNode
  privatePredecessors : List PCNode
  logicalCones : List (Nat × List PCNode)
  logicalIntersections : List (Nat × List PCNode)
  deriving Repr

def expectedGraphOfJson (j : Json) : Except String ExpectedGraph := do
  pure {
    nodes := ← pcNodesOfJson (← field j "nodes")
    edges := ← pcEdgesOfJson (← field j "edges")
    order := ← pcNodesOfJson (← field j "topological")
    classes := ← classRowsOfJson (← field j "classes")
    sinks := ← pcNodesOfJson (← field j "sinks")
    acceptanceSinks := ← pcNodesOfJson (← field j "acceptance_sinks")
    privatePredecessors := ← pcNodesOfJson (← field j "private_predecessors")
    logicalCones := ← coneRowsOfJson (← field j "logical_cones")
    logicalIntersections := ← coneRowsOfJson (← field j "logical_intersections")
  }

def moduleDeclOfJson (j : Json) : Except String ModuleDecl := do
  let moduleRef ← octetsOfHex (← stringField j "module_ref_hex")
  let ordinal ← natField j "ordinal"
  let body ← octetsOfHex (← stringField j "body_hex")
  let datum ← match decode body with
    | some datum => pure datum
    | none => throw "module declaration bytes do not decode"
  match M0.moduleDeclOfDatum moduleRef ordinal datum with
  | some declaration => pure declaration
  | none => throw "module declaration datum has another shape"

structure ConstructionCarrier where
  carrier : String
  core : Core
  modules : List ModuleDecl
  expected : ExpectedGraph
  deriving Repr

def constructionCarrierOfJson (j : Json) : Except String ConstructionCarrier := do
  let input ← field j "input"
  let coreBody ← octetsOfHex (← stringField input "core_domain_hex")
  let coreDatum ← match decode coreBody with
    | some datum => pure datum
    | none => throw "Core-domain bytes do not decode"
  let core ← match coreOfDatum coreDatum with
    | some core => pure core
    | none => throw "Core-domain datum has another fourteen-table shape"
  let modules ← (← arrayField input "module_declarations").toList.mapM moduleDeclOfJson
  pure {
    carrier := ← stringField j "carrier"
    core := core
    modules := modules
    expected := ← expectedGraphOfJson (← field j "expected")
  }

/-- Public readers for the runner's input file. -/
def readString (j : Json) (name : String) : Except String String := stringField j name
def readArray (j : Json) (name : String) : Except String (Array Json) := arrayField j name
def readField (j : Json) (name : String) : Except String Json := field j name

end M0.Transport
