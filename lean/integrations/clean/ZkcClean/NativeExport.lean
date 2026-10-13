import Clean.Table.Json
import Clean.Table.Inductive
import Clean.Air.FlatComponent
import ZkcClean.Native

/-! Source extraction for the optional native Bundle adapter.

The payload retains Clean expressions and cell assignments. Lookup interpretations
and public bindings are explicit adapter inputs; arbitrary Lean propositions are
not serialized. This module does not extend the channel-free correspondence theorem
in `ZkcClean.Export` to native Bundles.
-/

namespace ZkcClean.NativeExport
open Lean

variable {F : Type} [FiniteField F]

-- The adapter always emits canonical naturals, independent of a client's
-- arbitrary `ToJson F` instance. A source envelope supplies the residue law.
local instance : ToJson F where
  toJson value := toJson (FiniteField.val value)

def source (presentation : PrimePresentation F) (table publicLayout lookups channels : Json) : Json :=
  Json.mkObj [("format", "zkc.clean-export/0"), ("field", toJson presentation.modulus),
    ("table", table), ("public", publicLayout), ("lookups", lookups), ("channels", channels)]

/-- Preserve the proof-facing interaction mode even though Bundle balance uses
only the message and field weight. Requirements/guarantees remain Lean predicates.
-/
def flatOperation (op : FlatOperation F) : Json := match op with
  | .interact i => Json.mkObj [("interact", Json.mkObj [
      ("channel", toJson i.channel.name), ("arity", toJson i.channel.arity),
      ("multiplicity", toJson i.mult), ("message", toJson i.msg.toArray),
      ("assume_guarantees", toJson i.assumeGuarantees)])]
  | op => toJson op

def context {S : Type → Type} [ProvableType S] {W : ℕ+}
    (auxiliaryOffset : Nat) (source : TableConstraint W S F Unit) : Json :=
  let ctx := (source .empty).2
  let auxiliary := buildAuxMap ctx.assignment
  let cells := ctx.assignment.vars.mapIdx fun index cell => match cell with
    | .input offset => toJson offset
    | .aux _ => match auxiliary[index]? with
      | some column => Json.mkObj [("row", toJson (W.val - 1)),
          ("column", toJson (column + auxiliaryOffset))]
      | none => Json.null
  Json.mkObj [("window", toJson W.val), ("vars", toJson cells.toArray),
    ("circuit", toJson (ctx.circuit.toFlat.map flatOperation))]

def operation {S : Type → Type} [ProvableType S]
    (auxiliaryOffset : Nat) : TableOperation S F → Json
  | .boundary row c => Json.mkObj [("type", "Boundary"),
      ("row", toJson (match row with
        | .fromStart i => (i : Int)
        | .fromEnd i => -(i : Int) - 1)), ("context", context auxiliaryOffset c)]
  | .everyRow c => Json.mkObj [("type", "EveryRow"), ("context", context auxiliaryOffset c)]
  | .everyRowExceptLast c => Json.mkObj [("type", "EveryRowExceptLast"),
      ("context", context auxiliaryOffset c)]

def table {S : Type → Type} [ProvableType S]
    (origin : Name) (height : Nat) (operations : List (TableOperation S F)) : Json :=
  let (encoded, auxiliary) := operations.foldl (fun (encoded, offset) op =>
    let width := match op with
      | .boundary _ c => c.finalAssignment.numAux
      | .everyRow c => c.finalAssignment.numAux
      | .everyRowExceptLast c => c.finalAssignment.numAux
    (encoded.push (operation offset op), offset + width)) (#[], 0)
  Json.mkObj [
    ("origin", toJson origin.toString), ("model", "table"), ("height", toJson height),
    ("width", toJson (size S + auxiliary)),
    ("operations", toJson encoded)]

def component (origin : Name) (height : Nat) (source : Air.Flat.Component F) : Json :=
  Json.mkObj [
    ("origin", toJson origin.toString), ("model", "component"), ("height", toJson height),
    ("width", toJson source.width),
    ("operations", toJson (source.operations.toFlat.map flatOperation))]

/-- Public state cells, with sizes derived from the state's `ProvableType`.
This is an explicit parameterized boundary contract, not predicate extraction.
-/
def stateBoundary (origin : Name) (State : Type → Type) [ProvableType State] : Json :=
  let width := size State
  let bindings := ((List.range width).map fun column =>
    Json.mkObj [("row", "first"), ("column", toJson column),
      ("slot", toJson column)]) ++
    ((List.range width).map fun column =>
    Json.mkObj [("row", "last"), ("column", toJson column),
      ("slot", toJson (width + column))])
  Json.mkObj [("origin", toJson origin.toString), ("size", toJson (2 * width)),
    ("bindings", toJson bindings)]

/-- Couple an actual inductive transition with the state boundaries of
`InductiveTable.tableConstraints`. The equality-to-public translation remains
an adapter contract; no native correspondence theorem is claimed here.
-/
def inductiveTable {State Input : Type → Type} [ProvableType State] [ProvableType Input]
    (origin : Name) (height : Nat) (source : InductiveTable F State Input) : Json × Json :=
  (table origin height [.everyRowExceptLast source.inductiveConstraint],
    stateBoundary ``InductiveTable.tableConstraints State)

/-- The supported meanings of a registered two-column lookup. Relating this
meaning to the source's arbitrary `Contains` predicate is an author obligation.
-/
inductive LookupInterpretation (F : Type) where
  | fixedIndexed (values : Array F)
  | witnessIndexed (height : Nat)

def registration (definition : Name) (name : String) (arity : Nat) : Json :=
  Json.mkObj [("definition", toJson definition.toString), ("name", toJson name),
    ("arity", toJson arity)]

def lookup (definition : Name) (source : RawTable F) (meaning : LookupInterpretation F) : Json :=
  let interpretation := match meaning with
    | .fixedIndexed values => Json.mkObj [("kind", "fixed-indexed"), ("values", toJson values)]
    | .witnessIndexed height => Json.mkObj [("kind", "witness-indexed"), ("height", toJson height)]
  Json.mkObj [("source", registration definition source.name source.arity),
    ("interpretation", interpretation)]

/-- Register algebraic balance explicitly; requirements and guarantees remain
Lean predicates and are not certified by the declaration name or the arity.
-/
def channel (definition : Name) (source : RawChannel F) : Json :=
  Json.mkObj [("source", registration definition source.name source.arity),
    ("interpretation", "field-balance")]

end ZkcClean.NativeExport
