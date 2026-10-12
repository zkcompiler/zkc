import Clean.Table.Json
import Clean.Table.Inductive
import Clean.Air.FlatComponent

/-! Source extraction for the optional native Bundle adapter.

The payload retains Clean expressions and cell assignments. Lookup interpretations
and public bindings are explicit adapter inputs; arbitrary Lean propositions are
not serialized. This module does not extend the channel-free correspondence theorem
in `ZkcClean.Export` to native Bundles.
-/

namespace ZkcClean.NativeExport
open Lean

variable {F : Type} [FiniteField F] [ToJson F]

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
    | .aux _ => Json.mkObj [("row", toJson (W.val - 1)),
        ("column", toJson (auxiliary[index]! + auxiliaryOffset))]
  Json.mkObj [("window", toJson W.val), ("vars", toJson cells.toArray),
    ("circuit", toJson (ctx.circuit.toFlat.map flatOperation))]

def operation {S : Type → Type} [ProvableType S]
    (auxiliaryOffset : Nat) : TableOperation S F → Json
  | .boundary row c => Json.mkObj [("type", "Boundary"),
      ("row", toJson row), ("context", context auxiliaryOffset c)]
  | .everyRow c => Json.mkObj [("type", "EveryRow"), ("context", context auxiliaryOffset c)]
  | .everyRowExceptLast c => Json.mkObj [("type", "EveryRowExceptLast"),
      ("context", context auxiliaryOffset c)]

def table {S : Type → Type} [ProvableType S]
    (height : Nat) (operations : List (TableOperation S F)) : Json :=
  let (encoded, auxiliary) := operations.foldl (fun (encoded, offset) op =>
    let width := match op with
      | .boundary _ c => c.finalAssignment.numAux
      | .everyRow c => c.finalAssignment.numAux
      | .everyRowExceptLast c => c.finalAssignment.numAux
    (encoded.push (operation offset op), offset + width)) (#[], 0)
  Json.mkObj [
    ("model", "table"), ("height", toJson height),
    ("width", toJson (size S + auxiliary)),
    ("operations", toJson encoded)]

def component (height : Nat) (source : Air.Flat.Component F) : Json :=
  Json.mkObj [
    ("model", "component"), ("height", toJson height),
    ("width", toJson source.width),
    ("operations", toJson (source.operations.toFlat.map flatOperation))]

/-- State boundaries of an inductive table, bound to public slots in column order.
The first state occupies slots `[0, size State)`, the final state the next block.
These are the explicit parameterized equalities of `InductiveTable.tableConstraints`.
-/
def stateBindings (width : Nat) : Json :=
  toJson <| ((List.range width).map fun column =>
    Json.mkObj [("row", "first"), ("column", toJson column),
      ("slot", toJson column)]) ++
    ((List.range width).map fun column =>
    Json.mkObj [("row", "last"), ("column", toJson column),
      ("slot", toJson (width + column))])

end ZkcClean.NativeExport
