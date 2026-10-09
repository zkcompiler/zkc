import ZkcClean.Native

/-! Construction of the native comparison control (`zkc.clean-air-control/0`).

Each component is exported with `exportComponent` and emitted with
`emitRelation` and `emitArena`. Rows are either produced by Clean's own witness
generator from input values, or supplied directly. Source residuals evaluate
every upstream `Operations.constraints` expression with `Expression.eval` on
`Environment.fromArray`; a row holds when all of them vanish, which is
`Operations.ConstraintsHold` in the admitted fragment (`constraintsHold_iff`).
Construction fails unless the zkc AIR model of the decoded export gives the
same residuals on every row.

Mutations are functions on the actual export. A mutant is emitted with its own
relation and arena, and its residuals come from the zkc AIR model of the
decoded mutant: Clean has no source for a mutant. A mutation that does not
apply, or yields the export itself, is refused.

This code runs in Lean's interpreter. It evaluates upstream definitions on
concrete rows; kernel-checked statements about the same subjects live in the
tests and in the theorems of `ZkcClean.Native`.
-/

set_option autoImplicit false

namespace ZkcClean

open Zkc.Relation Lean

variable {F : Type} [FiniteField F]

/-- Prover data without entries. Admitted constraints do not read it
(`constraintsHold_data`). -/
def emptyData : ProverData F := fun _ _ => #[]

/-- A row from Clean's witness generator for the component's input values. -/
def generatedRow (component : Air.Flat.Component F) (input : List F) : List F :=
  FlatOperation.dynamicWitnesses component.rowOperations.toFlat default input

/-- Upstream residual of every constraint on one row, in export order. -/
def cleanResiduals (component : Air.Flat.Component F) (row : List F) : List F :=
  component.operations.constraints.map fun e =>
    Expression.eval (Environment.fromArray row.toArray emptyData) e

/-- Residuals of the decoded artifact in the zkc AIR model, on a one-row trace. -/
def modelResiduals (artifact : Artifact) (row : List F) : Option (List F) := do
  let constraints ← artifact.decode F
  if h : row.length = artifact.width then
    let trace : Fin 1 → Fin artifact.width → F :=
      fun _ column => row[column.val]'(by rw [h]; exact column.2)
    constraints.mapM fun constraint => constraint.expression.evaluateAt Fin.elim0 trace 0
  else none

/-! ## Mutations of an exported artifact -/

inductive Mutation where
  /-- Replace the first constant `old` (left to right) in an assertion. -/
  | constant (assertion old new : Nat)
  /-- Replace the first read of column `old` in an assertion. -/
  | column (assertion old new : Nat)
  /-- Delete an assertion. -/
  | delete (assertion : Nat)
  deriving DecidableEq, Repr

/-- Rewrite the first leaf, left to right, accepted by `leaf`. -/
def Term.replaceFirst (leaf : Term → Option Term) : Term → Option Term
  | .add left right =>
      match left.replaceFirst leaf with
      | some left => some (.add left right)
      | none => (right.replaceFirst leaf).map (Term.add left)
  | .mul left right =>
      match left.replaceFirst leaf with
      | some left => some (.mul left right)
      | none => (right.replaceFirst leaf).map (Term.mul left)
  | t => leaf t

def Mutation.leaf : Mutation → Term → Option Term
  | .constant _ old new, .constant value => if value = old then some (.constant new) else none
  | .column _ old new, .column index => if index = old then some (.column new) else none
  | _, _ => none

def Mutation.apply (mutation : Mutation) (artifact : Artifact) : Option Artifact :=
  match mutation with
  | .delete assertion =>
      if assertion < artifact.assertions.length then
        some { artifact with assertions := artifact.assertions.eraseIdx assertion }
      else none
  | .constant assertion _ _ | .column assertion _ _ => do
      let term ← artifact.assertions[assertion]?
      let changed ← term.replaceFirst mutation.leaf
      some { artifact with assertions := artifact.assertions.set assertion changed }

/-! ## Control document -/

structure ComponentControl (F : Type) [FiniteField F] where
  name : String
  /-- The upstream declaration that defines the component. -/
  declaration : String
  component : Air.Flat.Component F
  rows : List (String × List F)
  mutations : List (String × Mutation)

def canonical (value : F) : Json := toString (FiniteField.val value)

def rowResult (residuals : List F) : Json :=
  Json.mkObj [("residuals", Json.arr (residuals.toArray.map canonical)),
    ("holds", toJson (residuals.all (· = 0)))]

def subject (presentation : PrimePresentation F) (name reference : String)
    (artifact : Artifact) (rows : List Json) : Except String Json := do
  let relation ← (emitRelation presentation artifact).mapError (s!"{name}: {repr ·}")
  let arena ← (emitArena presentation artifact).mapError (s!"{name}: {repr ·}")
  return Json.mkObj [("name", name), ("reference", reference), ("relation", relation),
    ("arena", arena), ("rows", Json.arr rows.toArray)]

def ComponentControl.document (presentation : PrimePresentation F)
    (control : ComponentControl F) : Except String Json := do
  let artifact ← match exportComponent control.component with
    | .ok artifact => pure artifact
    | .error refusal => throw s!"{control.name}: export refused: {repr refusal}"
  let source ← control.rows.mapM fun (name, row) => do
    unless row.length = artifact.width do
      throw s!"{control.name}/{name}: row width {row.length}, export width {artifact.width}"
    let clean := cleanResiduals control.component row
    unless modelResiduals artifact row = some clean do
      throw s!"{control.name}/{name}: Clean and the zkc AIR model disagree"
    pure (rowResult clean)
  let exported ← subject presentation "export" "clean" artifact source
  let mutants ← control.mutations.mapM fun (name, mutation) => do
    let some mutant := mutation.apply artifact
      | throw s!"{control.name}/{name}: the mutation does not apply"
    if mutant = artifact then throw s!"{control.name}/{name}: the mutation changes nothing"
    let rows ← control.rows.mapM fun (rowName, row) => do
      let some residuals := modelResiduals mutant row
        | throw s!"{control.name}/{name}/{rowName}: the mutant is not admitted"
      pure (rowResult residuals)
    subject presentation name "model" mutant rows
  let rows := control.rows.toArray.map fun (name, row) =>
    Json.mkObj [("name", name), ("cells", Json.arr (row.toArray.map canonical))]
  return Json.mkObj [("name", control.name), ("declaration", control.declaration),
    ("rows", Json.arr rows), ("subjects", Json.arr (#[exported] ++ mutants.toArray))]

/-- The complete control: source pin, presentation and components. -/
def controlDocument (presentation : PrimePresentation F) (repository revision : String)
    (controls : List (ComponentControl F)) : Except String Json := do
  let components ← controls.mapM (·.document presentation)
  return Json.mkObj [("format", "zkc.clean-air-control/0"),
    ("source", Json.mkObj [("repository", repository), ("revision", revision)]),
    ("presentation", Json.mkObj [("field", presentation.identity),
      ("modulus", toString presentation.modulus)]),
    ("components", Json.arr components.toArray)]

end ZkcClean
