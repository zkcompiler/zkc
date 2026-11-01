import ZkcSecurityExamples.Gkr.CanonicalPolicy
import ZkcTools.StructuredSource.NamedValues
import Zkc.Source.Structured.ProtocolSignature

/-! Complete named rows preserve missing inputs, nominal product carriers and
same-typed coordinate order. The actual GKR bridge is total on raw statements;
no shape or honest-input premise is available in these roundtrips. -/
set_option autoImplicit false
set_option maxRecDepth 50000
noncomputable section
namespace TestsSecurity.NamedSubjectABI
open Zkc.Source Zkc.Source.Structured
open ZkcSecurity.Realizations.Gkr

def signature : ProtocolSignature := {
  name := "mixed", roles := ["producer", "validator"]
  inputs := [.index, .index, .vector scalarDomain,
    .product "example.Pair" "mk" (.cons .index (.cons (.vector scalarDomain) .nil))]
  outputs := [.index, .index]
  inputScopes := [[0, 1], [0], [0, 1], [1]], outputScopes := [[0, 1], [0, 1]] }

named_values Mixed [right, left, vector, pair] := signature.inputs
named_values Reordered [left, right] := signature.outputs
named_values Empty [] := ([] : List Ty)
-- Ordinary labels remain available even when they resemble generator locals.
named_values LocalNames [view, record] := signature.outputs

/-- error: named_values requires distinct field labels -/
#guard_msgs in
named_values Duplicate [same, same] := signature.outputs

/-- error: named_values field labels must cover every retained coordinate in order -/
#guard_msgs in
named_values Incomplete [left] := signature.outputs

/-- error: named_values reserved or qualified field label: Value -/
#guard_msgs in
named_values Reserved [Value, right] := signature.outputs

def Collision.pack : Nat := 0

open Lean Elab Command in
run_cmd do
  let name := mkIdent `Collision
  let failed ← try
    ZkcTools.StructuredSource.NamedValues.elaborateNamedValuesAtomic
      (← `(command| named_values $name [left, right] := signature.outputs))
    pure false
  catch error =>
    if error.isRuntime || error.isInterrupt then throw error
    pure true
  unless failed do throwError "expected a named-view declaration collision"
  if (← getEnv).contains `TestsSecurity.NamedSubjectABI.Collision.types then
    throwError "failed named view left a partial declaration"

named_values Reversed [right, left] := signature.outputs
structure Coordinates (F : Type) where
  left : F
  right : F

named_values_bridge CoordinatesView (Value : Ty → Type) : Coordinates (Value .index) :=
  Reversed Value with [left, right]

example (Value : Ty → Type) (record : Coordinates (Value .index)) :
    Reversed.pack (CoordinatesView.toView Value record) =
      .cons record.right (.cons record.left .nil) := rfl

example (Value : Ty → Type) (record : Coordinates (Value .index)) :
    CoordinatesView.fromView Value (CoordinatesView.toView Value record) = record :=
  CoordinatesView.fromView_toView Value record

example (Value : Ty → Type) (row : Values (Component Value) signature.inputs) :
    Mixed.pack (Mixed.unpack row) = row := Mixed.pack_unpack row

example (Value : Ty → Type) (view : Mixed.View (Component Value)) :
    Mixed.unpack (Mixed.pack view) = view := Mixed.unpack_pack view

example (Value : Ty → Type) (vector : Value (.vector scalarDomain)) :
    (Mixed.unpack (Mixed.pack (Value := Component Value)
      { right := none, left := none, vector := some vector, pair := none })).pair = none := rfl

/-- Display labels do not silently permute two identically typed coordinates. -/
example : Mixed.pack (Value := fun _ => Nat)
    { left := 11, right := 22, vector := 33, pair := 44 } =
      .cons 22 (.cons 11 (.cons 33 (.cons 44 .nil))) := rfl

example : Reordered.pack (Value := fun _ => Nat) { left := 11, right := 22 } ≠
    .cons 22 (.cons 11 .nil) := by
  intro same
  exact (by decide : (11 : Nat) ≠ 22) (congrArg (fun row => row.get .here) same)

/-- A visibility projection can lose a private slot; an unconditional inverse
would be false. The generated preservation law takes an explicit fixed-point
proof instead. -/
def hideLeft (row : Values (Component (fun _ : Ty => Nat)) signature.outputs) :=
  Reordered.pack { left := none, right := (Reordered.unpack row).right }

example : Reordered.project hideLeft { left := some 11, right := some 22 } ≠
    { left := some 11, right := some 22 } := by
  intro same
  have impossible := congrArg Reordered.View.left same
  cases impossible

example (view : Reordered.View (Component (fun _ : Ty => Nat)))
    (visible : hideLeft (Reordered.pack view) = Reordered.pack view) :
    Reordered.project hideLeft view = view := Reordered.project_eq_self hideLeft view visible

example (Value : Ty → Type) (row : Values Value []) : Empty.pack (Empty.unpack row) = row :=
  Empty.pack_unpack row

example (model : DomainModel) (row : (Canonical.subject model).Inputs) :
    Canonical.InputView.pack (Canonical.InputView.unpack row) = row :=
  Canonical.InputView.pack_unpack row

example (model : DomainModel)
    (statement : (Canonical.subject model).validatorArtifacts.Statement model) (handle : Nat) :
    Canonical.statement model (Canonical.invocation model statement handle) = statement :=
  Canonical.statement_invocation model statement handle

example (model : DomainModel) (runtime : Source.Invocation (model.Field scalarDomain)) :
    Canonical.invocation model (Canonical.statement model runtime) runtime.handle = runtime :=
  Canonical.invocation_statement model runtime

example (model : DomainModel) (runtime : Source.Invocation (model.Field scalarDomain)) :
    (Canonical.subject model).Relation (Canonical.sourceInputs model runtime) ↔ runtime.Correct :=
  Canonical.relation_exact model runtime

example (model : DomainModel)
    (statement : (Canonical.subject model).validatorArtifacts.Statement model) (handle : Nat)
    (witness : (Canonical.validatorSubject model).Witness) :
    (Canonical.validatorSubject model).Holds statement witness ↔
      (Canonical.invocation model statement handle).Correct :=
  Canonical.holds_all model statement handle witness

#print axioms Canonical.InputView.pack_unpack
#print axioms Canonical.StatementInvocation.toView_fromView
#print axioms Canonical.holds_all
end TestsSecurity.NamedSubjectABI
