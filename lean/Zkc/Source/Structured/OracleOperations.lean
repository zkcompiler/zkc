module

public import Zkc.Source.Structured.OracleValues
public import Zkc.Source.Component

@[expose] public section

/-! Resolved logical operations. Signatures retain the declaration association; no request
contains a caller-selected implementation or an admissibility proof. -/

set_option autoImplicit false
namespace Zkc.Source.Structured

structure OracleSignature where
  name : String
  inputs : List Ty
  kind : OracleKind
  admissibility : String
  shapeArguments : List (String × Nat)
  shapeBounds : List (String × Nat)
  deriving DecidableEq, Repr

def OracleDeclaration.signature (declaration : OracleDeclaration) : OracleSignature :=
  ⟨declaration.name, declaration.inputs, declaration.kind, declaration.admissibility,
    declaration.shapeArguments, declaration.shapeBounds⟩

/-- `none` denotes inherited ownership, permitted only in checked oracle bodies. -/
inductive OracleOp where
  | input (sort : OracleLogicalSort) (holder : Nat) (receivers : List Nat)
      (bounds : List (String × Nat))
  | send (kind : OracleKind) (holder : Nat) (receivers : List Nat)
      (bounds : List (String × Nat))
  | query (kind : OracleKind) (owner : Option Nat)
  | contents (kind : OracleKind) (holder : Nat)
  | components (sort : OracleLogicalSort) (holder : Nat) (receivers : List Nat)
  | shape (kind : OracleKind) (dimension : String)
  | forgetShape (source target : OracleKind)
  | virtual (declaration : OracleSignature) (holder : Nat) (receivers : List Nat)
  | sequenceEmpty (kind : OracleKind) (maximum : Nat) (roles : List Nat)
  | sequenceAppend (kind : OracleKind) (maximum : Nat) (roles : List Nat)
  | sequenceAt (kind : OracleKind) (maximum : Nat) (roles : List Nat)
  | sequenceLength (kind : OracleKind) (maximum : Nat)
  deriving DecidableEq, Repr

def OracleOp.arguments : OracleOp → List Ty
  | .input sort .. => [sort.dataType, sort.type]
  | .send kind .. => kind.data :: kind.shape.map (fun _ ↦ Ty.index)
  | .query kind _ => [.oracle kind, kind.query]
  | .contents kind _ | .shape kind _ => [.oracle kind]
  | .components sort .. => [sort.type]
  | .forgetShape source _ => [.oracle source]
  | .virtual declaration .. => declaration.inputs.dropLast
  | .sequenceEmpty .. => []
  | .sequenceAppend kind maximum _ => [.oracleSequence kind maximum, .oracle kind]
  | .sequenceAt kind maximum _ => [.oracleSequence kind maximum, .index]
  | .sequenceLength kind maximum => [.oracleSequence kind maximum]

def OracleOp.results : OracleOp → List Ty
  | .input sort .. => [sort.type]
  | .send kind .. | .sequenceAt kind .. => [.oracle kind]
  | .query kind _ => [kind.answer]
  | .contents kind _ => [kind.data]
  | .components sort .. => [sort.dataType, sort.type]
  | .shape .. | .sequenceLength .. => [.index]
  | .forgetShape _ target => [.oracle target]
  | .virtual declaration .. => [.oracle declaration.kind]
  | .sequenceEmpty kind maximum _ | .sequenceAppend kind maximum _ =>
      [.oracleSequence kind maximum]

/-- Fully resolved coordinates are supplied by reached applications/iterations, never an
allocation counter or a rendered site label. The unchanged row is retained separately. -/
structure OracleLocation where
  invocation : InvocationCoordinate
  definition : Nat
  row : List Nat
  deriving DecidableEq, Repr

def OracleLocation.anchor (location : OracleLocation) : OracleAnchor :=
  ⟨location.invocation, .construction location.row⟩

structure OracleRequest (carriers : Carriers) where
  operation : OracleOp
  location : OracleLocation
  self : Nat
  roles : Nat → Nat
  arguments : Values (Component (ProtocolValue carriers)) operation.arguments

abbrev oracleInterface (carriers : Carriers) : PIR.Signature where
  Op := OracleRequest carriers
  Reply request := Values (Component (ProtocolValue carriers)) request.operation.results

end Zkc.Source.Structured
