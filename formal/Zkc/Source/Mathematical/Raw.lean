import Zkc.Source.Mathematical.Static
import Zkc.Semantics.Execution

/-! Finite mathematical source data before registry, scope and type admission.

Reference kinds remain distinct even before their bounds are known. Attributes
are opaque finite data; they confer no operation or interpretation authority.
JSON and byte transport are owned by the independent consumer layer.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.Raw

inductive ReferenceKind where
  | type | domain | operationIdentity | wireIdentity | service | law
  | operation | wire | capabilityType | capabilityPort | root
  | definition | relation | value | region | role
  deriving DecidableEq, Repr

structure Reference (_kind : ReferenceKind) where
  index : Nat
  deriving DecidableEq, Repr

inductive Attribute where
  | boolean (value : Bool)
  | natural (value : Nat)
  | string (value : String)
  | array (values : List Attribute)
  | object (fields : List (String × Attribute))
  deriving Repr

mutual
  private def attributeDecEq (a b : Attribute) : Decidable (a = b) :=
    match a, b with
    | .boolean a, .boolean b => decidable_of_iff (a = b) (by simp)
    | .natural a, .natural b => decidable_of_iff (a = b) (by simp)
    | .string a, .string b => decidable_of_iff (a = b) (by simp)
    | .array a, .array b =>
        haveI := attributesDecEq a b
        decidable_of_iff (a = b) (by simp)
    | .object a, .object b =>
        haveI := attributeFieldsDecEq a b
        decidable_of_iff (a = b) (by simp)
    | .boolean _, .natural _ | .boolean _, .string _ | .boolean _, .array _ | .boolean _, .object _ |
      .natural _, .boolean _ | .natural _, .string _ | .natural _, .array _ | .natural _, .object _ |
      .string _, .boolean _ | .string _, .natural _ | .string _, .array _ | .string _, .object _ |
      .array _, .boolean _ | .array _, .natural _ | .array _, .string _ | .array _, .object _ |
      .object _, .boolean _ | .object _, .natural _ | .object _, .string _ | .object _, .array _ =>
        isFalse (by intro h; cases h)
  private def attributesDecEq (a b : List Attribute) : Decidable (a = b) :=
    match a, b with
    | [], [] => isTrue rfl
    | x :: xs, y :: ys =>
        haveI := attributeDecEq x y
        haveI := attributesDecEq xs ys
        decidable_of_iff (x = y ∧ xs = ys) (by simp)
    | [], _ :: _ | _ :: _, [] => isFalse (by intro h; cases h)
  private def attributeFieldsDecEq (a b : List (String × Attribute)) : Decidable (a = b) :=
    match a, b with
    | [], [] => isTrue rfl
    | (kx, x) :: xs, (ky, y) :: ys =>
        haveI := attributeDecEq x y
        haveI := attributeFieldsDecEq xs ys
        decidable_of_iff (kx = ky ∧ x = y ∧ xs = ys) (by simp [and_assoc])
    | [], _ :: _ | _ :: _, [] => isFalse (by intro h; cases h)
end

instance : DecidableEq Attribute := attributeDecEq

structure Identity where
  name : String
  version : String
  digest : String
  deriving DecidableEq, Repr

structure Manifest where
  domains : List Identity
  operations : List Identity
  wires : List Identity
  services : List Identity
  laws : List Identity
  deriving DecidableEq, Repr

structure TypeUse where
  type : Reference .type
  statics : List Static.Raw
  deriving DecidableEq, Repr

inductive Degree where
  | individual | total
  deriving DecidableEq, Repr

inductive TypeExpression where
  | nominal (domain : Reference .domain) (constructor : String) (arguments : List Static.Raw)
  | product (elements : List TypeUse)
  | fin (count : Static.Raw)
  | vector (element : TypeUse) (count : Static.Raw)
  | polynomial (domain : Reference .domain) (arity degree : Static.Raw) (convention : Degree)
  | residual (domain : Reference .domain) (arity degree : Static.Raw)
  deriving DecidableEq, Repr

structure TypeTemplate where
  statics : Nat
  body : TypeExpression
  deriving DecidableEq, Repr

structure CapabilityUse where
  type : Reference .capabilityType
  statics : List Static.Raw
  deriving DecidableEq, Repr

structure CapabilityType where
  identity : Reference .service
  statics : Nat
  arguments : List TypeUse
  result : TypeUse
  deriving DecidableEq, Repr

structure Permission where
  signature : CapabilityUse
  roles : List (Reference .role)
  deriving DecidableEq, Repr

inductive Purity where
  | total | ordered
  deriving DecidableEq, Repr

structure Operation where
  identity : Reference .operationIdentity
  statics : Nat
  capabilities : List CapabilityUse
  arguments : List TypeUse
  result : TypeUse
  purity : Purity
  distinct : List (Nat × Nat)
  deriving DecidableEq, Repr

structure Wire where
  identity : Reference .wireIdentity
  statics : Nat
  type : TypeUse
  deriving DecidableEq, Repr

structure Port where
  roles : List (Reference .role)
  type : TypeUse
  deriving DecidableEq, Repr

mutual
  inductive Node where
    | operation (operation : Reference .operation) (statics : List Static.Raw)
        (attributes : Attribute) (arguments : List (Reference .region))
    | tuple (elements : List (Reference .region))
    | project (value : Reference .region) (component : Nat)
    | map (count : Static.Raw) (body : Region)
    | fold (count : Static.Raw) (initial : List (Reference .region)) (body : Region)
    deriving Repr
  inductive Region where
    | mk (captures : List (Reference .value)) (nodes : List Node) (outputs : List (Reference .region))
    deriving Repr
end

structure Relation where
  statics : Nat
  publicInputs : List TypeUse
  witnessInputs : List TypeUse
  assumptions : List (Reference .law)
  body : Region
  deriving Repr

structure RelationBinding where
  relation : Reference .relation
  statics : List Static.Raw
  publicInputs : List (Reference .value)
  witnessInputs : List (Reference .value)
  deriving DecidableEq, Repr

inductive Terminal where
  | ret (values : List (Reference .value))
  | stop (site : Nat) (owner : Reference .role) (reason : PIR.Stop)
  deriving Repr

mutual
  inductive Step where
    | pure (region : Region)
    | local (site : Nat) (owner : Reference .role) (operation : Reference .operation)
        (statics : List Static.Raw) (attributes : Attribute)
        (capabilities : List (Reference .capabilityPort)) (arguments : List (Reference .value))
    | query (site : Nat) (owner : Reference .role) (capability : Reference .capabilityPort)
        (arguments : List (Reference .value))
    | guard (site : Nat) (owner : Reference .role) (condition : Reference .value)
    | message (site : Nat) (wire : Reference .wire) (statics : List Static.Raw)
        (sender receiver : Reference .role) (value : Reference .value)
    | invoke (site : Nat) (definition : Reference .definition) (statics : List Static.Raw)
        (roles : List (Reference .role)) (capabilities : List (Reference .capabilityPort))
        (arguments : List (Reference .value))
    | repeat (site : Nat) (count : Static.Raw) (carried : List Port)
        (initial captures : List (Reference .value)) (body : Body)
    deriving Repr
  inductive Body where
    | mk (steps : List Step) (terminal : Terminal)
    deriving Repr
end

structure Definition where
  statics : Nat
  roles : Nat
  capabilities : List Permission
  arguments : List Port
  results : List Port
  relations : List RelationBinding
  body : Body
  deriving Repr

structure Entry where
  definition : Reference .definition
  statics : List Nat
  roles : List (Reference .role)
  capabilities : List (Reference .root)
  deriving DecidableEq, Repr

structure Module where
  roles : List String
  types : List TypeTemplate
  operations : List Operation
  wires : List Wire
  capabilityTypes : List CapabilityType
  roots : List Permission
  relations : List Relation
  definitions : List Definition
  entry : Entry
  deriving Repr

structure Subject where
  manifest : Manifest
  module : Module
  deriving Repr

end Zkc.Source.Mathematical.Raw
