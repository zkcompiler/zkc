module

public import Zkc.Source.Structured.Addresses
public import Zkc.Source.Structured.Catalogue
public import Zkc.Source.Structured.Origin

@[expose] public section

/-! Original-stage wire vocabulary. Blocks are serialization records only;
execution and structural formation use the shared `RawRegion` and `Region`. -/

namespace Zkc.Source.Structured

/-! The BLS12-381 identities and modulus of the admitted catalogue
(`blsCatalogue`), retained as names for clients and tools. Admission resolves
identities against catalogue rows, not against these names. -/

def scalarDomain : String := "bls12-381.fr"
def groupDomain : String := "bls12-381.g1"
def scalarServiceContract : String := "random.bls12-381.fr/0"
def scalarModulus : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513
def indexLimit : Nat := 2 ^ 64

/- The identity of a represented product is its complete nominal encoding,
not a digest. Its constructor and flattened component order remain explicit. -/
mutual
  inductive Ty where
    | boolean | index | field (domain : String) | vector (domain : String)
    | group (domain : String) | groups (domain : String) | indices
    | service (contract : String)
    | oracle (kind : OracleKind)
    | oracleSequence (kind : OracleKind) (maximum : Nat)
    | sequence (element : Ty)
    | product (identity constructor : String) (fields : ProductFields)
    deriving DecidableEq, Repr, Inhabited
  inductive OracleKind where
    | table (row : Ty) (rows : Option Nat)
    deriving DecidableEq, Repr, Inhabited
  inductive ProductFields where
    | nil | cons (type : Ty) (rest : ProductFields)
    deriving DecidableEq, Repr, Inhabited
end

/-- Associated types are determined by the admitted library kind, never by a
redundant producer-provided signature. Row and shape admission are separate. -/
def OracleKind.data : OracleKind → Ty
  | .table (.field domain) _ => .vector domain
  | .table (.group domain) _ => .groups domain
  | .table .index _ => .indices
  | .table row _ => .sequence row

/-- Named immutable dimensions. Bounds for dynamic dimensions belong to an
occurrence, not to its static kind or an extra authored interface component. -/
def OracleKind.shape : OracleKind → List (String × Option Nat)
  | .table _ rows => [("rows", rows)]

def OracleKind.query (_ : OracleKind) : Ty := .index

def OracleKind.answer : OracleKind → Ty
  | .table row _ => row

def ProductFields.toList : ProductFields → List Ty
  | .nil => []
  | .cons type rest => type :: rest.toList

def ProductFields.ofList : List Ty → ProductFields
  | [] => .nil
  | type :: rest => .cons type (ofList rest)

@[simp] theorem ProductFields.toList_ofList (types : List Ty) :
    (ProductFields.ofList types).toList = types := by
  induction types with
  | nil => rfl
  | cons type rest ih => simp [ofList, toList, ih]

inductive Kind where
  | protocol | math | local | oracle
  deriving DecidableEq, Repr

inductive Visibility where
  | publicDef | privateDef
  deriving DecidableEq, Repr

structure Bound where
  index : Nat
  container : Nat
  axis : Nat
  deriving DecidableEq, Repr

inductive DomainConstructor where
  | elements (container : Nat)
  | indices (container axis : Nat)
  | range (lower upper : Nat)
  | zip (operands : List Nat)
  | product (operands : List Nat)
  deriving DecidableEq, Repr

structure Domain where
  name : String
  inputs : List Ty
  constructors : List DomainConstructor
  result : Nat
  deriving DecidableEq, Repr

/-- Kinded static values, distinct from the roots used by the existing
primitive interpreter. A wire reader must check both representations agree. -/
inductive BindingArgument where
  | domain (sort identity : String)
  | type (value : Ty)
  | natural (value : Nat)
  | mask (values : List Bool)
  deriving DecidableEq, Repr

/-- Complete logical declaration data retained by the current wire reader.
It is checked independently against the selected primitive contract. -/
structure BindingSchema where
  arguments : List BindingArgument
  inputs : List Ty
  outputs : List Ty
  deriving DecidableEq, Repr

/-- Typed callable primitive declaration. It installs no source body or
inlining permission. Internal primitive roots retain their existing meanings. -/
structure Binding where
  name : String
  contract : String
  arguments : List String
  implementation : String
  schema : Option BindingSchema := none
  deriving DecidableEq, Repr

/-- Logical operations preserve anchors and query occurrences. This wire
vocabulary does not grant ordinary Math, message or executable-codec admission. -/
inductive OracleDescriptor where
  | input (holder : String) (receivers : List String) (logicalSort : Ty) (bounds : List (String × Nat))
  | send (holder : String) (receivers : List String) (kind : OracleKind)
      (dimensions : List String) (bounds : List (String × Nat))
  | query (owner : Option String) (kind : OracleKind)
  | contents (owner : String) (kind : OracleKind)
  | components (holder : String) (receivers : List String) (logicalSort : Ty)
  | shape (kind : OracleKind) (dimension : String)
  | forgetShape (source target : OracleKind)
  | virtual (declaration holder : String) (receivers : List String) (kind : OracleKind)
  | sequenceEmpty (kind : OracleKind) (maximum : Nat)
  | sequenceAppend (kind : OracleKind) (maximum : Nat) (roles : List String)
  | sequenceAt (kind : OracleKind) (maximum : Nat) (roles : List String)
  | sequenceLength (kind : OracleKind) (maximum : Nat)
  deriving DecidableEq, Repr

inductive Descriptor where
  | oracle (value : OracleDescriptor)
  | exec (operation binding : String) (parameters : List String)
  | indexConstant (decimal : String)
  | indexEqual
  | indexLess
  | indexPowerOfTwo
  | multilinearRestrictPrefix (domain : String)
  | vectorLength (domain : String)
  | fieldConstant (domain decimal : String)
  | fieldAdd (domain : String)
  | fieldSubtract (domain : String)
  | fieldMultiply (domain : String)
  | fieldEmbed (extension base : String)
  | fieldEqual (domain : String)
  | groupIdentity (group : String)
  | groupAdd (group : String)
  | groupScale (group field : String)
  | groupEqual (group : String)
  | booleanConstant (value : Bool)
  | booleanAnd | booleanOr | booleanXor | booleanEqual | booleanNotEqual
  | select (type : Ty)
  | boundedAt (domain : String)
  | makeProduct (constructor : String)
  | getProduct (index : Nat)
  | call (name : String)
  | apply (name : String)
  | protocolApply (name : String) (roles : List String)
  | protocolRepeat (carried maximum : Nat) (roles : List String)
      (scopes : List (List String))
  | localCall (name owner : String)
  | fold (domain step predicate : String)
  | branch | loop | loopCondition
  | guard (owner : String)
  | restrict (roles : List String)
  | assemble (roles : List String)
  | exchange (sender receiver : String)
  | draw (owner field : String)
  | statement (relation : String) (selectors : List String) (acceptance : Nat) (target : Option String)
  deriving DecidableEq, Repr

inductive Terminator where
  | ret (indices : List Nat)
  | yield (indices : List Nat)
  | condition (indices : List Nat)
  | stop (reason : PIR.Stop) (site : String)
  deriving DecidableEq, Repr

mutual
  inductive Block where
    | block (instructions : List Instruction) (terminator : Terminator)
    deriving Repr
  inductive Instruction where
    | instruction (descriptor : Descriptor) (operands : List Nat)
        (results : List Ty) (regions : List WireRegion) (site : String)
    deriving Repr
  inductive WireRegion where
    | region (inputs outputs : List Ty) (body : Block)
    deriving Repr
end

mutual
  /-- Original instructions in stored preorder, including every callback. This
  projection records source syntax only; dependency authority remains the formed
  tree's existing recursive operation inventory. -/
  def Block.storedInstructions : Block → List Instruction
    | .block instructions _ => instructions.flatMap Instruction.storedInstructions

  def Instruction.storedInstructions : Instruction → List Instruction
    | instruction@(.instruction _ _ _ regions _) =>
      instruction :: regions.flatMap WireRegion.storedInstructions

  def WireRegion.storedInstructions : WireRegion → List Instruction
    | .region _ _ body => body.storedInstructions
end

def Block.topLevelInstructions : Block → List Instruction
  | .block instructions _ => instructions

def Instruction.isStatement : Instruction → Bool
  | .instruction (.statement ..) _ _ _ _ => true
  | _ => false

/-- Native participant names and ordered port scopes belong to each protocol.
The decoder retains them verbatim; admission resolves names against this roster. -/
structure ProtocolInterface where
  roles : List String
  inputScopes : List (List String)
  outputScopes : List (List String)
  deriving DecidableEq, Repr

structure Function where
  name : String
  kind : Kind
  visibility : Visibility
  inputs : List Ty
  outputs : List Ty
  interface : Option ProtocolInterface
  preconditions : List Bound
  origin : Option FunctionOrigin
  body : Block
  deriving Repr

structure FiniteDeclaration where
  name : String
  visibility : Visibility
  inputs : List Ty
  outputs : List Ty
  domain : String
  step : String
  predicate : String
  deriving Repr

structure CollectDeclaration where
  name : String
  visibility : Visibility
  inputs : List Ty
  outputs : List Ty
  domain : String
  body : String
  predicate : String
  deriving Repr

/-- Retained preparation metadata; the shared SSA body is derived at admission. -/
structure RealizationDeclaration where
  name : String
  inputs : List Ty
  outputs : List Ty
  helper : String
  deriving Repr

structure MapDeclaration where
  name : String
  inputs : List Ty
  outputs : List Ty
  helper : String
  rowwise : List Bool
  deriving Repr

/-- Sources precede ordinary parameters; the queried position is last. The
actual query body determines the footprint, including repeated unused queries. -/
structure OracleDeclaration where
  name : String
  inputs : List Ty
  kind : OracleKind
  admissibility : String
  shapeArguments : List (String × Nat)
  shapeBounds : List (String × Nat)
  body : Block
  deriving Repr

inductive Definition where
  | oracle (value : OracleDeclaration)
  | function (value : Function)
  | finite (value : FiniteDeclaration)
  | collect (value : CollectDeclaration)
  | realization (value : RealizationDeclaration)
  | map (value : MapDeclaration)
  deriving Repr

/-- Retained relation metadata. A formula link identifies source, not totality
or a proof that a protocol satisfies the relation. -/
structure Relation where
  name : String
  visibility : Visibility
  kind : String
  key : String
  revision : String
  inputs : List Ty
  outputs : List Ty
  purposes : List String
  formula : Option String := none
  staticArguments : List OriginTerm := []
  deriving DecidableEq, Repr

inductive ContractDirection where
  | input | output
  deriving DecidableEq, Repr

structure ContractSelector where
  direction : ContractDirection
  port : Nat
  role : String
  /-- Raw wire distinction. Anchor selectors have no participant copy; their
  role field is empty. Semantic admission currently refuses this profile. -/
  anchor : Bool := false
  deriving DecidableEq, Repr

structure RelationApplication where
  relation : String
  selectors : List ContractSelector
  deriving DecidableEq, Repr

inductive ContractKind where
  | target | input | output | continuation
  deriving DecidableEq, Repr

structure ContractClause where
  kind : ContractKind
  name : String
  subject : RelationApplication
  residual : Option RelationApplication
  decision : Option ContractSelector
  deriving DecidableEq, Repr

structure ProtocolContract where
  owner : String
  clauses : List ContractClause
  deriving DecidableEq, Repr

/-- Source records retain their declared usage attribute and closed field types.
No resource property is inferred from a flattened native carrier. -/
structure SourceRecord where
  type : OriginTerm
  resource : String
  sealed : Bool
  fields : List (String × OriginTerm)
  deriving BEq, Repr

structure SourcePort where
  name : String
  type : OriginTerm
  roles : List String
  offset : Nat
  count : Nat
  deriving BEq, Repr

structure SourceProtocol where
  name : String
  inputs : List SourcePort
  outputs : List SourcePort
  deriving BEq, Repr

structure SourceDeclarations where
  records : List SourceRecord := []
  protocols : List SourceProtocol := []
  deriving BEq, Repr

structure Snapshot where
  source : String
  entry : String
  domains : List Domain
  relations : List Relation
  bindings : List Binding
  definitions : List Definition
  contracts : List ProtocolContract := []
  /-- The catalogue rows of the identities the unit uses. -/
  catalogue : Catalogue
  sourceDeclarations : SourceDeclarations := {}
  deriving Repr

def Definition.name : Definition → String
  | .oracle f => f.name
  | .function f => f.name
  | .finite f => f.name
  | .collect f => f.name
  | .realization f => f.name
  | .map f => f.name
def Definition.inputs : Definition → List Ty
  | .oracle f => f.inputs
  | .function f => f.inputs
  | .finite f => f.inputs
  | .collect f => f.inputs
  | .realization f => f.inputs
  | .map f => f.inputs
def Definition.outputs : Definition → List Ty
  | .oracle f => [f.kind.answer]
  | .function f => f.outputs
  | .finite f => f.outputs
  | .collect f => f.outputs
  | .realization f => f.outputs
  | .map f => f.outputs
def Definition.kind : Definition → Kind
  | .oracle _ => .oracle
  | .function f => f.kind
  | .finite _ | .collect _ | .realization _ | .map _ => .local
def Definition.visibility : Definition → Visibility
  | .oracle _ => .publicDef
  | .function f => f.visibility
  | .finite f => f.visibility
  | .collect f => f.visibility
  | .realization _ | .map _ => .publicDef
def Definition.preconditions : Definition → List Bound
  | .oracle _ => []
  | .function f => f.preconditions
  | .finite _ | .collect _ | .realization _ | .map _ => []

end Zkc.Source.Structured
