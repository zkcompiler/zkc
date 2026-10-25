module

public import Zkc.Source.RegionDecoding
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

inductive Ty where
  | boolean | index | field (domain : String) | vector (domain : String)
  | group (domain : String) | service (contract : String)
  deriving DecidableEq, Repr, Inhabited

inductive Kind where
  | protocol | math | local
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
  deriving DecidableEq, Repr

structure Domain where
  name : String
  inputs : List Ty
  constructor : DomainConstructor
  deriving DecidableEq, Repr

/-- Non-callable primitive declaration, retained even when unused. -/
structure Binding where
  name : String
  contract : String
  arguments : List String
  implementation : String
  deriving DecidableEq, Repr

inductive Descriptor where
  | exec (operation binding : String) (parameters : List String)
  | indexConstant (decimal : String)
  | indexEqual
  | indexLess
  | indexPowerOfTwo
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

inductive Definition where
  | function (value : Function)
  | finite (value : FiniteDeclaration)
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
  deriving DecidableEq, Repr

inductive ContractDirection where
  | input | output
  deriving DecidableEq, Repr

structure ContractSelector where
  direction : ContractDirection
  port : Nat
  role : String
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
  deriving Repr

def Definition.name : Definition → String
  | .function f => f.name
  | .finite f => f.name
  | .realization f => f.name
  | .map f => f.name
def Definition.inputs : Definition → List Ty
  | .function f => f.inputs
  | .finite f => f.inputs
  | .realization f => f.inputs
  | .map f => f.inputs
def Definition.outputs : Definition → List Ty
  | .function f => f.outputs
  | .finite f => f.outputs
  | .realization f => f.outputs
  | .map f => f.outputs
def Definition.kind : Definition → Kind
  | .function f => f.kind
  | .finite _ | .realization _ | .map _ => .local
def Definition.visibility : Definition → Visibility
  | .function f => f.visibility
  | .finite f => f.visibility
  | .realization _ | .map _ => .publicDef
def Definition.preconditions : Definition → List Bound
  | .function f => f.preconditions
  | .finite _ | .realization _ | .map _ => []

end Zkc.Source.Structured
