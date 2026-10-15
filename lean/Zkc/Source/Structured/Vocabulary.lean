module

public import Zkc.Source.RegionDecoding

@[expose] public section

/-! Original-stage wire vocabulary. Blocks are serialization records only;
execution and structural formation use the shared `RawRegion` and `Region`. -/

namespace Zkc.Source.Structured

def scalarDomain : String := "bls12-381.fr"
def scalarModulus : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513
def indexLimit : Nat := 2 ^ 64

inductive Ty where
  | boolean | index | field (domain : String) | vector (domain : String)
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

inductive Descriptor where
  | fieldConstant (domain decimal : String)
  | fieldAdd (domain : String)
  | fieldSubtract (domain : String)
  | fieldMultiply (domain : String)
  | fieldEqual (domain : String)
  | booleanConstant (value : Bool)
  | booleanAnd | booleanOr | booleanXor | booleanEqual | booleanNotEqual
  | select (type : Ty)
  | boundedAt (domain : String)
  | call (name : String)
  | apply (name : String)
  | localCall (name owner : String)
  | fold (domain step predicate : String)
  | branch | loop | loopCondition
  | guard (owner : String)
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

structure Function where
  name : String
  kind : Kind
  visibility : Visibility
  inputs : List Ty
  outputs : List Ty
  preconditions : List Bound
  origin : Option (String × List (String × String))
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

inductive Definition where
  | function (value : Function)
  | finite (value : FiniteDeclaration)
  deriving Repr

structure Snapshot where
  source : String
  entry : String
  role : String
  domains : List Domain
  definitions : List Definition
  deriving Repr

def Definition.name : Definition → String
  | .function f => f.name
  | .finite f => f.name
def Definition.inputs : Definition → List Ty
  | .function f => f.inputs
  | .finite f => f.inputs
def Definition.outputs : Definition → List Ty
  | .function f => f.outputs
  | .finite f => f.outputs
def Definition.kind : Definition → Kind
  | .function f => f.kind
  | .finite _ => .local
def Definition.visibility : Definition → Visibility
  | .function f => f.visibility
  | .finite f => f.visibility
def Definition.preconditions : Definition → List Bound
  | .function f => f.preconditions
  | .finite _ => []

end Zkc.Source.Structured
