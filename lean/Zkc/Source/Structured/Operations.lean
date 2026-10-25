module

public import Zkc.Source.Structured.Primitives
public import Zkc.Source.Structured.NaturalPowerOfTwo

@[expose] public section

namespace Zkc.Source.Structured

inductive HelperKind where
  | math | local
  deriving DecidableEq, Repr

/-- Resolved signature from the checked declaration table, never wire authority.
Protocol roots cannot be represented by this signature. -/
structure Helper where
  name : String
  kind : HelperKind
  inputs : List Ty
  outputs : List Ty
  deriving DecidableEq, Repr

/-- Scalar Math helper lifted over every rowwise operand in source order. -/
structure MapSpec where
  helperName : String
  field : String
  rowwise : List Bool
  deriving DecidableEq, Repr

def MapSpec.scalarInputs (spec : MapSpec) : List Ty :=
  spec.rowwise.map (fun _ => .field spec.field)
def MapSpec.arguments (spec : MapSpec) : List Ty :=
  spec.rowwise.map (fun row => if row then .vector spec.field else .field spec.field)
def MapSpec.helper (spec : MapSpec) : Helper :=
  ⟨spec.helperName, .math, spec.scalarInputs, [.field spec.field]⟩

structure DomainSpec where
  name : String
  inputs : List Ty
  field : String
  container : Var inputs (.vector field)
  indices : Bool

def DomainSpec.item (domain : DomainSpec) : Ty :=
  if domain.indices then .index else .field domain.field

structure FoldSpec where
  domain : DomainSpec
  state : List Ty
  captures : List Ty
  step : String
  predicate : String
  kind : HelperKind

def FoldSpec.arguments (fold : FoldSpec) : List Ty :=
  fold.domain.inputs ++ (fold.state ++ fold.captures)
def FoldSpec.stepHelper (fold : FoldSpec) : Helper :=
  ⟨fold.step, fold.kind, fold.state ++ (fold.domain.item :: (fold.domain.inputs ++ fold.captures)), fold.state⟩
def FoldSpec.predicateHelper (fold : FoldSpec) : Helper :=
  ⟨fold.predicate, fold.kind, fold.domain.item :: (fold.domain.inputs ++ fold.captures), [.boolean]⟩

inductive Op where
  | exec (primitive : Primitive)
  | indexConstant (value : Nat)
  | indexEqual
  | indexLess
  | indexPowerOfTwo
  | vectorLength (domain : String)
  | fieldConstant (domain : String) (value : Nat)
  | fieldAdd (domain : String) | fieldSubtract (domain : String)
  | fieldMultiply (domain : String) | fieldEqual (domain : String)
  | fieldEmbed (extension base : String)
  | groupIdentity (domain : String)
  | groupAdd (domain : String)
  | groupScale (group field : String)
  | groupEqual (domain : String)
  | booleanConstant (value : Bool)
  | booleanAnd | booleanOr | booleanXor | booleanEqual | booleanNotEqual
  | select (type : Ty)
  | boundedAt (domain : String)
  | invoke (helper : Helper)
  | fold (spec : FoldSpec)
  | map (spec : MapSpec)
  | branch (captures outputs : List Ty)
  | loop (state captures : List Ty)
  | loopCondition (state captures : List Ty)
  | guard
  /-- Internal observation only; erased by the ordinary closed interpretation. -/
  | mark (site : String)

def Op.arguments : Op → List Ty
  | .exec primitive => primitive.arguments
  | .indexConstant _ => []
  | .indexEqual | .indexLess | .indexPowerOfTwo => [.index, .index]
  | .vectorLength d => [.vector d]
  | .fieldConstant .. | .booleanConstant .. | .groupIdentity .. | .mark .. => []
  | .fieldAdd d | .fieldSubtract d | .fieldMultiply d | .fieldEqual d => [.field d, .field d]
  | .fieldEmbed _ base => [.field base]
  | .groupAdd d | .groupEqual d => [.group d, .group d]
  | .groupScale g f => [.group g, .field f]
  | .booleanAnd | .booleanOr | .booleanXor | .booleanEqual | .booleanNotEqual => [.boolean, .boolean]
  | .select ty => [.boolean, ty, ty]
  | .boundedAt d => [.vector d, .index]
  | .invoke helper => helper.inputs
  | .fold spec => spec.arguments
  | .map spec => spec.arguments
  | .branch captures _ => .boolean :: captures
  | .loop state captures | .loopCondition state captures => .index :: .index :: (state ++ captures)
  | .guard => [.boolean]

def Op.results : Op → List Ty
  | .exec primitive => primitive.results
  | .indexConstant _ => [.index]
  | .indexEqual | .indexLess | .indexPowerOfTwo => [.boolean]
  | .vectorLength _ => [.index]
  | .fieldConstant d _ | .fieldAdd d | .fieldSubtract d | .fieldMultiply d | .boundedAt d => [.field d]
  | .fieldEmbed extension _ => [.field extension]
  | .groupIdentity d | .groupAdd d | .groupScale d _ => [.group d]
  | .fieldEqual _ | .booleanConstant _ | .booleanAnd | .booleanOr | .booleanXor |
    .booleanEqual | .booleanNotEqual | .groupEqual _ => [.boolean]
  | .select ty => [ty]
  | .invoke helper => helper.outputs
  | .fold spec => spec.state
  | .map spec => [.vector spec.field]
  | .branch _ outputs => outputs
  | .loop state _ | .loopCondition state _ => state
  | .guard | .mark _ => []

def Op.regions : Op → List (List Ty × List Ty)
  | .branch captures outputs => [(captures, outputs), (captures, outputs)]
  | .loop state captures => [(.index :: (state ++ captures), state ++ captures)]
  | .loopCondition state captures =>
      [(.index :: (state ++ captures), .boolean :: (state ++ captures))]
  | _ => []

/-- The exact helper interfaces used by an operation's meaning. Both fold
callbacks remain dependencies even when a domain is empty at runtime. -/
def Op.helpers : Op → List Helper
  | .invoke helper => [helper]
  | .map spec => [spec.helper]
  | .fold spec => spec.stepHelper ::
      (if spec.predicate.isEmpty then [] else [spec.predicateHelper])
  | .exec .. | .indexConstant .. | .indexEqual | .indexLess | .indexPowerOfTwo | .vectorLength .. |
    .fieldConstant .. | .fieldAdd .. | .fieldSubtract .. | .fieldMultiply .. |
    .fieldEmbed .. | .fieldEqual .. | .booleanConstant .. | .booleanAnd | .booleanOr | .booleanXor |
    .booleanEqual | .booleanNotEqual | .select .. | .boundedAt .. |
    .branch .. | .loop .. | .loopCondition .. | .guard | .mark .. |
    .groupIdentity .. | .groupAdd .. | .groupScale .. | .groupEqual .. => []

abbrev dialect : Dialect := ⟨Ty, Op, Op.arguments, Op.results, Op.regions⟩

end Zkc.Source.Structured
