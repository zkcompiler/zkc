module

public import Zkc.Source.Structured.Vocabulary

@[expose] public section

namespace Zkc.Source.Structured

/-- Resolved signature from the checked declaration table, never wire authority. -/
structure Helper where
  name : String
  inputs : List Ty
  outputs : List Ty
  deriving DecidableEq, Repr

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

def FoldSpec.arguments (fold : FoldSpec) : List Ty :=
  fold.domain.inputs ++ (fold.state ++ fold.captures)
def FoldSpec.stepHelper (fold : FoldSpec) : Helper :=
  ⟨fold.step, fold.state ++ (fold.domain.item :: (fold.domain.inputs ++ fold.captures)), fold.state⟩
def FoldSpec.predicateHelper (fold : FoldSpec) : Helper :=
  ⟨fold.predicate, fold.domain.item :: (fold.domain.inputs ++ fold.captures), [.boolean]⟩

inductive Op where
  | fieldConstant (domain : String) (value : Nat)
  | fieldAdd (domain : String) | fieldSubtract (domain : String)
  | fieldMultiply (domain : String) | fieldEqual (domain : String)
  | booleanConstant (value : Bool)
  | booleanAnd | booleanOr | booleanXor | booleanEqual | booleanNotEqual
  | select (type : Ty)
  | boundedAt (domain : String)
  | invoke (helper : Helper)
  | fold (spec : FoldSpec)
  | branch (captures outputs : List Ty)
  | loop (state captures : List Ty)
  | loopCondition (state captures : List Ty)
  | guard

def Op.arguments : Op → List Ty
  | .fieldConstant .. | .booleanConstant .. => []
  | .fieldAdd d | .fieldSubtract d | .fieldMultiply d | .fieldEqual d => [.field d, .field d]
  | .booleanAnd | .booleanOr | .booleanXor | .booleanEqual | .booleanNotEqual => [.boolean, .boolean]
  | .select ty => [.boolean, ty, ty]
  | .boundedAt d => [.vector d, .index]
  | .invoke helper => helper.inputs
  | .fold spec => spec.arguments
  | .branch captures _ => .boolean :: captures
  | .loop state captures | .loopCondition state captures => .index :: .index :: (state ++ captures)
  | .guard => [.boolean]

def Op.results : Op → List Ty
  | .fieldConstant d _ | .fieldAdd d | .fieldSubtract d | .fieldMultiply d | .boundedAt d => [.field d]
  | .fieldEqual _ | .booleanConstant _ | .booleanAnd | .booleanOr | .booleanXor |
    .booleanEqual | .booleanNotEqual => [.boolean]
  | .select ty => [ty]
  | .invoke helper => helper.outputs
  | .fold spec => spec.state
  | .branch _ outputs => outputs
  | .loop state _ | .loopCondition state _ => state
  | .guard => []

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
  | .fold spec => spec.stepHelper ::
      (if spec.predicate.isEmpty then [] else [spec.predicateHelper])
  | .fieldConstant .. | .fieldAdd .. | .fieldSubtract .. | .fieldMultiply .. |
    .fieldEqual .. | .booleanConstant .. | .booleanAnd | .booleanOr | .booleanXor |
    .booleanEqual | .booleanNotEqual | .select .. | .boundedAt .. |
    .branch .. | .loop .. | .loopCondition .. | .guard => []

abbrev dialect : Dialect := ⟨Ty, Op, Op.arguments, Op.results, Op.regions⟩

end Zkc.Source.Structured
