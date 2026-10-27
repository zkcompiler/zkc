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

/-- Collection kinds retain distinct native identities while sharing ordered
finite traversal. A numerical field vector is not a generic source sequence. -/
inductive Collection where
  | vector (field : String)
  | sequence (element : Ty)
  deriving DecidableEq, Repr

def Collection.type : Collection → Ty
  | .vector field => .vector field
  | .sequence element => .sequence element

def Collection.element : Collection → Ty
  | .vector field => .field field
  | .sequence element => element

/-- A constructor refers to data arguments and already admitted domain values.
The latter are heterogeneous item tuples, not invented nominal products. -/
inductive DomainNode (inputs : List Ty) (context : List (List Ty)) : List Ty → Type where
  | elements (collection : Collection) (container : Var inputs collection.type) :
      DomainNode inputs context [collection.element]
  | indices (collection : Collection) (container : Var inputs collection.type) :
      DomainNode inputs context [.index]
  | range (lower upper : Var inputs .index) : DomainNode inputs context [.index]
  | zip (items : List (List Ty)) (operands : Operands context items) :
      DomainNode inputs context items.flatten
  | product (items : List (List Ty)) (operands : Operands context items) :
      DomainNode inputs context items.flatten

/-- Stored constructor order is semantic: an unused constructor can stop before
another constructor or before the first callback. References are typed SSA. -/
inductive DomainBody (inputs : List Ty) : List (List Ty) → List Ty → Type where
  | ret {context items} (value : Var context items) : DomainBody inputs context items
  | letNode {context itemTypes items} (node : DomainNode inputs context itemTypes)
      (next : DomainBody inputs (itemTypes :: context) items) : DomainBody inputs context items

structure DomainSpec where
  name : String
  inputs : List Ty
  items : List Ty
  body : DomainBody inputs [] items

/-- Single-collection definitions use the same constructor sequence as every
composite domain. This is a typed authoring convenience, not another reader. -/
def DomainSpec.elements (name : String) (inputs : List Ty) (collection : Collection)
    (container : Var inputs collection.type) : DomainSpec :=
  ⟨name, inputs, [collection.element], .letNode (.elements collection container) (.ret .here)⟩

def DomainSpec.indices (name : String) (inputs : List Ty) (collection : Collection)
    (container : Var inputs collection.type) : DomainSpec :=
  ⟨name, inputs, [.index], .letNode (.indices collection container) (.ret .here)⟩

/-- Derived item-to-container provenance; it is never supplied by the wire. -/
def domainOperandBounds {context : List (List Ty)}
    (environment : Values (fun _ => List (Nat × Nat)) context) :
    {items : List (List Ty)} → Operands context items → List (Nat × Nat)
  | [], .nil => []
  | types :: _, .cons operand rest =>
      environment.get operand ++
        (domainOperandBounds environment rest).map (fun (item, container) =>
          (types.length + item, container))

def DomainNode.bounds {inputs : List Ty} {context : List (List Ty)}
    (environment : Values (fun _ => List (Nat × Nat)) context) :
    {items : List Ty} → DomainNode inputs context items → List (Nat × Nat)
  | _, .indices _ container => [(0, container.index)]
  | _, .zip _ operands | _, .product _ operands => domainOperandBounds environment operands
  | _, .elements .. | _, .range .. => []

def DomainBody.bounds {inputs : List Ty} : {context : List (List Ty)} → {items : List Ty} →
    DomainBody inputs context items → Values (fun _ => List (Nat × Nat)) context → List (Nat × Nat)
  | _, _, .ret value, environment => environment.get value
  | _, _, .letNode node next, environment =>
      next.bounds (.cons (node.bounds environment) environment)

def DomainSpec.bounds (domain : DomainSpec) : List (Nat × Nat) := domain.body.bounds .nil

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
  ⟨fold.step, fold.kind, fold.state ++ (fold.domain.items ++ (fold.domain.inputs ++ fold.captures)), fold.state⟩
def FoldSpec.predicateHelper (fold : FoldSpec) : Helper :=
  ⟨fold.predicate, fold.kind, fold.domain.items ++ (fold.domain.inputs ++ fold.captures), [.boolean]⟩

structure CollectSpec where
  domain : DomainSpec
  collection : Collection
  captures : List Ty
  body : String
  predicate : String
  kind : HelperKind

def CollectSpec.arguments (spec : CollectSpec) : List Ty := spec.domain.inputs ++ spec.captures
def CollectSpec.bodyHelper (spec : CollectSpec) : Helper :=
  ⟨spec.body, spec.kind, spec.domain.items ++ (spec.domain.inputs ++ spec.captures),
    [spec.collection.element]⟩
def CollectSpec.predicateHelper (spec : CollectSpec) : Helper :=
  ⟨spec.predicate, spec.kind, spec.domain.items ++ (spec.domain.inputs ++ spec.captures), [.boolean]⟩

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
  | makeProduct (identity constructor : String) (fields : ProductFields)
  | getProduct (identity constructor : String) (fields : ProductFields)
      (type : Ty) (field : Var fields.toList type)
  | invoke (helper : Helper)
  | fold (spec : FoldSpec)
  | collect (spec : CollectSpec)
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
  | .makeProduct _ _ fields => fields.toList
  | .getProduct identity constructor fields _ _ => [.product identity constructor fields]
  | .invoke helper => helper.inputs
  | .fold spec => spec.arguments
  | .collect spec => spec.arguments
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
  | .makeProduct identity constructor fields => [.product identity constructor fields]
  | .getProduct _ _ _ type _ => [type]
  | .invoke helper => helper.outputs
  | .fold spec => spec.state
  | .collect spec => [spec.collection.type]
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
  | .collect spec => spec.bodyHelper ::
      (if spec.predicate.isEmpty then [] else [spec.predicateHelper])
  | .fold spec => spec.stepHelper ::
      (if spec.predicate.isEmpty then [] else [spec.predicateHelper])
  | .exec .. | .indexConstant .. | .indexEqual | .indexLess | .indexPowerOfTwo | .vectorLength .. |
    .fieldConstant .. | .fieldAdd .. | .fieldSubtract .. | .fieldMultiply .. |
    .fieldEmbed .. | .fieldEqual .. | .booleanConstant .. | .booleanAnd | .booleanOr | .booleanXor |
    .booleanEqual | .booleanNotEqual | .select .. | .boundedAt .. | .makeProduct .. | .getProduct .. |
    .branch .. | .loop .. | .loopCondition .. | .guard | .mark .. |
    .groupIdentity .. | .groupAdd .. | .groupScale .. | .groupEqual .. => []

abbrev dialect : Dialect := ⟨Ty, Op, Op.arguments, Op.results, Op.regions⟩

end Zkc.Source.Structured
