module

public import Zkc.Frontend.Lowered.Basic
public import Zkc.Frontend.Semantics.Static
public import Zkc.Frontend.Typed.Summary

@[expose] public section

set_option autoImplicit false

/-!
# The leaves of the typed tree

What a node of the typed tree carries besides its children: its mark (its place, its number,
what it was made for), its closed type, a binder with its type, a literal, the callee that an
application was resolved to, a conversion, and what the source writes of the roles of a
statement. What depends on roles beyond what is written is computed by the passes and kept in
their tables, by the number of the node.

Typing does not depend on facts (TY4), so nothing here is about a fact: a conversion that a
fact must justify is a node like any other, and whether the role that computes it has the fact
is decided by the core, on the code emitted for that role.
-/

namespace Zkc.Frontend.Typed

open Syntax

/-- The number of a node in its definition: its place in the order of the tree, depth first.
The numbering pass gives it; until then it is `0`. -/
abbrev NodeId := Nat

/-- What elaboration made a node for, when the source did not write it: the form of §4.2 of the
reference that it is part of the elaboration of. A refusal of the core at such a node is about
the form, at the place of the form. -/
inductive Derivation where
  /-- Written in the source. -/
  | written
  /-- A binding that keeps the order in which operands are written (HO4). -/
  | operand
  /-- The comparison of two values component by component (TY12). -/
  | equality
  /-- The loop of a comprehension (TY11). -/
  | comprehension
  /-- The loop of a binder form, with its accumulator (§3.5). -/
  | fold
  /-- An update that widens a `mut` name where a suite ends (TY10). -/
  | widening
  /-- A level of a pattern. -/
  | pattern
  deriving Inhabited, BEq, Repr

/-- The place of a node: where it stands in the source, its number in its definition, and what
elaboration made it for. -/
structure Mark where
  span : Span
  id : NodeId := 0
  derivation : Derivation := .written
  deriving Inhabited

/-- A node written at a place, before it has its number. -/
instance : Coe Span Mark := ⟨fun span => { span }⟩

/-- The mark of a node that elaboration makes for a derived form at a place. -/
def Mark.derived (span : Span) (derivation : Derivation) : Mark := { span, derivation }

/-- The mark and the closed type of an expression. -/
structure Info extends Mark where
  type : ClosedType
  deriving Inhabited

/-- A local binder at an instance: the binder of the lowered form with its closed type. A binder
that elaboration makes (one per result of an application bound to one name) is numbered after
those of the lowered form. -/
structure Binder where
  id : LocalId
  name : String
  span : Span
  type : ClosedType
  origin : BinderOrigin := .written
  mutable : Bool := false
  /-- Its type was written where it is bound. Every update of a `mut` name widens to it
  (TY10). -/
  declared : Bool := false
  /-- Its type is used exactly once (LN1). -/
  linear : Bool := false
  deriving Inhabited

/-- A literal. Its type is that of its node: a `nat`, a `bool`, an `index<n>`, a type of the
vocabulary (the numbers its model reads it from), or bytes. -/
inductive Literal where
  | nat (value : Nat)
  | bool (value : Bool)
  | index (value : Nat)
  | nominal (data : List Nat)
  | bytes (data : List Nat)
  deriving Inhabited, BEq

/-- Where a static natural that stands as a value comes from: what a message quotes for it. In
the emitted code it is a literal. -/
inductive StaticSource where
  /-- A numeral. -/
  | number
  | parameter (reference : ParameterRef)
  /-- A static name of a body, or the index of an iteration typed on its own. -/
  | «local» (binder : LocalId)
  /-- A static name of a module, a natural member, or a size of `log2( )`: as the source writes
  it, which identifies it as a term. -/
  | declared (text : String)
  deriving Inhabited

/-- A row of the vocabulary at its static arguments. -/
structure RowRef where
  name : String
  statics : Array StaticValue := #[]
  deriving Inhabited, BEq, Hashable

/-- The operations that the core owns and that an application names. Their static data (the
element type, the sizes) are the types of the operands and of the result. Making and taking
apart data are `construct` and `project`; the refining operations and the widenings are
conversions. An operation on naturals reads an `index<s>` operand through `fin.to_nat`, once per
term, after every operand is evaluated. -/
inductive CoreOperation where
  | natAdd | natSub | natMul | natDiv | natRem | natPow | natEqual | natLess
  | boolAnd | boolOr | boolNot | boolEqual
  | seqLength | seqAt | seqSlice | seqConcat | seqFill
  deriving Inhabited, BEq, Repr

namespace CoreOperation

/-- The name the reference gives the operation. -/
def name : CoreOperation → String
  | .natAdd => "nat.add" | .natSub => "nat.sub" | .natMul => "nat.mul" | .natDiv => "nat.div"
  | .natRem => "nat.rem" | .natPow => "nat.pow" | .natEqual => "nat.equal"
  | .natLess => "nat.less" | .boolAnd => "bool.and" | .boolOr => "bool.or"
  | .boolNot => "bool.not" | .boolEqual => "bool.equal" | .seqLength => "seq.length"
  | .seqAt => "seq.at" | .seqSlice => "seq.slice" | .seqConcat => "seq.concat"
  | .seqFill => "seq.fill"

/-- Whether the operation is defined on a domain only: an application of it is justified by
the facts of the role that computes it. -/
def hasDomain : CoreOperation → Bool
  | .natSub | .natDiv | .natRem | .seqAt | .seqSlice => true
  | _ => false

end CoreOperation

/-- What an application applies. -/
inductive Callee where
  /-- A function instance: `local.call`. -/
  | «instance» (id : InstanceId)
  /-- A row of the vocabulary: `local.apply`. -/
  | row (row : RowRef)
  /-- A row that a declaration binds, with the signature that it states when the vocabulary does
  not have the row. -/
  | boundRow (row : Typing.Row)
  | operation (operation : CoreOperation)
  /-- In the opaque elaboration of a definition generic over a module parameter (SP12): a
  member of the parameter's interface. `module` is the module instance that stands for the
  parameter; `declared` is the member's declaration in the interface. -/
  | member («module» : InstanceId) (name : String) (declared : Option DeclarationId)
  /-- An operation of specifications that has no form in the core: on `rational`, or on a
  `spec type`. A body that applies one is typed and not emitted. -/
  | specification (name : String)
  deriving Inhabited

/-- A conversion (TY5). The type converted from is that of the operand and the type converted
to that of the node. The first five widen and always hold. The next three go against the
widening: the role that computes one needs the fact that justifies it, and the refining
operation of the core is applied where the node stands. The last two convert the parts of a
collection or of a tuple, which is made again from the converted parts. -/
inductive Conversion where
  /-- `[T; s]` to `[T]`: `seq.unsized`. -/
  | unsized
  /-- `index<s>` to `nat`: `fin.to_nat`. -/
  | indexToNat
  /-- `index<s>` to `index<t>`, `s <= t`: `fin.widen`. -/
  | widenIndex
  /-- `nonzero<F>` to `F`: the row `field.from_nonzero`. -/
  | fromNonzero
  /-- `[T]` to `[T; s]` by the fact `length(t) == s`: `seq.sized`. -/
  | sized
  /-- A natural to `index<s>` by a range that ends below `s`: `nat.below`. -/
  | bounded
  /-- `F` to `nonzero<F>` by the fact that it is not zero: the restricted row
  `field.nonzero`. -/
  | nonzero
  | elements (inner : Conversion)
  /-- One conversion per component; none for a component that stays. -/
  | components (inner : Array (Option Conversion))
  /-- `[]` against a collection of no elements or an unsized collection: the collection of no
  elements of the element type, made again (TY6). -/
  | empty
  /-- One conversion to the type `middle`, then another. -/
  | andThen (first : Conversion) (middle : ClosedType) (second : Conversion)
  deriving Inhabited

namespace Conversion

/-- Whether a fact of the computing role must justify the conversion, or one inside it. -/
partial def needsFact : Conversion → Bool
  | .sized | .bounded | .nonzero => true
  | .elements inner => needsFact inner
  | .components inner => inner.any fun
    | some conversion => needsFact conversion
    | none => false
  | .andThen first _ second => needsFact first || needsFact second
  | _ => false

end Conversion

/-- What a message quotes for a node: the expression written at a place, or a text. -/
inductive Quote where
  | span (span : Span)
  | text (text : String)
  deriving Inhabited

/-- What a construction makes. -/
inductive Construction where
  | tuple
  /-- A sized collection of its elements. -/
  | sequence
  | record («instance» : InstanceId)
  /-- An alternative of a variant, from its payload. -/
  | alternative («variant» : InstanceId) (index : Nat)
  deriving Inhabited

/-- What the source says of the roles of a statement that computes (HO2, HO5): the roles
written after `@`, when some are. The roles that compute the statement are the placement
pass's, in its table; in local code the one role that runs the function computes everything. -/
structure Placement where
  written : Option RoleSet := none
  deriving Inhabited

/-- The attributes of an `if`, a `match` or a `for`. Its participants (CT1) are the placement
pass's. -/
structure Control where
  /-- The `mut` names declared outside the statement that its suites update, in the order in
  which the suites first update them. They are the carried values of a loop and the results of
  the arms of a choice; every arm ends with each of them at the type it has after the
  statement. -/
  updates : Array LocalId := #[]
  /-- The type each of those names has after the statement: the join of the types its suites
  leave it at (TY10). -/
  carried : Array ClosedType := #[]
  deriving Inhabited

end Zkc.Frontend.Typed
