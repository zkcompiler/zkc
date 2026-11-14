module

public import Zkc.Core.Types
public import Zkc.Frontend.Semantics.Program

@[expose] public section

set_option autoImplicit false

/-!
# What the lowered form and the typed tree share

The lowered form of a declaration is computed once and is the same for every instance; the typed
tree is computed per instance from it. Both name a local binder by its number in its
declaration, a role by its place in the roster, an event by its number in the text, and both
write the kernel statements with the same constructors. The types of this file are those that
do not depend on an instance.
-/

namespace Zkc.Frontend

open Syntax

/-- The functions of the fixed table that have no declaration (NL4). -/
inductive FixedFunction where
  | sum | product | all | any | inner
  deriving Inhabited, BEq, Repr

/-- One segment of a path. -/
inductive Step where
  /-- A local name of the definition: a parameter, a port, a binder, an index, a collected
  name. NL2 leaves one binding of a name in scope, so the name identifies it. -/
  | «local»
  | parameter (reference : ParameterRef)
  /-- `Self` in an interface. -/
  | self (interface : DeclarationId)
  /-- A declaration, found in a namespace. -/
  | declaration (id : DeclarationId)
  /-- A member of the interfaces or sorts that what came before has. For a static parameter,
  `Self` and members reached from them it was checked against what the text declares; for a
  declared type it is checked at the instance. `declared` is the member's declaration in an
  interface when the text determines it. -/
  | member (name : String) (declared : Option DeclarationId)
  | alternative («variant» : DeclarationId) (index : Nat)
  /-- A generated member of a protocol, a scheme or a layout module. -/
  | generated (name : String)
  | fixed (function : FixedFunction)
  /-- `log2`, the operator of sizes (TY2). -/
  | sizeOperator
  /-- A role of the roster of a protocol, where a role stands in a path: the static argument of
  `Inputs`, `Coins` and `Received` (§8), an argument `corrupted` of a goal (GL2). -/
  | role (name : String)
  /-- A word of a goal (GL2): a stage, `fixed`, `adaptive`, `hidden`, `observed`, `residual`. -/
  | word (word : String)
  /-- The label of a clause, as the value of the argument `clause` of a goal (GL2). Which clause
  it names is decided with the goal. -/
  | label (name : String)
  /-- A module that has no source file: its names are entries of the vocabulary (GL1). -/
  | vocabularyModule (path : String)
  /-- An entry of the vocabulary, named through its module. -/
  | entry («module» : String) (name : String)
  /-- A single name that no scope binds, where a value or a pattern after `case` stands, and that
  some variant of the program has as an alternative: the alternative of that name of the variant
  that typing expects there. When the expected type is not a variant with that alternative,
  typing refuses the name by NL3. -/
  | bareAlternative (name : String)
  deriving Inhabited, BEq, Repr


/-- A local binder of a declaration: a parameter, a port, a name bound by a statement, an
index, a collected name, or a name that lowering made. Numbered once, in the lowered form, in
the order of the text; a use names its binder by this number. -/
abbrev LocalId := Nat

/-- An event of a protocol body, numbered in the order of the text, depth first (EV3). -/
abbrev EventId := Nat

/-- A set of roles of a roster, by their places in it. Bit `r` is set when role `r` is in. -/
structure RoleSet where
  mask : Nat := 0
  deriving Inhabited, BEq, Hashable, Repr

namespace RoleSet

def empty : RoleSet := {}

def single (role : Nat) : RoleSet := ⟨1 <<< role⟩

/-- Every role of a roster of `count` roles. -/
def all (count : Nat) : RoleSet := ⟨(1 <<< count) - 1⟩

def contains (roles : RoleSet) (role : Nat) : Bool := roles.mask.testBit role

def insert (roles : RoleSet) (role : Nat) : RoleSet := ⟨roles.mask ||| (1 <<< role)⟩

def union (first second : RoleSet) : RoleSet := ⟨first.mask ||| second.mask⟩

def inter (first second : RoleSet) : RoleSet := ⟨first.mask &&& second.mask⟩

def isEmpty (roles : RoleSet) : Bool := roles.mask == 0

def subset (inner outer : RoleSet) : Bool := inner.mask &&& outer.mask == inner.mask

def ofArray (roles : Array Nat) : RoleSet := roles.foldl insert empty

/-- The roles in roster order. -/
def toArray (roles : RoleSet) : Array Nat := Id.run do
  let mut result := #[]
  for role in [0:roles.mask.log2 + 1] do
    if roles.contains role then result := result.push role
  return result

/-- The roles by name, in roster order, as a message writes them: `P, V`. -/
def names (roles : RoleSet) (roster : Array String) : Array String :=
  roles.toArray.map fun role => (roster[role]?).getD s!"role{role}"

end RoleSet

/-- The operators of expressions. What one means depends on the types of its operands, so the
lowered form keeps it as written and elaboration resolves it: to an operation of the core, a row
of the vocabulary, or the function of a declared type (NL6). -/
inductive Operator where
  | add | subtract | multiply | divide | remainder | power | negate
  | concatenate
  | equal | notEqual | less | lessEqual | greater | greaterEqual
  | not
  /-- `xs[i]` -/
  | index
  deriving Inhabited, BEq, Repr

/-- The folds of the mathematical forms (§3.5): `∑`, `∏`, `∀`, `∃`. Both spellings of a form are
one node. -/
inductive Fold where
  | sum | product | all | any
  deriving Inhabited, BEq, Repr

/-- How a conditional expression was written. `a and b` is `if a then b else false` and `a or b`
is `if a then true else b` (§4.2); the form is kept for messages and for emission, which may
apply the boolean operation of the core. -/
inductive ConditionalForm where
  | ifThenElse | and | or
  deriving Inhabited, BEq, Repr

/-- What an accumulator that elaboration makes for a derived form accumulates: the fold it is of,
or the collection of a comprehension. Emission reads it where a rule is stated on the source
form (a sum written term by term, the range of a carried sum). -/
inductive Accumulation where
  | sum | product | all | any
  /-- `∑` or `∏` of a declared type, by its functions `add` from `zero()` (`mul` from `one()`),
  or of a type member of a module parameter, by those members of its interface. -/
  | declared
  /-- The terms of a fold of elements of a sort, collected for the row of its form. -/
  | terms
  /-- The elements of a comprehension; with a filter, appended to where the filter holds. -/
  | comprehension
  /-- The value of an equality of structured values, set where the two are compared part by
  part (TY12). -/
  | equality
  deriving Inhabited, BEq, Repr

/-- Why a binder has no name of the source: what lowering made it for. -/
inductive BinderOrigin where
  /-- Written in the source. -/
  | written
  /-- The value of a pattern binding, taken apart by the bindings after it. -/
  | patternValue
  /-- The iteration number of a loop over a collection. -/
  | iteration
  /-- The accumulator of a fold, or the collection that a comprehension collects: what it
  accumulates. -/
  | accumulator (accumulation : Accumulation)
  /-- The result of an application bound to no name. -/
  | discarded
  /-- An operand that elaboration binds so that it is evaluated where the source evaluates it,
  before the operands and the conversions after it. Its uses are its value, the same term. -/
  | operand
  deriving Inhabited, BEq, Repr

/-- One segment of a path that stands for something outside the body: a declaration, a static
parameter, a member, an alternative. The steps are those of resolution, without `local`: a use of
a local name is a node of its own, which names its binder. -/
abbrev PathStep := Step

/-- An event of a protocol as its text gives it, for every instance (EV3): its number is its
place in this list. -/
structure SourceEvent where
  span : Span
  /-- The binder when it is one name, otherwise the name of `#[site(…)]`. -/
  name : Option String
  /-- Its parts, in order: `value`, or `to R` per receiver of a send to several. -/
  parts : Array String
  deriving Inhabited

end Zkc.Frontend
