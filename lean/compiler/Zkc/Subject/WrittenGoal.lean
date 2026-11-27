module

public import Zkc.Subject.Bound
public import Zkc.Subject.Charges
public import Zkc.Subject.ShortApplication
public import Zkc.Vocabulary.Security

@[expose] public section
set_option autoImplicit false

namespace Zkc.Subject
open Core

/-- An instantiated deciding clause: its short application, its place in the source contract
(counting every clause), and the deployed inputs that the prover gives the witness parameters,
where the source names them. -/
structure Decision {V : Vocabulary} {pkg : Package V} (root : WrittenRoot pkg) where
  application : ShortApplication root
  place : Nat
  witness : Option (HList (PortRef root.entry.header.ins) (application.relation.header.ins.drop application.arity))

/-- The source goal's own arguments, its table of caps, its bound, and where the bound comes
from. -/
structure GoalFields where
  specification : List Nat
  /-- The table of caps of the root at the goal's proof arguments. There is none where the
  contract has a charge that a table has no place for; such a goal writes its ceiling. -/
  caps : Option CapTable
  bound : Bound
  /-- Whether the source writes the bound, as the goal's ceiling. Where it does not, the bound is
  the total of the table (`CapTable.sumsTo`). -/
  ceiling : Bool

/-- A fraction of naturals, not reduced, at which the kernel adds a table up. It is zero where
its denominator is zero, as a rational divided by zero is, so its arithmetic is that of the
nonnegative rationals; it rests on no axiom. -/
structure Fraction where
  numerator : Nat
  denominator : Nat

namespace Fraction

/-- The fraction with a denominator that is not zero. -/
def normal (f : Fraction) : Fraction := if f.denominator == 0 then ⟨0, 1⟩ else f

instance : NatCast Fraction := ⟨fun n => ⟨n, 1⟩⟩
instance : Zero Fraction := ⟨⟨0, 1⟩⟩
instance : Add Fraction := ⟨fun a b =>
  let a := a.normal; let b := b.normal
  ⟨a.numerator * b.denominator + b.numerator * a.denominator, a.denominator * b.denominator⟩⟩
instance : Mul Fraction := ⟨fun a b =>
  let a := a.normal; let b := b.normal
  ⟨a.numerator * b.numerator, a.denominator * b.denominator⟩⟩
instance : Div Fraction := ⟨fun a b =>
  let a := a.normal; let b := b.normal
  normal ⟨a.numerator * b.denominator, a.denominator * b.numerator⟩⟩
instance : Max Fraction := ⟨fun a b =>
  let a := a.normal; let b := b.normal
  if a.numerator * b.denominator ≤ b.numerator * a.denominator then b else a⟩

/-- Whether the fraction is the number `numerator / denominator`, the denominator not zero. -/
def isNumber (f : Fraction) (numerator denominator : Nat) : Bool :=
  let f := f.normal
  f.numerator * denominator == numerator * f.denominator

end Fraction

/-- **A bound that is taken from a table is the table's**: the table counts as the stored program
does, and its total is the bound's number. A closed decision over fractions of naturals,
evaluated by the kernel where a challenge is declared over a goal that writes no ceiling. -/
def CapTable.sumsTo {V : Vocabulary} (table : CapTable) (p : NamedProgram V) (root : Key)
    (bound : Bound) : Bool :=
  table.counted p root &&
    (table.totalAt Fraction table.root).isNumber bound.numerator bound.denominator

/-- The semantic consumer takes one goal with its selected decision. -/
structure WrittenGoal {V : Vocabulary} {pkg : Package V} (root : WrittenRoot pkg) where
  decision : Decision root
  fields : GoalFields

/-- A finite table whose issuer chooses a bounded selector for its named rows. -/
structure BoundedTable (α : Type) where
  size : Nat
  get : Fin size → α

/-- A goal's row: the path of its declaration in the source (its components), the property that
it names, the position of its decision in the same subject, and its fields. What a goal
publishes is stated from its row and named by its path. -/
structure GoalSlot (decisions : Nat) where
  path : List String
  property : Zkc.Security.Property
  clause : Fin decisions
  fields : GoalFields

/-- Source names for readers, aligned before dropping any verifier-invisible inputs. -/
structure RootOrigins {V : Vocabulary} {pkg : Package V} (root : WrittenRoot pkg) where
  /-- The defining file module distinguishes a nested module from an imported module of the same name. -/
  schemeFileModule : Array String
  schemePath : String
  inputNames : Array String
  aligned : inputNames.size = root.entry.header.ins.length

/-- A written subject: its clauses, its goal rows, and the source names of its root, which a
command over the subject is given with its rows. No published statement reaches the origins. -/
structure WrittenSubject {V : Vocabulary} {pkg : Package V} (root : WrittenRoot pkg) where
  clauses : BoundedTable (Decision root)
  goals : BoundedTable (GoalSlot clauses.size)
  origins : RootOrigins root

def WrittenSubject.goalAt {V : Vocabulary} {pkg : Package V} {root : WrittenRoot pkg}
    (subject : WrittenSubject root) (index : Fin subject.goals.size) : WrittenGoal root :=
  let goal := subject.goals.get index
  ⟨subject.clauses.get goal.clause, goal.fields⟩

end Zkc.Subject
