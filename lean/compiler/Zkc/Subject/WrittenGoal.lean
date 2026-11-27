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

/-- **The number of a goal, with the table that goes with it.** Where the source writes no
ceiling, the bound is the total of the goal's table of caps, so there is a table. Where the
source writes the bound as the goal's ceiling, there is a table unless the contract has a charge
that a table has no place for. -/
inductive GoalNumber where
  | total (caps : CapTable) (bound : Bound)
  | ceiling (bound : Bound) (caps : Option CapTable)

/-- The bound that the goal claims. -/
def GoalNumber.bound : GoalNumber → Bound
  | .total _ bound | .ceiling bound _ => bound

/-- The table of caps, where the goal has one. -/
def GoalNumber.caps : GoalNumber → Option CapTable
  | .total caps _ => some caps
  | .ceiling _ caps => caps

/-- Whether the source writes the bound, as the goal's ceiling. -/
def GoalNumber.written : GoalNumber → Bool
  | .total .. => false
  | .ceiling .. => true

/-- The source goal's own arguments and its number. -/
structure GoalFields where
  specification : List Nat
  number : GoalNumber

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

end Zkc.Subject
