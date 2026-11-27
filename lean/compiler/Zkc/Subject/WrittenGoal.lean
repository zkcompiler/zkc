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

/-- The source goal's own arguments, its table of caps and its bound. -/
structure GoalFields where
  specification : List Nat
  caps : CapTable
  bound : Bound

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

structure WrittenSubject {V : Vocabulary} {pkg : Package V} (root : WrittenRoot pkg) where
  clauses : BoundedTable (Decision root)
  goals : BoundedTable (GoalSlot clauses.size)

def WrittenSubject.goalAt {V : Vocabulary} {pkg : Package V} {root : WrittenRoot pkg}
    (subject : WrittenSubject root) (index : Fin subject.goals.size) : WrittenGoal root :=
  let goal := subject.goals.get index
  ⟨subject.clauses.get goal.clause, goal.fields⟩

/-- Source names for readers, aligned before dropping any verifier-invisible inputs. -/
structure RootOrigins {V : Vocabulary} {pkg : Package V} (root : WrittenRoot pkg) where
  /-- The defining file module distinguishes a nested module from an imported module of the same name. -/
  schemeFileModule : Array String
  schemePath : String
  inputNames : Array String
  aligned : inputNames.size = root.entry.header.ins.length

/-- The source names of a written root, read by the tools that name the binders of a library
term (`ZkcFormal.Written.SourceNames`). An instance is a fact of the subject; no published
statement reaches it. -/
class SourceNames {V : Vocabulary} {pkg : Package V} (root : WrittenRoot pkg) where
  origins : RootOrigins root

end Zkc.Subject
