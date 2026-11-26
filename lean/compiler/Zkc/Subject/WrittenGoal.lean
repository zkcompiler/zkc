module

public import Zkc.Subject.Charges
public import Zkc.Subject.ShortApplication

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

/-- The source goal's own arguments and numerical data. -/
structure GoalFields where
  specification : List Nat
  caps : CapTable
  ceiling : Option Rat

/-- The semantic consumer takes one goal with its selected decision. -/
structure WrittenGoal {V : Vocabulary} {pkg : Package V} (root : WrittenRoot pkg) where
  decision : Decision root
  fields : GoalFields

/-- A finite table whose issuer chooses a bounded selector for its named rows. -/
structure BoundedTable (α : Type) where
  size : Nat
  get : Fin size → α

/-- A goal's fields and the position of its decision in the same subject. -/
structure GoalSlot (decisions : Nat) where
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

end Zkc.Subject
