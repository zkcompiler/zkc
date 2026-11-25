module

public import Zkc.Subject.Charges
public import Zkc.Subject.Package

@[expose] public section
set_option autoImplicit false

namespace Zkc.Subject
open Core

/-- A protocol in the installation, located by the key of its own header. -/
structure ProtocolEntry {V : Vocabulary} (pkg : Package V) where
  header : ProtocolHeader V
  member : Member pkg.installed.headers.protocols header
  found : pkg.installed.findProtocol header.key = some ⟨header, member⟩

/-- A function in the installation, located by the key of its own header. -/
structure FunctionEntry {V : Vocabulary} (pkg : Package V) where
  header : FnHeader V
  member : Member pkg.installed.headers.fns header
  found : pkg.installed.find header.key = some (.fn member)

/-- The ordered parties of a written scheme, in the deployed protocol's roster. -/
structure WrittenRoot {V : Vocabulary} (pkg : Package V) where
  entry : ProtocolEntry pkg
  prover : Fin entry.header.roles
  verifier : Fin entry.header.roles
  distinct : prover ≠ verifier

/-- A typed position in the full deployed input list, including its holders. -/
structure PortRef {V : Vocabulary} (ports : List (LTy V)) (t : V.Ty) where
  holders : Holders
  member : Member ports ⟨t, holders⟩

/-- A statement operand must be available to both parties of the scheme. -/
structure SharedPort {V : Vocabulary} (ports : List (LTy V)) (prover verifier : Role)
    (t : V.Ty) extends PortRef ports t where
  heldByProver : prover ∈ holders
  heldByVerifier : verifier ∈ holders

/-- An instantiated deciding clause. Its position counts every clause in the source contract.
The arity splits the actual function signature into statement and witness parameters. -/
structure Decision {V : Vocabulary} {pkg : Package V} (root : WrittenRoot pkg) where
  place : Nat
  relation : FunctionEntry pkg
  arity : Fin (relation.header.ins.length + 1)
  boolean : relation.header.outs = [.bool]
  statement : HList (SharedPort root.entry.header.ins root.prover root.verifier)
    (relation.header.ins.take arity)
  witness : Option (HList (PortRef root.entry.header.ins) (relation.header.ins.drop arity))

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
  schemePath : String
  inputNames : Array String
  aligned : inputNames.size = root.entry.header.ins.length

end Zkc.Subject
