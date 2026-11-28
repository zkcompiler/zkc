module

public import Zkc.Subject.Package

@[expose] public section
set_option autoImplicit false

/-! What a statement of a property is stated over: the entries of the installation, the written
root, the typed positions of deployed inputs, and a relation applied at its statement positions.
The module imports nothing of a goal: no table of caps, no decision, no fields. -/

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

/-- A relation applied at its statement positions (the short application `R(a…)` of the
language): the relation, how its parameters split into statement and witness parameters (the
arity), its Boolean result, and the deployed inputs in its statement positions, which both
parties hold. A statement of a property that is stated over a short application reads nothing
else of the contract: not the place of a clause, not its witness operands, not a goal's fields. -/
structure ShortApplication {V : Vocabulary} {pkg : Package V} (root : WrittenRoot pkg) where
  relation : FunctionEntry pkg
  arity : Fin (relation.header.ins.length + 1)
  boolean : relation.header.outs = [.bool]
  statement : HList (SharedPort root.entry.header.ins root.prover root.verifier)
    (relation.header.ins.take arity)

end Zkc.Subject
