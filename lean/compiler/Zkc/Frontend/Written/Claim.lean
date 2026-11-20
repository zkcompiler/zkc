module

public import Zkc.Frontend.Written.Root
public import Zkc.Core.Scheme.Roles

@[expose] public section

/-!
The clause of a written soundness goal.

A soundness goal forms its claim from one `proves` or `reduces` clause of the contract of its
scheme's protocol: the one that the goal names by its label, or the only one (GL3). The clause
is given as the source wrote it, with the relation it applies and the operands in the order of
the relation's parameters, so that a consumer can state what the goal claims and an independent
reader can compare it with the source.

Reading a charge at a site states no claim and asks for no clause (`goalDrawCharge`): a caller
without a contract reads the charges of its callees under the proof arguments of each use.
-/

namespace Zkc.Frontend.Written
open Syntax

/-- The verifier of a scheme at its written stage, by its place in the roster: the online role
that is not the prover, from the admitted header of the scheme's protocol. -/
def schemeVerifier (c : AdmittedRoot) (scheme : SchemeEntry) : ExportM Nat := do
  let some (.protocol code) := c.state.results.body? c.id
    | throw "missing the typed protocol of the scheme"
  let some ⟨header, _⟩ := c.evidence.admitted.program.findProtocol ⟨c.id⟩
    | throw "missing the admitted header of the scheme's protocol"
  let parties ← writtenParties scheme code.roles
  let some (_, verifier) := Core.onlineParties header (List.replicate code.roles.size .online)
      parties.interactive parties.declaredProver
    | refuse parties.place "GL3" "the scheme does not determine its prover and its verifier"
  return verifier

/-- The clause from which a written soundness goal forms its claim (GL3): the deciding clause
that the goal names, or the only one of the contract, whose deciding role is the verifier of
the scheme. -/
def goalClause (c : AdmittedRoot) (goal : String) : ExportM DecidingClause := do
  let (selected, _) ← selectNamedGoal c.state goal .soundness
  unless selected.scheme.protocol == c.id do throw "GL3: goal selects a different protocol"
  let some key := c.state.results.key? c.id | throw "missing the instance of the scheme's protocol"
  let place := (selected.goal.map (·.span)).getD selected.scheme.span
  let clause ← decidingClause c.state key.declaration selected.clause place
  let verifier ← schemeVerifier c selected.scheme
  unless clause.role == some verifier do
    refuse clause.span "GL3" "the deciding role of the clause is the verifier of the scheme"
  return clause

end Zkc.Frontend.Written
