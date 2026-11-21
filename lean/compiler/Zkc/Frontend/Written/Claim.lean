module

public import Zkc.Frontend.Written.Root
public import Zkc.Frontend.Emit.Root
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

What goals of one scheme claim is one package (`goalClaims`). The relation of each clause is
instantiated at the static values of its application and at the proof values of its goal, in
one state that starts as the state of the root, so its key is of the same numbering as the
deployed definitions; and the package is what the root reaches, in the order and with the
stored definitions of the root's own package, followed by what each relation adds. A statement
about a goal has one fact of admission and names the protocol and the relation by their keys.
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

/-- What one written soundness goal claims, in the package of its claims. -/
structure ClaimedGoal where
  goal : String
  clause : DecidingClause
  /-- The relation of the clause at the static values of its application and the proof values
  of the goal: the key of its definition in the package. Two goals that give one value claim
  one relation. -/
  relation : InstanceId
  /-- For each statement parameter of the relation, in their order, the port of the protocol
  that is its operand, by its place among the ports. -/
  statement : Array Nat
  /-- For each witness parameter of the relation, the port that the clause gives for it; none
  where the relation has witness parameters and the clause is written short. -/
  witness : Option (Array Nat)

/-- What written soundness goals of one scheme claim, as one package. -/
structure GoalClaims where
  /-- The root of the claims: the protocol of the scheme. -/
  root : InstanceId
  goals : List ClaimedGoal
  /-- The state in which the relations are instantiated and their bodies typed. -/
  state : Compile.State
  /-- The package: what the root reaches, then what each relation adds, in the order of the
  goals. -/
  emission : Emit.RootEmission
  emitted : Typing.emitRoots state (root :: goals.map (·.relation)) = .ok emission
  evidence : (emission.package ⟨[],[],[],[],[]⟩).Admission

/-- The port of a protocol that an operand of a clause is, by its place among the ports. -/
def operandPort (head : Lowered.ProtocolHead) (operand : Lowered.Expr) : ExportM Nat :=
  match operand with
  | .local at_ id =>
    match head.ports.findIdx? (·.binder.id == id) with
    | some index => pure index
    | none => refuse at_ "WK-CLAUSE" "an operand of the clause is no port of the protocol"
  | other => refuse other.span "WK-CLAUSE" "an operand of the clause that is no port is not read yet"

/-- What a goal claims, with its relation instantiated in `state` and the state after it. -/
def claimedGoal (c : AdmittedRoot) (state : Compile.State) (goal : String) :
    ExportM (ClaimedGoal × Compile.State) := do
  let (selected, _) ← selectNamedGoal c.state goal .soundness
  unless selected.scheme.protocol == c.id do throw "GL3: goal selects a different protocol"
  let clause ← goalClause c goal
  let some application := clause.application
    | refuse clause.span "WK-CLAUSE" "the clause applies no relation"
  let some key := c.state.results.key? c.id | throw "missing the instance of the scheme's protocol"
  let some {content := .protocol head .., ..} := c.state.env.modules.lowered? key.declaration
    | throw "missing the protocol of the scheme"
  let (typed, state) ← evaluate state clause.span (Typing.typedClauses c.id selected.specification)
  let some (_, tree) := typed.find? (·.1 == clause.place)
    | refuse clause.span "WK-CLAUSE" "the clause was not typed"
  let .apply _ (.instance relation) _ := tree
    | refuse clause.span "WK-CLAUSE" "the clause is no application of a relation instance"
  let statement ← application.statement.mapM (operandPort head)
  let some found := c.state.program.declarations[application.relation]?
    | throw "missing the relation of the clause"
  let .relation node := found.node | throw "the clause applies a declaration that is no relation"
  let witness ←
    if (node.witness.getD #[]).isEmpty then pure (some #[])
    else if application.witness.isEmpty then pure none
    else some <$> application.witness.mapM (operandPort head)
  return ({ goal, clause, relation, statement, witness }, state)

/-- What written soundness goals of one scheme claim (GL3), as one package: for each goal its
clause, the relation that the clause applies as a definition at the proof values of the goal,
and the ports that are its operands. The relations are instantiated one after another in one
state, so each has a key of its own beside the deployed definitions, which are those of the
root's own package, first and unchanged. -/
def goalClaims (c : AdmittedRoot) (goals : List String) : ExportM GoalClaims := do
  let mut state := c.state
  let mut claimed := []
  for goal in goals do
    let (next, after) ← claimedGoal c state goal
    state := after
    claimed := claimed ++ [next]
  match emitted : Typing.emitRoots state (c.id :: claimed.map (·.relation)) with
  | .error (.waiting why) => throw s!"WK-CORE: a relation of the claims waits: {why}"
  | .error (.noCoreForm why) => throw s!"WK-CORE: a relation of the claims has no core form: {why}"
  | .error (.defect why) => throw s!"WK-CORE: the claims did not emit: {why}"
  | .ok emission =>
    let .ok evidence := (emission.package ⟨[],[],[],[],[]⟩).checkEvidence
      | throw "WK-CORE: admission refused the package of the claims"
    return { root := c.id, goals := claimed, state, emission, emitted, evidence }

end Zkc.Frontend.Written
