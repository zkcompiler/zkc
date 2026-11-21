module

public import Zkc.Frontend.Written.Root
public import Zkc.Frontend.Written.Charge
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

A goal is read by one function, and what its statement says is in what that function returns:
the scheme with its prover and its verifier, the clause, the relation, the operands, the proof
arguments, the ceiling and the table of caps of the root at the goal's proof arguments. The
records are made here and nowhere else, so a consumer cannot pair a goal with another goal's
role, operands or table.

An operand of the clause is an input of the deployed header, by its place there. The ports of
the source and the inputs of the header are two lists: a `spec` port is in the first and not in
the second (SX2). The place is found in the list from which the header is emitted
(`Typed.ProtocolBody.deployedPorts`), and the place among the source's ports does not leave
this file. A statement operand is an input that both the prover and the verifier of the scheme
hold: the statement of the scheme (SC4), of which GL3 asks every statement argument of the
clause to be a function. An input that the verifier holds alone is read by the deciding role
(SX6) and is not determined by the statement, so it is refused. A `spec` port is admitted by
GL3 under a fixed statement, as a value that no role holds; a statement with such a value is
not issued yet, and the operand is refused.

Reading a charge at a site states no claim and asks for no clause (`goalDrawCharge`): a caller
without a contract reads the charges of its callees under the proof arguments of each use.

What goals of one scheme claim is one package (`goalClaims`): goals of two schemes are refused,
also where the two schemes have one protocol and one verifier. The relation of each clause is
instantiated at the static values of its application and at the proof values of its goal, in
one state that starts as the state of the root, so its key is of the same numbering as the
deployed definitions; and the package is what the root reaches, in the order and with the
stored definitions of the root's own package, followed by what each relation adds. A statement
about a goal has one fact of admission and names the protocol and the relation by their keys.
-/

namespace Zkc.Frontend.Written
open Syntax

/-- The prover and the verifier of a scheme at its written stage, by their places in the
roster: the online roles, from the admitted header of the scheme's protocol. -/
def schemeParties (c : AdmittedRoot) (scheme : SchemeEntry) : ExportM (Nat × Nat) := do
  let some (.protocol code) := c.state.results.body? c.id
    | throw "missing the typed protocol of the scheme"
  let some ⟨header, _⟩ := c.evidence.admitted.program.findProtocol ⟨c.id⟩
    | throw "missing the admitted header of the scheme's protocol"
  let parties ← writtenParties scheme code.roles
  let some found := Core.onlineParties header (List.replicate code.roles.size .online)
      parties.interactive parties.declaredProver
    | refuse parties.place "GL3" "the scheme does not determine its prover and its verifier"
  return found

/-- The verifier of a scheme at its written stage, by its place in the roster. -/
def schemeVerifier (c : AdmittedRoot) (scheme : SchemeEntry) : ExportM Nat :=
  (·.2) <$> schemeParties c scheme

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

/-- What one written soundness goal claims, in the package of its claims. It is made by
`goalClaims` alone. -/
structure ClaimedGoal where
  private mk ::
  goal : String
  clause : DecidingClause
  /-- The relation of the clause at the static values of its application and the proof values
  of the goal: the key of its definition in the package. Two goals that give one value claim
  one relation. -/
  relation : InstanceId
  /-- For each statement parameter of the relation, in their order, the input of the deployed
  header that is its operand, by its place among the inputs of the header. Each is held by the
  prover and the verifier of the scheme. -/
  statement : Array Nat
  /-- For each witness parameter of the relation, the input of the deployed header that the
  clause gives for it, by its place there; none where the relation has witness parameters and
  the clause is written short. -/
  witness : Option (Array Nat)
  /-- The values of the goal's proof arguments, in the order of the specification-only static
  parameters of the scheme's protocol. -/
  specification : Array Nat
  /-- The ceiling that the goal states, when it states one (GL4). -/
  ceiling : Option Rat
  /-- The table of caps of the root at the goal's proof arguments (SX8): every charge that the
  root reaches, by use. The bound of the goal's statement is its total. -/
  caps : CapTable
  /-- The draws of the root by the names of their sites, each with the keys of the draws that
  realize it: every named draw that is emitted, charged or not. -/
  sites : SiteKeys

/-- What written soundness goals of one scheme claim, as one package. It is made by
`goalClaims` alone. -/
structure GoalClaims where
  private mk ::
  /-- The root of the claims: the protocol of the scheme. -/
  root : InstanceId
  /-- The scheme of the goals, by its declaration, and its name. -/
  scheme : DeclarationId
  schemeName : String
  /-- The prover and the verifier of the scheme, by their places in the roster. The verifier is
  the deciding role of every goal. -/
  prover : Nat
  verifier : Nat
  /-- The names that the source gives the inputs of the deployed header, in their order. -/
  inputs : Array String
  goals : List ClaimedGoal
  /-- The state in which the relations are instantiated and their bodies typed. -/
  state : Compile.State
  /-- The package: what the root reaches, then what each relation adds, in the order of the
  goals. -/
  emission : Emit.RootEmission
  emitted : Typing.emitRoots state (root :: goals.map (·.relation)) = .ok emission
  evidence : (emission.package ⟨[],[],[],[],[]⟩).Admission

/-- The input of the deployed header that an operand of a clause is, by its place among the
inputs. With `statement`, the operand is at a statement parameter of the relation: it is then an
input that the roles of `statement` (the prover and the verifier of the scheme) both hold. -/
def operandPlace (body : Typed.ProtocolBody) (statement : Option (Nat × Nat))
    (operand : Lowered.Expr) : ExportM Nat :=
  match operand with
  | .local at_ id => do
    let some port := body.ports.find? (·.binder.id == id)
      | refuse at_ "WK-CLAUSE" "an operand of the clause is no port of the protocol"
    let name := port.binder.name
    if port.specification then
      refuse at_ "WK-CLAUSE" (s!"`{name}` is a specification port: a statement about a fixed " ++
        "specification value is not issued yet")
    if let some (prover, verifier) := statement then
      unless port.holders.contains prover && port.holders.contains verifier do
        let holders := ", ".intercalate
          (port.holders.toArray.toList.map fun role => body.roster.getD role s!"role {role}")
        refuse at_ "GL3" (s!"`{name}` is held by {holders}: a statement argument of the clause is " ++
          "a function of the scheme's statement, the inputs that the prover and the verifier " ++
          "both hold (SC4)")
    let some place := body.inputPlace? id
      | throw s!"WK-CORE: the port `{name}` has no place among the deployed inputs"
    return place
  | other => refuse other.span "WK-CLAUSE" "an operand of the clause that is no port is not read yet"

/-- What a goal claims, with its relation instantiated in `state` and the state after it, and
the scheme that the goal names. -/
@[no_expose] def claimedGoal (c : AdmittedRoot) (state : Compile.State) (goal : String) :
    ExportM (ClaimedGoal × SchemeEntry × Compile.State) := do
  let (selected, _) ← selectNamedGoal c.state goal .soundness
  unless selected.scheme.protocol == c.id do throw "GL3: goal selects a different protocol"
  let clause ← goalClause c goal
  let some application := clause.application
    | refuse clause.span "WK-CLAUSE" "the clause applies no relation"
  let some checked := c.state.results.checked? c.id
    | throw "missing the checked protocol of the scheme"
  let .protocol body := checked.definition.body
    | throw "the root of the scheme is no protocol"
  let parties ← schemeParties c selected.scheme
  let (typed, state) ← evaluate state clause.span
    (Typing.typedClauses c.id selected.specification (only := some clause.place))
  let some (_, tree) := typed.find? (·.1 == clause.place)
    | refuse clause.span "WK-CLAUSE" "the clause was not typed"
  let .apply _ (.instance relation) _ := tree
    | refuse clause.span "WK-CLAUSE" "the clause is no application of a relation instance"
  let statement ← application.statement.mapM (operandPlace body (some parties))
  let some found := c.state.program.declarations[application.relation]?
    | throw "missing the relation of the clause"
  let .relation node := found.node | throw "the clause applies a declaration that is no relation"
  let witness ←
    if (node.witness.getD #[]).isEmpty then pure (some #[])
    else if application.witness.isEmpty then pure none
    else some <$> application.witness.mapM (operandPlace body none)
  let (caps, sites) ← goalCaps c selected.specification
  return ({ goal, clause, relation, statement, witness, specification := selected.specification,
            ceiling := selected.ceiling, caps, sites }, selected.scheme, state)

/-- What written soundness goals of one scheme claim (GL3), as one package: for each goal its
clause, the relation that the clause applies as a definition at the proof values of the goal,
and the ports that are its operands. The relations are instantiated one after another in one
state, so each has a key of its own beside the deployed definitions, which are those of the
root's own package, first and unchanged. -/
@[no_expose] def goalClaims (c : AdmittedRoot) (goals : List String) : ExportM GoalClaims := do
  let mut state := c.state
  let mut claimed := []
  let mut first : Option (String × SchemeEntry) := none
  for goal in goals do
    let (next, named, after) ← claimedGoal c state goal
    match first with
    | some (earlierGoal, earlier) =>
      unless earlier.declaration == named.declaration do
        refuse named.span "WK-GOAL" (s!"the goal `{earlierGoal}` is of the scheme `{earlier.name}` and " ++
          s!"the goal `{goal}` of the scheme `{named.name}`: the claims of a package are of one " ++
          "scheme; read the goals of each scheme apart")
    | none => first := some (goal, named)
    state := after
    claimed := claimed ++ [next]
  let some (_, scheme) := first | throw "WK-GOAL: a package of claims has a goal"
  let (prover, verifier) ← schemeParties c scheme
  -- the header that is emitted has the deployed ports of the checked body, one for one
  let some checked := c.state.results.checked? c.id | throw "missing the checked protocol of the scheme"
  let .protocol body := checked.definition.body | throw "the root of the scheme is no protocol"
  match emitted : Typing.emitRoots state (c.id :: claimed.map (·.relation)) with
  | .error (.waiting why) => throw s!"WK-CORE: a relation of the claims waits: {why}"
  | .error (.noCoreForm why) => throw s!"WK-CORE: a relation of the claims has no core form: {why}"
  | .error (.defect why) => throw s!"WK-CORE: the claims did not emit: {why}"
  | .ok emission =>
    let .ok evidence := (emission.package ⟨[],[],[],[],[]⟩).checkEvidence
      | throw "WK-CORE: admission refused the package of the claims"
    let package := emission.package ⟨[],[],[],[],[]⟩
    let some (.protocol _ _ inputs _ _) := package.named.definitions.find? (·.key.number == c.id)
      | throw "WK-CORE: the package of the claims does not have the root"
    unless inputs.map (·.holders) == body.deployedPorts.toList.map (·.holders.toArray.toList) do
      throw "WK-CORE: the inputs of the deployed header are not the deployed ports of the protocol"
    -- the counts of each goal's table are those of the program that the module prints
    for goal in claimed do
      unless goal.caps.counted package.named ⟨c.id⟩ do
        throw s!"WK-CHARGE: the counts of the table of caps of `{goal.goal}` are not those of the package"
    return { root := c.id, scheme := scheme.declaration, schemeName := scheme.name, prover, verifier
             inputs := body.deployedPorts.map (·.binder.name)
             goals := claimed, state, emission, emitted, evidence }

end Zkc.Frontend.Written
