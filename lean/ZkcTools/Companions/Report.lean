module

public meta import ZkcTools.Companions.Assembly
public meta import ZkcTools.Companions.Goals

public meta section

/-! One authoring record for an actual attempted obligation. Source identities
and spans come from the owner of the source export; proof-search addresses are
not substituted for them. Stub text is append-only user scaffolding. Neither a
stub marker nor an authoring result supplies a security receipt or assumption. -/
set_option autoImplicit false
namespace ZkcTools.Companions
open Lean Meta

/-- One-based source positions, with Unicode-character columns. -/
structure SourceSpan where
  file : String
  startLine : Nat
  startColumn : Nat
  endLine : Nat
  endColumn : Nat
  deriving ToJson

structure StubLocation where
  file : String
  line : Nat
  deriving ToJson

/-- Retained source metadata, not proof authority or a reconstructed source span.
The capture digest does not attest to the native exporter or dependency closure. -/
structure SourceIdentity where
  owner : String
  symbol : String
  capture : String
  deriving ToJson

/-- Frontend canonical instance key for a Lean-owned implementation law. -/
def SourceIdentity.implementationKey (subject : SourceIdentity) (label : String) : String :=
  (toJson ([toJson "zkc.companion/0", toJson subject.owner,
    toJson (["instance", subject.symbol] : List String), toJson "implementation-law",
    toJson (["label", label] : List String)] : List Json)).compress

structure Obligation where
  identity : String
  source : Option SourceSpan := none
  responsibility : String
  expected : Expr
  stub : Option StubLocation := none
  stubText : Option String := none
  /-- An independently generated type declaration, closed over its complete
  telescope. When supplied, its value must be the requested type. -/
  goal : Option Name := none
  subject : Option SourceIdentity := none
  proofNavigation : Option StubLocation := none

/-- Check the independently fixed goal before attempting any proof method. -/
def validateGoal (expected : Expr) (goal : Name) : MetaM Unit := do
  let variables := (← getLCtx).foldl (fun variables declaration =>
    if declaration.isAuxDecl then variables else variables.push declaration.toExpr) #[]
  let closed ← instantiateMVars (← mkForallFVars variables (← instantiateMVars expected))
  if closed.hasFVar || closed.hasMVar then
    throwError "generated companion goal must have a fixed closed type (free variables: {closed.hasFVar}, expression metavariables: {closed.hasExprMVar}): {closed}"
  let declaration ← mkConstWithFreshMVarLevels goal
  unless ← withoutModifyingState <| isDefEq declaration closed do
    throwError "generated companion goal does not match the complete expected telescope: {goal}\nGenerated: {← whnf declaration}\nExpected: {closed}"

/-- Detailed diagnostics are created on demand, independently of evidence
selection. The expected type is the input to assembly, not inferred from the
selected proof or an error message. -/
def report (obligation : Obligation) (result : Assembly) : MetaM Json := do
  let expected ← instantiateMVars obligation.expected
  let render (value : Expr) : MetaM String :=
    withOptions (fun options => options.setBool `pp.fullNames true) do
      return toString (← ppExpr value)
  let mut variables := #[]
  let mut context := #[]
  for declaration in ← getLCtx do
    -- Recursive declaration placeholders are elaborator bookkeeping, not
    -- premises that may authorize a companion for the enclosing theorem.
    if declaration.isAuxDecl then continue
    variables := variables.push declaration.toExpr
    let value ← declaration.value?.mapM render
    context := context.push <| Json.mkObj [
      ("name", toJson declaration.userName.toString),
      ("type", toJson (← render declaration.type)), ("value", toJson value)]
  -- Preserve local lets as lets, and include hypotheses even when the result
  -- does not mention their proof terms. Pretty-printing the bare goal loses them.
  let closed ← instantiateMVars (← mkForallFVars variables expected)
  if closed.hasFVar then throwError "companion report has an unclosed expected type"
  if let some goal := obligation.goal then
    validateGoal expected goal
  let expectedText ← render expected
  let environment ← getEnv
  let goalModule := obligation.goal.bind fun goal =>
    (environment.getModuleIdxFor? goal).map fun index =>
      environment.header.moduleNames[index.toNat]!.toString
  let (status, method, reason, attempts) := match result with
    | .discharged _ method attempts => ("discharged", some method, none, attempts)
    | .openObligation reason attempts => ("open", none, some reason, attempts)
    | .refused reason attempts => ("refused", none, some reason, attempts)
  return Json.mkObj [
    ("schema", toJson "zkc.companion-obligation/0"),
    ("status_scope", toJson "authoring only; receipt audit remains authoritative"),
    ("identity", toJson obligation.identity), ("source_span", toJson obligation.source),
    ("source_identity", toJson obligation.subject),
    ("proof_navigation", toJson obligation.proofNavigation),
    ("responsibility", toJson obligation.responsibility), ("expected_type", toJson expectedText),
    ("context", Json.arr context), ("closed_expected_type", toJson (← render closed)),
    ("expected_constants", toJson (closed.getUsedConstants.toList.map Name.toString)),
    ("dependency_scope", toJson "direct constants in the full expected telescope; not a transitive proof or receipt audit"),
    ("goal_declaration", toJson (obligation.goal.map Name.toString)),
    ("goal_module", toJson goalModule), ("stub_text", toJson obligation.stubText),
    ("status", toJson status), ("method", toJson method), ("reason", toJson reason),
    ("default_attempts", toJson attempts), ("stub", toJson obligation.stub)]

inductive StubKind where
  | proof
  | value
  deriving BEq

/-- `goal` names a generated goal/type declaration, including its whole generic
telescope. No pretty-printed local expression is promoted into a declaration. -/
structure Stub where
  identity : String
  declaration : Name
  goal : Name
  kind : StubKind
  deriving BEq

def Stub.marker (stub : Stub) : String := "-- zkc companion " ++ reprStr stub.identity

private def plainName : Name → Bool
  | .anonymous => false
  | .num _ _ => false
  | .str parent part =>
      (parent.isAnonymous || plainName parent) && !part.isEmpty &&
      part.toList.all (fun character => character.isAlphanum || character == '_' || character == '\'') &&
      !(part.toList.head?.getD '0').isDigit

private def identifier : Name → String
  | .anonymous => ""
  | .num _ _ => ""
  | .str parent part =>
      (if parent.isAnonymous then "" else identifier parent ++ ".") ++ "«" ++ part ++ "»"

/-- Names are generator-owned ordinary Lean identifiers. Identity strings use
Lean's escaping and can contain qualification separators and source labels. -/
def Stub.render (stub : Stub) : Except String String := do
  unless !stub.identity.isEmpty && plainName stub.declaration && plainName stub.goal do
    throw "invalid companion stub identity or generated declaration name"
  let annotation := "@[zkc " ++ reprStr stub.identity ++ "]"
  let declaration := identifier stub.declaration
  let goal := identifier stub.goal
  let body := match stub.kind with
    | .proof => "proof_wanted " ++ declaration ++ " : " ++ goal ++ "\n" ++
        "attribute [zkc " ++ reprStr stub.identity ++ "] " ++ declaration ++ "\n"
    | .value => "-- " ++ annotation ++ "\n-- noncomputable def " ++ declaration ++ " : " ++ goal ++ " := by\n" ++
        "--   Provide the mathematical contract value here.\n"
  return stub.marker ++ "\n" ++ body

/-- Append only unseen source identities. Old text, including user proofs and
stale stubs, is preserved byte-for-byte; their current types are checked later
by companion lookup. Markers only suppress duplicate scaffolding. -/
def appendStubs (existing : String) (stubs : Array Stub) : Except String String := do
  let mut seen : Array Stub := #[]
  let mut result := existing
  for stub in stubs do
    if let some prior := seen.find? (·.identity == stub.identity) then
      unless prior == stub do throw "conflicting companion stub for the same identity"
      continue
    if seen.any (fun prior => prior.declaration == stub.declaration) then
      throw "duplicate generated companion declaration name"
    seen := seen.push stub
    let rendered ← stub.render
    if (existing.splitOn "\n").contains stub.marker then continue
    result := result ++ (if result.isEmpty || result.endsWith "\n" then "" else "\n") ++ "\n" ++ rendered
  return result

end ZkcTools.Companions
