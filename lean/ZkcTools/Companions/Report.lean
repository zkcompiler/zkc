module

public meta import ZkcTools.Companions.Assembly

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

structure Obligation where
  identity : String
  source : Option SourceSpan := none
  responsibility : String
  expected : Expr
  stub : Option StubLocation := none

/-- Detailed diagnostics are created on demand, independently of evidence
selection. The expected type is the input to assembly, not inferred from the
selected proof or an error message. -/
def report (obligation : Obligation) (result : Assembly) : MetaM Json := do
  let expected ← instantiateMVars obligation.expected
  let expected ← withOptions (fun options => options.setBool `pp.fullNames true) do
    return toString (← ppExpr expected)
  let (status, method, reason, attempts) := match result with
    | .discharged _ method attempts => ("discharged", some method, none, attempts)
    | .openObligation reason attempts => ("open", none, some reason, attempts)
    | .refused reason attempts => ("refused", none, some reason, attempts)
  return Json.mkObj [
    ("schema", toJson "zkc.companion-obligation/0"),
    ("status_scope", toJson "authoring only; receipt audit remains authoritative"),
    ("identity", toJson obligation.identity), ("source_span", toJson obligation.source),
    ("responsibility", toJson obligation.responsibility), ("expected_type", toJson expected),
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
