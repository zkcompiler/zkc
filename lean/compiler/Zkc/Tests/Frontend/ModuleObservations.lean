import Zkc.Frontend.Driver.Session
import Zkc.Frontend.Written.Package
import Zkc.Tests.Frontend.SyntaxHarness

namespace Zkc.Tests.Frontend

open Zkc.Frontend

private def compileObservations (body : String) (phase : String := "packages") : Driver.Session :=
  let file := "observations.zkc"
  let source := Syntax.parseString file ("module observations\n" ++ body)
  Id.run <| Driver.Session.start.compile #[⟨file, source⟩] (fun _ => pure none) phase

private def defaultsOf (s : Compile.State) (name : String) : Array Nat :=
  s.results.defaults.filterMap fun report =>
    if s.program.nameOf report.declaration == name then some report.count else none

private def checkDetachedDeclarations : TestM Unit := do
  let relation := "module M<n: nat>:
    pub relation Accept(x: bool): if n == 0 then (x,x) else x
relation Holds(x: bool): x
protocol Check roles(P,V)(x: bool @(P,V)):
    guard @V x
spec for Check:
    proves @V "
  for (clause, used) in [("M<4>::Accept(x)", true), ("Holds(x)", false)] do
    let session := compileObservations (relation ++ clause ++ "\n")
    expectTrue (session.state.log.hasErrors != used &&
        (defaultsOf session.state "Accept").isEmpty == used)
      s!"detached clause {clause}: {session.renderDiagnostics}, defaults {defaultsOf session.state "Accept"}"

  let proof := "module Widths<n: nat>:
    pub nat Width = n
protocol Child<spec e: nat> roles(P)(x: bool @P):
    guard @P x
protocol Parent roles(P)(x: bool @P):
    Child<spec e = "
  for (argument, used) in [("Widths<4>::Width", true), ("4", false)] do
    let session := compileObservations (proof ++ argument ++ ">(x)\n")
    expectTrue (!session.state.log.hasErrors && (defaultsOf session.state "Width").isEmpty == used)
      s!"proof argument {argument}: {session.renderDiagnostics}, defaults {defaultsOf session.state "Width"}"

/-- Type the same contract at each of its two environments before default selection.
Only the concrete typing reaches the public relation for that purpose. -/
private def checkOpaqueClause : TestM Unit := do
  let source := "interface Carrier:
    type T
module B: Carrier:
    type T = bool
pub relation Verify<T, n: nat>(x: bool): x
module Widths<n: nat>:
    pub nat Width = n
protocol Child<spec e: nat> roles(P,V)(x: bool @(P,V)):
    guard @V x
protocol Check<X: Carrier> roles(P,V)(x: bool @(P,V)):
    Child<spec e = Widths<4>::Width>(x)
spec for Check:
    proves @V Verify<X::T,4>(x)
// instantiate: Check<B>
"
  let session := compileObservations source "instances"
  let s := session.state
  let some inst := s.table.requestedIds.find? (fun id =>
      s.program.nameOf (s.table.allocatedKey! id).declaration == "Check")
    | failure s!"missing generic protocol: {session.renderDiagnostics}"
  let key := s.table.allocatedKey! inst
  let some lowered := s.env.modules.lowered? key.declaration | failure "missing lowered protocol"
  let .protocol head statements returned := lowered.content | failure "expected a protocol"
  for hypothetical in [true, false] do
    let action : CompileM Unit := do
      let decl ← Static.declaration key.declaration
      let args ← if hypothetical then Prod.fst <$> Emit.opaqueValues decl key.arguments
        else pure key.arguments
      let env := Static.instanceEnv s.program decl args
      discard <| Emit.elaborateProtocol inst "Check" "Check" env head statements returned[0]?
        lowered.locals Typing.typeBody {} («opaque» := hypothetical)
      if hypothetical then
        discard <| Emit.opaqueClauseTypings inst args #[] Typing.typeBody
      else
        Emit.typeClauses inst #[] Typing.typeBody
      Instances.defaultProgram
    let (outcome, after) := action.run (Typing.withProtocolBodies session.context) s
    for name in ["Verify", "Width"] do
      let defaults := defaultsOf after name
      expectTrue ((outcome matches .ok ()) && !after.log.hasErrors && defaults.isEmpty != hypothetical)
        s!"{name} defaults after the {if hypothetical then "opaque" else "concrete"} typing: {defaults}"

private def checkApplicableLaws : TestM Unit := do
  let declarations := "interface Laws<k: nat>:
    law guaranteed(x: bool) where (k == 1): x == x
pub module M<n: nat>: Laws<n>:
    law own(x: bool) where (n == 1): x == x
    pub def helper(x: bool) -> bool: x
def run(x: bool) -> bool: "
  for (use, expected) in [("M<1>::helper(x)", 2), ("M<2>::helper(x)", 0), ("x", 2)] do
    let session := compileObservations (declarations ++ use ++ "\n")
    let rows := session.state.results.obligations
    let applicable := rows.map (·.law)
    expectTrue (!session.state.log.hasErrors && rows.size == expected &&
        (expected == 0 || (applicable.contains "guaranteed<k = 1>" && applicable.contains "own<n = 1>")))
      s!"{use}: expected {expected} applicable laws, got {applicable}; {session.renderDiagnostics}"

/-- Every contract closes its relation in a separate scratch table. The two Box types print
alike and the interface law has no static arguments of its own to distinguish its owners. -/
private def observationLaws := "interface Laws:
    law same(x: bool): x == x
module Left:
    pub struct Box<n: nat>:
        flag: bool
module Right:
    pub struct Box<n: nat>:
        flag: bool
module M<T>: Laws:
    law own(x: bool): x == x
    pub relation Accept(x: bool): x
"

private def useBox (root argument : String) : String :=
  s!"protocol {root} roles(P,V)(x: bool @(P,V)):\n    guard @V x\nspec for {root}:\n    proves @V M<{argument}>::Accept(x)\n"

private def checkLawPublication : TestM Unit := do
  let arguments := ["Left::Box<1>", "Right::Box<1>", "Left::Box<2>"]
  let calls := (useBox "A" arguments[0]!) ++ (useBox "B" arguments[1]!) ++
    (useBox "C" arguments[2]!) ++ (useBox "Again" arguments[0]!)
  let source := observationLaws ++ calls
  let explicit := compileObservations (source ++ String.join
    (arguments.map fun arg => s!"// instantiate: M<{arg}>\n")) "types"
  let selected := compileObservations source "types"
  for (path, session) in [("explicit", explicit), ("selected", selected)] do
    let rows := session.state.results.obligations
    expectTrue (!session.state.log.hasErrors && rows.size == 6 &&
        (rows.filter (·.law == "same")).size == 3 && rows.all (·.place.file == "observations.zkc"))
      s!"{path}: expected three interface laws and three module laws, got {rows.map (·.law)}; {session.renderDiagnostics}"
  let direct := explicit.state.results.obligationKeys
  let privateKeys := selected.state.results.obligationKeys
  expectTrue (direct.size == 6 && direct == privateKeys)
    "the two request paths must identify the same six distinct law instances"
  expectTrue (!(selected.state.table.requestedIds.any fun id =>
      selected.state.program.nameOf (selected.state.table.allocatedKey! id).declaration == "same"))
    "private validation published a law signature"

/-- An isolated check can be replayed after another check reused all its scratch numbers.
Replaying the original publication or typing the same law at shifted numbers adds no row. -/
private def checkReplayedLaws : TestM Unit := do
  let check (name : String) (pad : Bool) :=
    let padding := if pad then "// instantiate: Left::Box<19>\n" else ""
    compileObservations (observationLaws ++ padding ++ s!"// instantiate: M<{name}::Box<1>>\n") "types"
  let left := check "Left" false
  let right := check "Right" false
  let shifted := check "Left" true
  let saved := (compileObservations observationLaws "names").state
  let publish : CompileM Unit := do
    for session in [left, right, left, shifted] do
      Static.publishValidationObligations saved session.state
  let (outcome, final) := publish.run {vocabulary} saved
  expectTrue ([left, right, shifted].all (fun s =>
      !s.state.log.hasErrors && s.state.results.obligations.size == 2) &&
      (outcome matches .ok ()) && final.results.obligations.size == 4 &&
      final.table.allocatedCount == saved.table.allocatedCount)
    s!"replaying independently numbered checks published {final.results.obligations.size} laws"

/-- Using a public function only through a required member suppresses its public defaults
while preserving the serialized packages of independently defaulted functions. -/
private def checkPrivateDefaultNumbers : TestM Unit := do
  let source := "pub def first<n: nat>(x: bool) -> bool: x
interface A:
    def sibling(x: bool) -> bool
module M<n: nat>: A:
    def sibling(x): BODY
    pub def helper(x: bool) -> bool: x
pub def evaluate(x: bool) -> bool: M<1>::helper(x)
pub def later<n: nat>(x: bool) -> bool: x
"
  let unused := compileObservations (source.replace "BODY" "x")
  let used := compileObservations (source.replace "BODY" "first<n>(x)")
  let later (s : Driver.Session) : Array (String × String) := (s.admitRoots none).held.filterMap fun (name, p) =>
    if name.startsWith "default instance `later<" then some (name, (Written.package p.toSourcePackage).text)
    else none
  let unusedPackages := later unused
  let usedPackages := later used
  expectTrue ((unused.admitRoots none).complete.isOk && (used.admitRoots none).complete.isOk &&
    defaultsOf unused.state "first" == #[4] && (defaultsOf used.state "first").isEmpty &&
    usedPackages.size == 4 && unusedPackages == usedPackages)
    "a function reached only in a checked member changed the packages of later default roots"

def moduleObservationsSuite : TestM Unit := do
  checkDetachedDeclarations
  checkPrivateDefaultNumbers
  checkOpaqueClause
  checkApplicableLaws
  checkLawPublication
  checkReplayedLaws

end Zkc.Tests.Frontend
