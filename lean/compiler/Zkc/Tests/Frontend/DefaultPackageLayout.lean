import Zkc.Frontend.Driver.Session
import Zkc.Frontend.Written.Goals
import Zkc.Tests.Frontend.SyntaxHarness

namespace Zkc.Tests.Frontend
open Zkc.Frontend

namespace DefaultPackageLayout

private def declarations := "module layout
use zkc::security::{soundness}
interface A:
    def f(x: bool) -> bool
struct Tag<n: nat>:
    flag: bool
def stamp<T>(x: bool) -> bool: x
def ghost<n: nat>(x: bool) -> bool: stamp<Tag<n>>(x)
def step<n: nat>(x: bool) -> bool: x
module M<n: nat>: A:
    def f(x): x
"

private def check (name target : String) := s!"protocol {name} roles(P,V)(x: bool @(P,V)):
    guard @V x
spec for {name}:
    proves @V {target}(x)
"

private def source (body helper target : String) := declarations ++
  s!"    pub relation Accepted(x: bool): {body}\n    pub def helper(x: bool) -> bool: {helper}\n" ++
  "relation Holds(x: bool): x\n" ++ check "Check" target

private def input (text : String) : SourceInput :=
  ⟨"layout.zkc", Syntax.parseString "layout.zkc" text⟩

private def compile (text : String) (options : Options := {}) (phase := "packages") :=
  Id.run <| (Driver.Session.start vocabulary options).compile #[input text] (fun _ => pure none) phase

private def packages (s : Driver.Session) (prefix_ := "default instance `helper") :=
  s.admitRoots.held.filterMap fun (name, pkg) =>
    if name.startsWith prefix_ then some (name, (Written.package pkg.toSourcePackage).text) else none

private def requested (s : Driver.Session) := s.state.table.requestedIds.map fun id =>
  s.state.program.nameOf (s.state.table.allocatedKey! id).declaration

private def layoutCases : TestM Unit := do
  for (body, helper, shared) in [
      ("ghost<n>(x)", "step<n>(x)", false),
      ("if n != 1 then ghost<n>(x) else x", "step<n>(x)", false),
      ("if n != n then ghost<n>(x) else x", "step<n>(x)", false),
      ("ghost<n>(x)", "step<n>(ghost<n>(x))", true)] do
    let control := compile (source body helper "Holds")
    let hidden := compile (source body helper "M<1>::Accepted")
    let names := requested hidden
    expectTrue (hidden.admitRoots.complete.isOk && control.admitRoots.complete.isOk &&
      (packages control).size == 4 && packages hidden == packages control &&
      !names.contains "Accepted" && names.contains "ghost" == shared &&
      names.contains "Tag" == shared && hidden.state.defaults.map (·.count) == #[4] &&
      hidden.state.results.obligations.isEmpty && hidden.state.reports.isEmpty)
      s!"default body {body}, ordinary use {helper}: {names}, {hidden.renderDiagnostics}"

  -- An ordinary body between two suppressed schedules requests its callees before the second
  -- schedule's callees. A final ordinary body also uses one of the second schedule's keys.
  let alternating (hidden : Bool) := (source "ghost<n>(x)" "step<n>(x)"
      (if hidden then "M<1>::Accepted" else "Holds")).replace "relation Holds" (
      "    pub relation Second(x: bool): ghost<n + 4>(x)\n" ++
      "    pub def last(x: bool) -> bool: ghost<n + 4>(step<n + 4>(x))\nrelation Holds") ++
    check "Other" (if hidden then "M<2>::Second" else "Holds")
  let control := compile (alternating false)
  let hidden := compile (alternating true)
  for name in ["default instance `helper", "default instance `last"] do
    expectTrue (control.admitRoots.complete.isOk && hidden.admitRoots.complete.isOk &&
      (packages control name).size == 4 && packages hidden name == packages control name)
      s!"alternating default bodies changed {name}: {hidden.renderDiagnostics}"

private def isolation : TestM Unit := do
  let raw := source "if n == 1 then x else ghost<n>(x)" "step<n>(x)" "M<1>::Accepted"
  let law := raw.replace "struct Tag" ("interface L:\n    law stable(x: bool): x == x\n" ++
    "module Extra<k: nat>: L:\n    nat Size = k\n" ++
    "def useIt<H: L>(x: bool) -> bool: x\nstruct Tag")
  let law := law.replace "stamp<Tag<n>>(x)" "useIt<Extra<n>>(x)"
  let hidden := compile law
  let ordinary := compile (law.replace "M<1>::Accepted(x)" "Holds(x)")
  expectTrue (hidden.admitRoots.complete.isOk && ordinary.state.results.obligations.size > 0 &&
    hidden.state.results.obligations.isEmpty && !(requested hidden).contains "Extra" &&
    (packages hidden).size == 4 && packages hidden == packages ordinary)
    s!"private module or law escaped: {hidden.renderDiagnostics}, {ordinary.renderDiagnostics}"

  let more := raw.replace "pub relation Accepted(" "pub relation Accepted<k: nat>("
  let more := more.replace "M<1>::Accepted(x)" "M<1>::Accepted<1>(x)"
  let options : Options := {budgets.defaultInstances := 4}
  let ordinary := compile (more.replace "M<1>::Accepted<1>(x)" "Holds(x)") options
  let hidden := compile more options
  expectTrue (ordinary.hasIncomplete && !hidden.hasIncomplete && hidden.admitRoots.complete.isOk &&
    hidden.state.defaults.map (·.count) == #[4] && (packages hidden).size == 4 &&
    packages hidden == packages ordinary)
    s!"a private default budget changed the public session: {hidden.renderDiagnostics}"

  let single := raw.replace "pub def helper" "def helper"
  for text in ["module layout\n", "module layout\ndef plain(x: bool) -> bool: x\n", single] do
    let s := compile text {} "defaults"
    expectTrue (s.state.defaultBodyBatches.isEmpty && !(requested s).contains "ghost")
      s!"unnecessary suspended body schedule: {s.renderDiagnostics}"

private def namedOwnership : TestM Unit := do
  let ordinary := source "if n == 1 then x else (x,x)" "step<n>(x)" "M<1>::Accepted"
  let scheme (name target goal : String) := s!"scheme {name} = {target}:
    prover P
    construction interactive
goal {goal} = soundness({name})
"
  let single := ordinary ++ scheme "Checked" "Check" "good"
  let both := single ++ check "Other" "M<2>::Accepted" ++ scheme "Rejected" "Other" "bad"
  let issue (text : String) names := Written.issueSoundnessGoals
    (Id.run <| assemble #[input text] fun _ => pure none) names
  let #[base] := issue both ["good"] | failure "expected the selected control goal"
  let #[bad, good] := issue both ["bad", "good"] | failure "expected two goal decisions"
  let .ok ref := base.outcome | failure "the control goal failed"
  let .ok issued := good.outcome | failure "the valid goal inherited the sibling's failure"
  let .error why := bad.outcome | failure "the invalid relation was accepted by its own goal"
  expectTrue (why.contains "TY5" && ref.publication.statements == issued.publication.statements &&
    ref.publication.challenge == issued.publication.challenge)
    s!"named goals lost the selected relation's outcome or bytes: {why}"

end DefaultPackageLayout

def defaultPackageLayoutSuite : TestM Unit := do
  DefaultPackageLayout.layoutCases
  DefaultPackageLayout.isolation
  DefaultPackageLayout.namedOwnership

end Zkc.Tests.Frontend
