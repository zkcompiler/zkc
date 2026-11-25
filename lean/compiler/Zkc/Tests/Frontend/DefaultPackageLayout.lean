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

-- An Inputs view reads only the protocol signature. Its queued body calls Inner later.
-- A module requested by the ordinary helper then schedules a live law behind that body.
private def deferredProtocol : TestM Unit := do
  let raw := source "ghost<n>(x)" "step<n>(x)" "M<1>::Accepted"
  let text := (raw.replace "def ghost" ("protocol Inner<k: nat> roles(P,V)(x: bool @(P,V)):\n" ++
      "    guard @V stamp<Tag<k>>(x)\nprotocol Outer<k: nat> roles(P,V)(x: bool @(P,V)):\n" ++
      "    Inner<k>(x)\ndef ghost")).replace "bool: stamp<Tag<n>>(x)" "bool: stamp<Outer<n>::Inputs<P>>(x)"
  let text := text.replace "def step<n: nat>(x: bool) -> bool: x" (
    "interface Carrier\nmodule Live<k: nat>: Carrier:\n    nat Size = k\n" ++
    "    law visible(x: bool): finish<k>(x)\ndef finish<k: nat>(x: bool) -> bool: x\n" ++
    "def take<H: Carrier>(x: bool) -> bool: x\ndef step<n: nat>(x: bool) -> bool: take<Live<n>>(x)")
  let ordinary := compile (text.replace "M<1>::Accepted(x)" "Holds(x)")
  let hidden := compile text
  let laws := "default instance `visible"
  expectTrue (ordinary.admitRoots.complete.isOk && hidden.admitRoots.complete.isOk &&
    (packages ordinary laws).size == 4 && packages hidden laws == packages ordinary laws &&
    (requested ordinary).contains "Inner" && !(requested hidden).contains "Outer" &&
    !(requested hidden).contains "Inner" && hidden.state.results.obligations.size == 4)
    s!"deferred protocol requests changed a later law: {hidden.renderDiagnostics}"

-- Pick<n> is first materialized by an ordinary default after Hidden's private store
-- already exists. The excluded helper needs the contents of that exact nominal argument.
private def nominalInput : TestM Unit := do
  let text := "module nominal
interface Key<k: nat>:
    nat Width
module Pick<k: nat>: Key<k>:
    nat Width = k
def ghost<k: nat>(x: bool) -> bool: x
pub relation Hidden<k: nat>(x: bool): ghost<k>(x)
interface I<n: nat> where (n == 1):
    def f(x: bool) -> bool
module Cell<n: nat, H: Key<n>>: I<n>:
    def f(x): x
    pub def helper(x: bool) -> bool: step<H::Width>(x)
def step<k: nat>(x: bool) -> bool: x
def finish<k: nat>(x: bool) -> bool: x
pub def later<k: nat>(x: bool) -> bool: finish<k>(x)
relation Holds(x: bool): x
protocol Check roles(P,V)(x: bool @(P,V)):
    guard @V x
spec for Check:
    proves @V Hidden<4>(x)
"
  let ordinary := compile ((text.replace "n == 1" "n == n").replace "Hidden<4>(x)" "Holds(x)")
  let hidden := compile text
  let later := "default instance `later"
  let eligible := "default instance `helper<1,"
  expectTrue (ordinary.admitRoots.complete.isOk && hidden.admitRoots.complete.isOk &&
    (packages hidden later).size == 4 && packages hidden later == packages ordinary later &&
    (packages hidden).size == 1 && packages hidden eligible == packages ordinary eligible &&
    !(requested hidden).contains "Hidden")
    s!"nominal default argument lost its signature: {hidden.renderDiagnostics}"

/-- A public owner reached only through a member contributes its former default slots.
The callee of each independent tail keeps its published number as well. -/
private def publicOwner : TestM Unit := do
  let program := "module direct
interface Mark:
    def identity(x: bool) -> bool
def leaf<k: nat>(x: bool) -> bool: x
pub module Family<n: nat>: Mark:
    def identity(x): x
    pub def pick(x: bool) -> bool: x
def useOne(x: bool) -> bool: Family<1>::pick(x)
pub def tail<n: nat>(x: bool) -> bool: leaf<n>(x)
"
  let scheduled := compile program (phase := "defaults")
  let batches := scheduled.state.defaultLayout.batches.toArray
  expectTrue (batches.size == 1 && scheduled.state.defaultLayout.stores.size == 1 &&
      scheduled.state.defaultLayout.stores[0]!.instanceCount == 4)
    "a layout batch should retain only its four private requests"
  let s := compile program
  let tails := packages s "default instance `tail"
  expectTrue (s.admitRoots.complete.isOk && tails.size == 4 && !(requested s).contains "Family")
    s!"public owner defaults leaked into live requests: {s.renderDiagnostics}"
  for ((_, text), i) in tails.zipIdx do
    expectTrue (text.contains s!".fn ⟨{6 + i}⟩" && text.contains s!".fn ⟨{14 + i}⟩")
      s!"tail<{i}> lost its function or its callee's package key"

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
    expectTrue (s.state.defaultLayout.stores.isEmpty && !(requested s).contains "ghost")
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
  let #[base] := issue both ["good"] | failure "expected the control goal"
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
  DefaultPackageLayout.deferredProtocol
  DefaultPackageLayout.nominalInput
  DefaultPackageLayout.publicOwner
  DefaultPackageLayout.isolation
  DefaultPackageLayout.namedOwnership

end Zkc.Tests.Frontend
