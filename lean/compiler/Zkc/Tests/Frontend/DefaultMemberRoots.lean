import Zkc.Frontend.Driver.Session
import Zkc.Frontend.Written.Package
import Zkc.Tests.Frontend.SyntaxHarness

namespace Zkc.Tests.Frontend
open Zkc.Frontend

private def compile (source : String) : Driver.Session :=
  let file := "default-members.zkc"
  let input := ⟨file, Syntax.parseString file ("module roots\n" ++ source)⟩
  Id.run <| Driver.Session.start.compile #[input] fun _ => pure none

private def method := "interface A:\n    def f(x: bool) -> bool\n"

private def helper := "    pub def helper(x: bool) -> bool: x\n"

private def healthy := "def healthy(x: bool) -> bool: x\n"

private def memberName (n : Nat) := s!"default instance `helper<{n}>`"

private def helperBytes (s : Driver.Session) : Array String :=
  s.admitRoots.held.filterMap fun (name, package) =>
    if name.contains "helper" then some (Written.package package.toSourcePackage).text else none

/-- Compiler-scheduled, directed and selected members all need the actual lexical receiver.
The sibling roots and specializations retain their individual outcomes. -/
def defaultMemberRootsSuite : TestM Unit := do
  for (parameters, extra, bad) in [
      ("<n: nat>", "", (Array.range 4).map memberName),
      ("<n: nat>", "// instantiate: M<1>::helper\n", #["helper<1>"]),
      ("<n: nat>", "def selected(x: bool) -> bool: M<1>::helper(x)\n", #["selected"]),
      ("", "", #["helper"])] do
    let s := compile (method ++ s!"module M{parameters}: A:\n" ++ helper ++ healthy ++ extra)
    let requested := s.admitRoots (some (bad.push "healthy"))
    expectTrue (requested.held.map Prod.fst == #["healthy"] &&
      requested.lacking.map Prod.fst == bad && s.admitRoots.held.map Prod.fst == #["healthy"] &&
      s.diagnostics.any (fun d => d.rule == "SP8" && d.span.startLine == 4))
      s!"wrong member packages {requested.lackingLines}: {s.renderDiagnostics}"

  let src := method ++ "module M<n: nat>: A:\n" ++
    "    def f(x): if n == 1 then (x, x) else x\n" ++ helper ++ healthy
  let s := compile src
  expectTrue (s.admitRoots.lacking.map Prod.fst == #[memberName 1] &&
    s.admitRoots.held.map Prod.fst == #["healthy", memberName 0, memberName 2, memberName 3] &&
    s.diagnostics.any (·.rule == "TY5"))
    s!"a failing specialization affected its siblings: {s.renderDiagnostics}"

  for (member, accepted) in [("x", true), ("(x, x)", false)] do
    let s := compile (method ++ "    law stable(x: bool): x == x\nmodule M<n: nat>: A:\n" ++
      s!"    def f(x): {member}\n    law own(x: bool): x == x\n" ++
      healthy ++ "// instantiate: M<1>\n")
    let names := #["default instance `stable at M<1>`", "default instance `own<1>`"]
    let laws := s.admitRoots (some names)
    expectTrue (laws.held.size == (if accepted then 2 else 0) &&
      laws.lacking.size == (if accepted then 0 else 2) &&
      (s.admitRoots (some #["healthy"])).held.size == 1)
      s!"scheduled laws failed to use their receiver: {laws.lackingLines}, {s.renderDiagnostics}"

  let single := "interface A<n: nat> where (n == 1):\n    def f(x: bool) -> bool\n" ++
    "module M<n: nat>: A<n>:\n    def f(x): x\n" ++ helper ++ healthy
  let s := compile single
  expectTrue (s.admitRoots.complete.isOk && s.admitRoots.held.map Prod.fst ==
    #["healthy", memberName 1] && s.state.defaults.map (·.count) == #[1])
    s!"ineligible receivers became member roots: {s.renderDiagnostics}"
  let demanded := compile (single ++ "// instantiate: M<0>\n")
  expectTrue (demanded.admitRoots.held.map Prod.fst == #["healthy", memberName 1] &&
    demanded.admitRoots.lacking.isEmpty && demanded.state.defaults.map (·.count) == #[1] &&
    demanded.diagnostics.any (·.rule == "SP4"))
    s!"a refused explicit request became a second default: {demanded.renderDiagnostics}"
  let inactive := compile (method ++ "module M<n: nat>: A where (n > 10):\n" ++ helper ++ healthy)
  expectTrue (inactive.admitRoots.complete.isOk && inactive.admitRoots.held.map Prod.fst ==
    #["healthy"] && inactive.state.defaults.map (·.count) == #[0])
    s!"a skipped member required its malformed receiver: {inactive.renderDiagnostics}"

  let hidden := compile (method ++ "module M<n: nat>: A:\n    def f(x): x\n" ++
    "    module Hidden<k: nat>: A:\n        nat K = k\n" ++ helper ++ healthy)
  expectTrue (hidden.admitRoots.complete.isOk && (helperBytes hidden).size == 4 &&
    hidden.state.defaults.map (·.count) == #[4])
    s!"an unused private nested module was required: {hidden.renderDiagnostics}"

  let source (body target : String) := method ++ "module M<n: nat>: A:\n    def f(x): x\n" ++
    "    pub relation Accepted(x: bool): " ++ body ++ "\n" ++ helper ++
    "relation Holds(x: bool): x\nprotocol Check roles(P,V)(x: bool @(P,V)):\n    guard @V x\n" ++
    "spec for Check:\n    proves @V " ++ target ++ "(x)\n"
  let scheduled := compile (source "x" "Holds")
  let expected := helperBytes scheduled
  expectTrue (scheduled.admitRoots.complete.isOk && expected.size == 4)
    s!"missing comparison roots: {scheduled.renderDiagnostics}"
  for body in ["x", "if n == 1 then x else (x, x)"] do
    let s := compile (source body "M<1>::Accepted")
    let names := s.state.defaults.map fun d => s.state.program.nameOf d.declaration
    let requests := s.state.table.requestedIds.map fun i =>
      s.state.program.nameOf (s.state.table.allocatedKey! i).declaration
    expectTrue (s.admitRoots.complete.isOk && helperBytes s == expected && names == #["helper"] &&
      !requests.contains "Accepted" && s.state.reports.isEmpty)
      s!"detached relation changed packages, requests or reports: {names}, {s.renderDiagnostics}"

end Zkc.Tests.Frontend
