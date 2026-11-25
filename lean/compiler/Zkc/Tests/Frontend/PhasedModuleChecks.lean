import Zkc.Frontend.Driver.Checks
import Zkc.Tests.Frontend.SyntaxHarness

namespace Zkc.Tests.Frontend
open Zkc.Frontend

private def owner (name : String) := s!"module {name}<n: nat>: I:
    pub def helper(x: bool) -> bool: x
    def f(x): if n == 0 then x else {name}<n = n - 1>::helper(x)
"

private def longOnly := "module graph
interface I:
    def f(x: bool) -> bool
" ++ owner "M" ++ "def deep(x: bool) -> bool: M<6>::helper(x)
def healthy(x: bool) -> bool: x
"

private def shortcut := longOnly ++ "pub def extra<n: nat>(x: bool) -> bool: M<2>::helper(x)\n"

private def allHeld := #["deep", "healthy"] ++
  (Array.range 4).map fun n => s!"default instance `extra<{n}>`"

private def limited : Options := {budgets.instantiationDepth := 4, budgets.staticEvaluation := 256}

private def compile (source : String) (lastPhase : String) (options := limited) : Driver.Session :=
  let input := (⟨"graph", Syntax.parseString "graph" source⟩ : SourceInput)
  Id.run <| (Driver.Session.start vocabulary options).compile #[input] (fun _ => pure none) lastPhase

private def budgets (s : Driver.Session) (phases : Array String) : Array Budget :=
  (s.incompleteOf phases).filterMap fun d => d.exhaustion.map (·.budget)

private def checkRanges (s : Driver.Session) : TestM Unit := do
  let mut offset := 0
  for report in s.reports do
    unless report.firstDiagnostic == offset && report.interrupted.isNone do
      return ← failure s!"{report.name} starts at {report.firstDiagnostic}, expected {offset}, interrupt {report.interrupted}"
    offset := offset + report.diagnostics
  expectTrue (offset == s.state.log.entries.size) "phase ranges do not cover the display log"

private def checkComplete (s : Driver.Session) : TestM Unit := do
  let result := s.admitRoots
  expectTrue (result.complete.isOk && result.held.map (·.1) == allHeld &&
      s.state.rootModuleFailures.isEmpty && s.state.log.incomplete == 0 &&
      (TypingCheck.mk s).incomplete.isEmpty && s.diagnostics.isEmpty)
    s!"held {result.held.map (·.1)}, lacking {result.lackingLines}, diagnostics {s.renderDiagnostics}"
  checkRanges s

/-- A separate producer at exactly the same SP7 display key is counted on each occurrence.
Once the preliminary owner check is superseded, the surviving diagnostic and its phase own
that slot, with their original budget and message. -/
private def checkSameSite (early : Driver.Session) : TestM Unit := do
  let some first := (early.incompleteOf #["types"])[0]? | failure "missing owner cutoff"
  let phase : Driver.Phase := {
    name := "other check", reads := #[], writes := #[]
    run := do
      for _ in [:2] do
        discard <| logExhaustion .defaultInstances ⟨.ofText "another request", first.span⟩ }
  let pending := early.run phase
  expectTrue (pending.state.log.incomplete == 3 && (pending.incompleteOf #[phase.name]).isEmpty)
    "early duplicate should be counted and displayed once at types"
  let final := Id.run <| pending.runAllTimed (pure 0) #[Driver.defaults, Driver.defaultBodies, Driver.packages]
  expectTrue (final.admitRoots.held.map (·.1) == allHeld && !final.admitRoots.complete.isOk &&
      final.state.log.incomplete == 2 && (final.incompleteOf #["types", "default bodies"]).isEmpty &&
      budgets final #[phase.name] == #[.defaultInstances] &&
      final.state.log.entries[0]?.any (·.message.render Renderer.plain |>.contains "another request"))
    s!"same-site occurrence or phase ownership lost: {final.renderDiagnostics}"
  checkRanges final

/-- Two owners can run out at the same written selection. The later check keeps exactly
the still-unchecked instance and its caller chain, even if the earlier display key was shared. -/
private def checkSharedSelection : TestM Unit := do
  let source := shortcut ++ "def stuck(x: bool) -> bool: M<12>::helper(x)\n"
  let early := compile source "types"
  expectTrue (early.state.log.incomplete == 2 && (early.incompleteOf #["types"]).size == 1)
    "two depth boundaries at one selection must count twice"
  let later := early.runAll #[Driver.defaults, Driver.defaultBodies, Driver.packages]
  let ds := later.incompleteOf #["default bodies"]
  expectTrue (later.state.log.incomplete == 1 && (later.incompleteOf #["types"]).isEmpty &&
      ds.size == 1 && ds[0]!.chain.back?.any (·.subject.renderWith Renderer.plain false == "stuck") &&
      later.admitRoots.held.map (·.1) == allHeld &&
      later.admitRoots.lacking.map (·.1) == #["stuck"])
    s!"the persistent cutoff must name its own caller: {later.renderDiagnostics}"

/-- Static evaluation of two distinct closed terms exhausts in the same required member.
The settled owner failures keep both occurrences, their single display entry and its phase. -/
private def checkStaticCutoff : TestM Unit := do
  let source := shortcut ++ "module Slow<n: nat>: I:
    pub def helper(x: bool) -> bool: x
    def f(x): if (n + 1) ^ 513 == 1 then x else false
def slowOne(x: bool) -> bool: Slow<1>::helper(x)
def slowTwo(x: bool) -> bool: Slow<2>::helper(x)
"
  let s := compile source "packages"
  expectTrue (s.state.log.incomplete == 2 && budgets s #["types"] == #[.staticEvaluation] &&
      (s.incompleteOf #["default bodies"]).isEmpty && s.admitRoots.held.map (·.1) == allHeld &&
      s.admitRoots.lacking.map (·.1) == #["slowOne", "slowTwo"] && !s.admitRoots.complete.isOk)
    s!"shared static exhaustion: {s.renderDiagnostics}"

def phasedModuleChecksSuite : TestM Unit := do
  let early := compile shortcut "types"
  let lacks := (early.admitRoots (some #["deep"])).lacking
  expectTrue (early.state.log.incomplete == 1 && budgets early #["types"] == #[.instantiationDepth] &&
      lacks.any (fun (_, l) => l matches .exhausted _) && early.state.rootModuleFailures.size == 1)
    s!"types lost its genuine cutoff: {early.renderDiagnostics}"
  let selected := early.run Driver.defaults
  expectTrue (selected.hasIncomplete && (InstanceCheck.mk selected).incomplete.isEmpty)
    "defaults should preserve the pending cutoff and select only its own diagnostics"
  let final := checkTyping ⟨selected⟩
  checkComplete final.session
  checkComplete (compile shortcut "packages")
  checkComplete (checkTyping (checkInstances ⟨compile shortcut "names"⟩)).session
  checkComplete (Id.run (early.runAllTimed (pure 0) #[Driver.defaults, Driver.defaultBodies, Driver.packages]))
  checkSameSite early
  checkSharedSelection
  checkStaticCutoff
  -- Raw phase users consume the same effective state, without constructing a Session report.
  let (phase, retried) := Driver.defaultBodies.runIn selected.context selected.state
  let (_, packaged) := Driver.packages.runIn selected.context retried
  expectTrue (phase.interrupted.isNone && phase.firstDiagnostic == 0 && phase.diagnostics == 0 &&
      !packaged.log.hasIncomplete && packaged.rootModuleFailures.isEmpty &&
      packaged.results.packageReports.all (fun report => report.outcome matches .admitted _) &&
      packaged.results.packageReports.size == 6) "raw phase retry did not settle all six packages"

  let stillDeep := compile longOnly "packages"
  expectTrue (stillDeep.admitRoots.held.map (·.1) == #["healthy"] &&
      !stillDeep.admitRoots.complete.isOk && stillDeep.state.log.incomplete == 2 &&
      budgets stillDeep #["types"] == #[.instantiationDepth] &&
      budgets stillDeep #["default bodies"] == #[])
    s!"unchanged root set lost a real cutoff: {stillDeep.renderDiagnostics}"
  let other := compile (shortcut ++ owner "N" ++ "def stuck(x: bool) -> bool: N<6>::helper(x)\n") "packages"
  expectTrue (other.admitRoots.held.map (·.1) == allHeld &&
      other.admitRoots.lacking.any (fun (n,l) => n == "stuck" && (l matches .exhausted _)) &&
      other.state.log.incomplete == 1 && budgets other #["default bodies"] == #[.instantiationDepth])
    s!"independent module exhaustion: {other.renderDiagnostics}"
  let capped := compile shortcut "packages" {limited with budgets.defaultInstances := 2}
  expectTrue (capped.admitRoots.held.map (·.1) == allHeld.extract 0 4 && !capped.admitRoots.complete.isOk &&
      capped.state.log.incomplete == 1 && budgets capped #["defaults"] == #[.defaultInstances] &&
      budgets capped #["types", "default bodies"] == #[])
    s!"default formation limit: {capped.renderDiagnostics}"
  checkRanges capped

  let bad := compile (shortcut ++ "def bad(x: bool) -> bool: (x,x)\n") "packages"
  expectTrue (bad.admitRoots.held.map (·.1) == allHeld && bad.hasErrors && !bad.hasIncomplete &&
      !bad.admitRoots.complete.isOk && (bad.refusalsOf #["types"]).map (·.rule) == #["TY5"])
    s!"independent refusal: {bad.renderDiagnostics}"
  let revealed := compile (shortcut.replace "then x else M" "then (x,x) else M") "packages"
  expectTrue (revealed.admitRoots.held.map (·.1) == #["healthy"] && !revealed.hasIncomplete &&
      revealed.state.rootModuleFailures.size == 5 && (revealed.refusalsOf #["types"]).isEmpty &&
      (revealed.refusalsOf #["default bodies"]).map (·.rule) == #["TY5"])
    s!"a newly reached refusal belongs to the retry: {revealed.renderDiagnostics}"
  let stopped := compile (shortcut ++ "def bad(x: bool) -> bool: (x,x)\n") "packages"
    {limited with stopAtErrors := true}
  expectTrue (stopped.hasErrors && !stopped.ran "defaults" &&
      budgets stopped #["types"] == #[.instantiationDepth]) "stopped before retry lost the original cutoff"
  let wait := compile (shortcut ++ "protocol Retried roles(P, V)(a: bool @P) -> got: bool @V:
    k @P <- attempt
    m <- send a to V
    return m
") "packages"
  expectTrue (wait.admitRoots.held.map (·.1) == allHeld && !wait.hasIncomplete && !wait.hasErrors &&
      !wait.admitRoots.complete.isOk && (wait.admitRoots (some #["deep"])).complete.isOk &&
      wait.admitRoots.lacking.any (fun (n,l) => n == "Retried" && (l matches .waiting _)))
    s!"independent wait: {wait.admitRoots.lackingLines}"
  let body := compile (shortcut ++
    "def forever<n: nat>(x: bool) -> bool: forever<n = n + 1>(x)\ndef stuck(x: bool) -> bool: forever<0>(x)\n")
    "packages"
  expectTrue (body.admitRoots.held.map (·.1) == allHeld && body.state.log.incomplete == 1 &&
      budgets body #["types"] == #[.instantiationDepth] && budgets body #["default bodies"] == #[])
    s!"ordinary body depth check: {body.renderDiagnostics}"
  checkRanges body

end Zkc.Tests.Frontend
