import Zkc.Frontend.Driver.Session
import Zkc.Tests.Frontend.SyntaxHarness

namespace Zkc.Tests.Frontend
open Zkc.Frontend

private def compileGraph (text : String) (depth : Nat) (steps : Nat := 256) : Driver.Session :=
  let opts : Options := {
    budgets.instantiationDepth := depth, budgets.staticEvaluation := steps,
    traces := {"module.owner", "module.member"}}
  let src : SourceInput := ⟨"graph", Syntax.parseString "graph" text⟩
  Id.run ((Driver.Session.start vocabulary opts).compile #[src] fun _ => pure none)

private def header := "module graph
interface I:
    def f(x: bool) -> bool
"

private def owner (name member : String) :=
  s!"module {name}<n: nat>: I:
    pub def h(x: bool) -> bool: x
    def f(x): {member}
"

private def root (name body : String) := s!"def {name}(x: bool) -> bool: {body}\n"

private def healthy := root "healthy" "x"

private def bridge := "def first<n: nat>(x: bool) -> bool: second<n = n>(x)
def second<n: nat>(x: bool) -> bool: Tail<n = n>::h(x)
"

private def tailBody := "if n == 0 then x else Tail<n = n - 1>::h(x)"

private def expectOutcome (s : Driver.Session) (held : Array String)
    (errors incomplete : Nat) : TestM Unit := do
  let packages := s.admitRoots none
  let actual := (packages.held.map (·.1)).qsort (· < ·)
  expectTrue (actual == held.qsort (· < ·) && s.state.log.errors == errors &&
    s.state.log.incomplete == incomplete && packages.complete.isOk == (errors == 0 && incomplete == 0))
    s!"expected {held}, {errors} errors, {incomplete} incomplete; held {actual}, log {s.state.log.errors}/{s.state.log.incomplete}: {s.renderDiagnostics}"

private def expectChain (s : Driver.Session) (rule : String) (middle : String)
    (roots : List String) : TestM Unit := do
  let chain := (s.diagnostics.find? (·.rule == rule)).map (·.chain) |>.getD #[]
  let labels := chain.map (·.subject.renderWith Renderer.plain false)
  expectTrue (labels.contains middle && labels.back?.any roots.contains &&
    chain.all (fun frame => frame.span.file == "graph" && frame.span.startLine > 0))
    s!"{rule} expected {middle} on a path from {roots}, got {s.renderDiagnostics}"

/-- Module-owner edges cost one depth level. Following the reads of a finished ordinary query
costs none. A shared local body may also acquire a completed query from a shorter caller. -/
def moduleDepthSuite : TestM Unit := do
  let base := header ++ owner "Tail" tailBody ++ owner "A" "Tail<n = n>::h(x)" ++ bridge
  let paths := base ++ owner "Long" "A<n = n>::h(x)" ++ owner "Short" "first<n = n>(x)"
  let far := root "far" "Long<4>::h(x)"
  let near := root "near" "Short<4>::h(x)"
  for roots in [far ++ near, near ++ far] do
    expectOutcome (compileGraph (paths ++ roots ++ healthy) 6) #["far", "near", "healthy"] 0 0
  let onlyFar := compileGraph (base ++ owner "Long" "A<n = n>::h(x)" ++ far ++ healthy) 6
  -- The ordinary roots and the default bodies each validate the same genuine depth cutoff.
  expectOutcome onlyFar #["healthy"] 0 2
  expectChain onlyFar "SP7" "Long<n = 4>" ["far"]
  for (left, right) in [("A<n = n>::h(x)", "first<n = n>(x)"), ("first<n = n>(x)", "A<n = n>::h(x)")] do
    let text := base ++ owner "Start" s!"if x then {left} else {right}" ++
      root "selected" "Start<6>::h(x)" ++ healthy
    expectOutcome (compileGraph text 8) #["selected", "healthy"] 0 0
    expectOutcome (compileGraph text 7) #["healthy"] 0 2

  let localBodies := header ++ owner "A" "first<n = n>(x)" ++ owner "B" "common<n = n>(x)" ++
    "def first<n: nat>(x: bool) -> bool: second<n = n>(x)
def second<n: nat>(x: bool) -> bool: common<n = n>(x)
def common<n: nat>(x: bool) -> bool: x
"
  let far := root "far" "A<1>::h(x)"
  let near := root "near" "B<1>::h(x)"
  for roots in [far ++ near, near ++ far] do
    expectOutcome (compileGraph (localBodies ++ roots ++ healthy) 4) #["far", "near", "healthy"] 0 0
    expectOutcome (compileGraph (localBodies ++ roots ++ healthy) 3) #["near", "healthy"] 0 2

  let shared := header ++ owner "Tail" (tailBody.replace "then x" "then (if (n + 1) ^ 41 == 1 then x else false)")
  let picks := (List.range 4).map fun i => s!"pick{i}"
  let text := shared ++ String.join (picks.map (root · "Tail<3>::h(x)")) ++ healthy
  for steps in [32, 256] do
    let session := compileGraph text 32 steps
    let held := if steps == 32 then #["healthy"] else picks.toArray.push "healthy"
    expectOutcome session held 0 (if steps == 32 then 1 else 0)
    for traceClass in ["module.owner", "module.member"] do
      let attempts := session.reports.map fun phase => phase.traces.countP (·.traceClass == traceClass)
      expectTrue (attempts.foldl (· + ·) 0 == 4) s!"expected four {traceClass} checks, got {attempts}"

  let sameSite := header ++ owner "M" "if (n + 1) ^ 41 == 1 then x else false" ++
    root "one" "M<1>::h(x)" ++ root "two" "M<2>::h(x)" ++ healthy
  let repeated := compileGraph sameSite 32 32
  expectOutcome repeated #["healthy"] 0 2
  expectTrue ((repeated.diagnostics.filter (·.rule == "TY2")).size == 1)
    "two distinct incomplete checks at one source site should display one diagnostic"

  -- The memo records the allowance that exhausted the closed term. A caller that resumes a
  -- saved environment with a larger budget can validate the same concrete owner.
  let limited := compileGraph text 32 32
  let raised := {limited.context with options.budgets.staticEvaluation := 256}
  let reads := limited.state.moduleReads
  let (retried, _) := (Typing.checkModuleReads reads).run (Typing.withProtocolBodies raised) limited.state
  expectTrue retried.isOk "a larger static allowance reused an earlier exhausted verdict"

  let cycle := header ++ owner "A" "B<n = n>::h(x)" ++
    owner "B" "if x then A<n = n>::h(x) else C<n = n>::h(x)" ++ owner "C" "(x,x)"
  let alpha := root "alpha" "A<1>::h(x)"
  let beta := root "beta" "B<1>::h(x)"
  for roots in [alpha ++ beta, beta ++ alpha] do
    let bad := compileGraph (cycle ++ roots ++ healthy) 32
    expectOutcome bad #["healthy"] 1 0
    expectChain bad "TY5" "B<n = 1>" ["alpha", "beta"]
    expectOutcome (compileGraph ((cycle.replace "(x,x)" "x") ++ roots ++ healthy) 32)
      #["alpha", "beta", "healthy"] 0 0

end Zkc.Tests.Frontend
