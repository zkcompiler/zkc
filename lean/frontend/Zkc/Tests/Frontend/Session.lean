import Zkc.Tests.Frontend.Harness
import Zkc.Tests.Frontend.Names
import Zkc.Tests.Frontend.Running

/-!
# The session and its stores

What a run records about itself, without the reference:

- The log shows a diagnostic once and counts every error it is given: an error repeated at its
  place still advances the count that "was anything refused since this point" reads, and an
  error is never hidden behind a warning of the same rule at the same place.
- A budget of the compiler that runs out is an incomplete check, never a refusal (SP10): a chain
  of instantiations that does not end stops at the budget of its depth with an incomplete
  diagnostic that names the budget, its value and the request, no error, and every request on
  the way exhausted, not failed; a later request for an exhausted entry finds it exhausted.
- A reference to a declaration that leaves the run names its file by the module path: the same
  two files given in either order give the same reference, and each run finds the declaration
  from it.
- Recovery takes only a refusal that was logged: a budget that runs out under the inference of a
  static argument leaves the root not checked, and is not taken for a refusal.
- What is run, proved, verified or written comes from a completed result only: an admitted result
  says which roots asked for it holds and which it lacks, with why; a root is complete when the
  session reported no error, left no check incomplete and holds it. A root that waits is lacking,
  not left out, and keeps no other root from being complete; an error anywhere in the program
  completes nothing; a root that the program does not have is lacking;
  and a root that emission did not make an entry of the package of the program is lacking from
  its admission.
-/

namespace Zkc.Tests.Frontend

open Zkc.Frontend
open Zkc.Frontend.Syntax

/-- What became of a package, in a word. -/
def reportOutcome : PackageOutcome → String
  | .admitted _ => "admitted"
  | .unjustified .. => "not justified"
  | .refused .. => "refused"
  | .waiting _ => "waiting"
  | .typedOnly _ => "typed only"
  | .defect _ => "a defect"
  | .exhausted _ => "not checked"

/-! ## The log -/

def logSuite : TestM Unit := do
  let span : Span := { file := "log", startLine := 1, startColumn := 5, startByte := 4
                       stopLine := 1, stopColumn := 9, stopByte := 8 }
  let refusal : Diagnostic := { rule := "SP4", span, message := .ofText "refused" }
  -- the same error twice: shown once, counted twice
  let once := ({} : Log).add refusal
  let twice := once.add refusal
  expectTrue (twice.entries.size == 1) s!"log: a repeated error is shown {twice.entries.size} times"
  expectTrue (twice.errors == 2) s!"log: two errors given are counted as {twice.errors}"
  expectTrue (twice.hasErrorsSince once.errors)
    "log: an error repeated at its place does not count as an error since the first"
  -- a warning, then an error of the same rule at the same place: the error is shown and counted
  let warned := ({} : Log).add { refusal with severity := .warning }
  let refused := warned.add refusal
  expectTrue (!warned.hasErrors) "log: a warning counts as an error"
  expectTrue refused.hasErrors "log: an error after a warning at its place is not counted"
  expectTrue (refused.entries.any (·.isError)) "log: an error after a warning at its place is not shown"
  expectTrue (refused.hasErrorsSince warned.errors)
    "log: an error after a warning at its place does not count as an error since the warning"

/-! ## Budgets -/

/-- A chain of instantiations that does not end: `f<n>` calls `g<n + 1>`, which calls `f<n + 1>`. -/
def unboundedProgram : String := "module deep
def f<n: nat>(x: nat) -> nat:
    return g<n + 1>(x)
def g<n: nat>(x: nat) -> nat:
    return f<n>(x)
def main(x: nat) -> nat:
    return f<0>(x)
"

/-- Requests of the table of trees, each asking for the next key: a chain that does not end. -/
def chainQuery (step : Nat → InstanceId → CompileM Typed.Definition) :
    Query InstanceId Typed.Definition where
  kind := .tree
  table := (·.trees)
  setTable := fun results table => { results with trees := table }
  instanceOf := fun _ id => id
  compute := step

partial def chainStep (_ : Nat) (id : InstanceId) : CompileM Typed.Definition := do
  let (_, place) ← ask (chainQuery chainStep) (id + 1) { subject := .ofText s!"step {id + 1}", span := default }
  return place

def isExhausted {ρ : Type} : QueryState ρ → Bool
  | .exhausted _ => true
  | _ => false

def budgetSuite : TestM Unit := do
  -- a program whose chain of instantiations does not end, with a budget of depth 8
  let input : SourceInput := { name := "deep", parsed := parseString "deep" unboundedProgram }
  let session := Id.run <|
    (Driver.Session.start (options := { budgets := { instantiationDepth := 8 } })).compile #[input]
      (memoryLoader nameLibrary) "packages"
  let log := session.state.log
  expectTrue (!log.hasErrors)
    s!"budgets: running out of a budget refuses: {(session.refusalsOf #["names", "instances", "types", "defaults", "default bodies", "packages"]).map (·.render)}"
  let incomplete := session.incompleteOf #["instances", "types", "defaults", "default bodies", "packages"]
  expectTrue (incomplete.size == 1 && log.incomplete == 1)
    s!"budgets: {incomplete.size} incomplete checks are shown and {log.incomplete} counted, not one"
  match incomplete[0]?.bind (·.exhaustion) with
  | some exhaustion =>
    let request := exhaustion.request.subject.renderWith Renderer.plain false
    expectTrue (exhaustion.budget == .instantiationDepth && exhaustion.limit == 8)
      s!"budgets: the budget that ran out is {reprStr exhaustion.budget} at {exhaustion.limit}"
    expectTrue (request.startsWith "f<" || request.startsWith "g<")
      s!"budgets: the request that ran out is `{request}`"
  | none => failure "budgets: the incomplete check carries no budget"
  let results := session.state.results
  let failed := (results.signatures.entries.filter (·.state matches .failed)).size +
    (results.bodies.entries.filter (·.state matches .failed)).size
  expectTrue (failed == 0) s!"budgets: {failed} requests on the chain are failed, not exhausted"
  expectTrue (results.bodies.entries.any (isExhausted ·.state))
    "budgets: no body on the chain is exhausted"
  match results.packageReports.find? (·.description == "main") with
  | some { outcome := .exhausted _, .. } => pass
  | some report => failure s!"budgets: the package of main is {reportOutcome report.outcome}, not unchecked"
  | none => failure "budgets: main has no package report"
  -- the requests of a table: the chain stops at the budget, every request on it exhausted, and a
  -- later request for one of them finds it exhausted
  let context : Compile.Context :=
    { vocabulary := Zkc.Frontend.vocabulary, options := { budgets := { instantiationDepth := 4 } } }
  let first : ChainFrame := { subject := .ofText "step 0", span := default }
  let (outcome, state) := (request (chainQuery chainStep) 0 first).run context {}
  match outcome with
  | .ok (_, .exhausted exhaustion) =>
    expectTrue (exhaustion.limit == 4) s!"budgets: a request runs out at {exhaustion.limit}, not 4"
  | .ok _ => failure "budgets: a request deeper than its budget is not exhausted"
  | .error _ => failure "budgets: a request deeper than its budget is interrupted"
  let entries := state.env.results.trees.entries
  expectTrue (entries.size == 5 && entries.all (isExhausted ·.state))
    s!"budgets: of {entries.size} requests on the chain, not all five are exhausted"
  expectTrue (!state.log.hasErrors && state.log.incomplete == 1)
    s!"budgets: the requests log {state.log.errors} errors and {state.log.incomplete} incomplete checks"
  match (ask (chainQuery chainStep) 2 first).run context state with
  | (.error (.exhausted _), _) => pass
  | (.error .abandoned, _) => failure "budgets: an exhausted request is taken for a refused one"
  | _ => failure "budgets: an exhausted request is asked for again and not found exhausted"
  -- a static term whose evaluation costs more steps than its budget: not checked, not refused
  let input : SourceInput :=
    { name := "power", parsed := parseString "power" "module power\nnat N = 2 ^ 100\n" }
  let session := Id.run <|
    (Driver.Session.start (options := { budgets := { staticEvaluation := 50 } })).compile #[input]
      (memoryLoader nameLibrary) "instances"
  let log := session.state.log
  expectTrue (!log.hasErrors)
    s!"budgets: a static term past its budget refuses: {(session.refusalsOf #["names", "instances"]).map (·.render)}"
  let incomplete := session.incompleteOf #["instances"]
  expectTrue (incomplete.any fun diagnostic =>
      diagnostic.exhaustion.any fun exhaustion =>
        exhaustion.budget == .staticEvaluation && exhaustion.limit == 50)
    s!"budgets: no check is incomplete for the steps of a static term: {incomplete.map (·.message.render Renderer.plain)}"
  -- a declaration with more default instances than the budget: as many as it allows are formed,
  -- and the check of the declaration is incomplete
  let input : SourceInput :=
    { name := "defaults", parsed := parseString "defaults" "module defaults\npub def f<n: nat>(x: nat) -> nat: x + n\n" }
  let session := Id.run <|
    (Driver.Session.start (options := { budgets := { defaultInstances := 2 } })).compile #[input]
      (memoryLoader nameLibrary) "defaults"
  expectTrue (!session.state.log.hasErrors)
    s!"budgets: default instances past their budget refuse: {(session.refusalsOf #["names", "instances", "defaults"]).map (·.render)}"
  let incomplete := session.incompleteOf #["defaults"]
  expectTrue (incomplete.any fun diagnostic =>
      diagnostic.exhaustion.any fun exhaustion =>
        exhaustion.budget == .defaultInstances && exhaustion.limit == 2)
    s!"budgets: no check is incomplete for the default instances: {incomplete.map (·.message.render Renderer.plain)}"
  let formed := session.state.env.results.defaults.filter (·.count == 2)
  expectTrue (formed.size == 1)
    s!"budgets: the default instances formed within the budget are not two"

/-! ## References that leave the run -/

def referenceFiles : Array SourceInput :=
  #[("first", "module refs::first
pub def helper(x: nat) -> nat:
    return x
pub def other(x: nat) -> nat:
    return helper(x)
"), ("second", "module refs::second
use refs::first::{helper}
pub def twice(x: nat) -> nat:
    return helper(helper(x))
")].map fun (name, text) => { name, parsed := parseString name text }

/-- The references of a run to the declarations of a name, with what the run finds from each,
and the exports of the file of the first. -/
def referencesOf (inputs : Array SourceInput) (name : String) :
    Array (Option ModuleRef × Option String) × Option (Array (ModuleRef × String × ModuleRef)) :=
  let check := Id.run (checkNames inputs (memoryLoader nameLibrary))
  let store := check.session.state.env.modules
  let ids := (List.range store.program.declarations.size).filter (store.program.nameOf · == name)
  let references := ids.toArray.map fun id =>
    let reference := store.declarationRef? id
    (reference, (reference.bind store.declarationOf?).map store.program.nameOf)
  let exports := (ids.head?.bind store.owner?).bind fun owner => (store.interface? owner).map (·.exports)
  (references, exports)

def referenceSuite : TestM Unit := do
  let (inOrder, exportsInOrder) := referencesOf referenceFiles "helper"
  let (reversed, exportsReversed) := referencesOf referenceFiles.reverse "helper"
  expectTrue (inOrder.size == 1) s!"references: {inOrder.size} declarations named helper"
  expectTrue (inOrder.map (·.1) == reversed.map (·.1))
    s!"references: the reference of helper depends on the order of the files: {reprStr (inOrder.map (·.1))} and {reprStr (reversed.map (·.1))}"
  expectTrue ((inOrder ++ reversed).all (·.2 == some "helper"))
    "references: a run does not find helper from its reference"
  expectTrue ((inOrder.map (·.1)).all fun reference => reference.any (·.module == "refs::first"))
    "references: the reference of helper does not name the module refs::first"
  expectTrue (exportsInOrder.isSome && exportsInOrder == exportsReversed)
    "references: the exports of refs::first depend on the order of the files"

/-! ## Admitted and completed results -/

/-- A function, and a protocol that waits for `attempt`. -/
def admissionProgram (extra : String := "") : String := "module admitted
type F = primitive(\"bls12-381.fr\")
def double(x: F) -> F: x + x
protocol Retried roles(P, V)(a: F @P) -> got: F @V:
    k @P <- attempt
    m <- send a to V
    return m
" ++ extra

/-- A session of a program in memory, after the packages of its roots. -/
def admissionSession (text : String) : Driver.Session :=
  let input : SourceInput := { name := "admitted", parsed := parseString "admitted" text }
  Id.run ((Driver.Session.start).compile #[input] (memoryLoader nameLibrary) "packages")

def isWaiting : Lack → Bool
  | .waiting _ => true
  | _ => false

def admissionSuite : TestM Unit := do
  let session := admissionSession (admissionProgram)
  expectTrue (!session.hasErrors) s!"admission: the program is refused: {(session.refusalsOf #["names", "instances", "types"]).map (·.render)}"
  -- every root: the function held, the protocol lacking because it waits; not complete
  let every := session.admitRoots
  expectTrue (every.held.any (·.1 == "double")) "admission: the function is not held"
  expectTrue (every.lacking.any fun (root, lack) => root == "Retried" && isWaiting lack)
    s!"admission: the protocol that waits is not lacking as waiting: {every.lacking.map (·.1)}"
  expectTrue (every.complete matches .error _) "admission: a result that lacks a root is complete"
  -- each root on its own: the function is complete, the protocol that waits keeps it from nothing
  match every.completeRoots with
  | .ok (completed, lacking) =>
    expectTrue ((completed.find? "double").isSome) "admission: the function is not complete on its own"
    expectTrue (lacking.any fun (root, lack) => root == "Retried" && isWaiting lack)
      "admission: the protocol that waits is not listed with why"
  | .error missing => failure s!"admission: no root is complete on its own: {missing}"
  -- the function alone: complete, and it runs
  match (session.admitRoots (some #["double"])).complete with
  | .ok completed =>
    match completed.runFunction "double" [.number 3] with
    | .returned [.number 6] => pass
    | other => failure s!"admission: double of 3 does not return 6: {describeOutcome other}"
  | .error missing => failure s!"admission: the function alone is not complete: {missing}"
  -- the protocol alone: not complete, because it waits
  match (session.admitRoots (some #["Retried"])).complete with
  | .ok _ => failure "admission: a root that waits is complete"
  | .error missing =>
    expectTrue (missing.any fun line => (line.splitOn "waiting").length > 1)
      s!"admission: what is missing does not say that the protocol waits: {missing}"
  -- a root that the program does not have
  expectTrue ((session.admitRoots (some #["absent"])).lacking.any fun (_, lack) => lack matches .absent)
    "admission: a root that the program does not have is not lacking"
  -- an error anywhere: nothing completes, the function alone included
  let refused := admissionSession (admissionProgram "def wrong(x: F) -> bool: x\n")
  expectTrue refused.hasErrors "admission: a body of the wrong type is not refused"
  expectTrue (refused.admitRoots.completeRoots matches .error _)
    "admission: a root of a program with an error is complete on its own"
  match (refused.admitRoots (some #["double"])).complete with
  | .ok _ => failure "admission: a root of a program with an error is complete"
  | .error missing =>
    expectTrue (missing.any fun line => (line.splitOn "errors are reported").length > 1)
      s!"admission: what is missing does not say that errors are reported: {missing}"

/-! ## Recovery -/

/-- A call whose static argument is inferred through a static name of the library: the inference
evaluates the name, which is first instantiated there. -/
def inferredProgram : String := "module deep
use lib::sizes::{K}
def first<n: nat>(xs: [nat; n + K]) -> nat:
    return 0
def main(xs: [nat; 8]) -> nat:
    return first(xs)
"

def recoverySuite : TestM Unit := do
  -- with a budget of depth 1, the static name is instantiated beyond it, under the inference of
  -- the call: the root lacks because the check is incomplete, and nothing is refused
  let library := nameLibrary.push ("lib::sizes", "module lib::sizes\npub nat K = 4\n")
  let input : SourceInput := { name := "deep", parsed := parseString "deep" inferredProgram }
  let session := Id.run <|
    (Driver.Session.start (options := { budgets := { instantiationDepth := 1 } })).compile #[input]
      (memoryLoader library) "packages"
  expectTrue (!session.hasErrors)
    s!"recovery: running out of a budget under an inference refuses: {(session.refusalsOf #["names", "instances", "types", "defaults", "default bodies", "packages"]).map (·.render)}"
  let lacking : Option (String × Lack) := (session.admitRoots (some #["main"])).lacking[0]?
  match lacking with
  | some (_, .exhausted exhaustion) =>
    expectTrue (exhaustion.budget == .instantiationDepth)
      s!"recovery: main lacks because {reprStr exhaustion.budget} ran out"
  | some (_, lack) => failure s!"recovery: main lacks for another reason: {lack.describe}"
  | none => failure "recovery: main is complete although a budget ran out"
  -- with the default budget the same program is complete
  let complete := Id.run <|
    (Driver.Session.start).compile #[input] (memoryLoader library) "packages"
  expectTrue ((complete.admitRoots (some #["main"])).complete matches .ok _)
    "recovery: the program is not complete with the default budget"

def sessionSuite : TestM Unit := do
  logSuite
  budgetSuite
  referenceSuite
  admissionSuite
  recoverySuite

end Zkc.Tests.Frontend
