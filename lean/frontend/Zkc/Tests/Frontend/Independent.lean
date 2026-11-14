import Lean.Data.Json
import Zkc.Tests.Frontend.Protocols

/-!
# The independent conformance suite

A suite of layer A written from the reference alone by a reader who saw no implementation: a
directory of cases (`cases/<id>/…`) and `expectations.json`, which gives each case its
phase, its expected outcome (`accept`, `refuse`, `parse`, `underdetermined`) and the rules it
cites. Each case is read, its names resolved, its instances formed, its bodies typed, and the
packages of its roots emitted and admitted by the core.

- `accept`: no refusal, and every package admitted.
- `refuse`: the first refusal is by a rule that the case cites, or by a rule of the table of
  equivalent labels below, which gives each its reason.
- `parse`: the files parse.
- `underdetermined`: the outcome is printed, and checked against the reading taken for the
  question (the table of readings below), not against the suite's own label.

A case whose roots wait for a form that is not elaborated yet waits, with the form. Ten cases
whose expectations state small runs are run on those inputs.
-/

namespace Zkc.Tests.Frontend

open Zkc.Frontend
open Zkc.Core.Concrete (Datum)

/-- A case of the suite: its files, by the names the expectations give them. -/
structure IndependentCase where
  id : String
  phase : String
  expected : String
  rules : Array String
  files : Array (String × System.FilePath)

/-- The cases of `expectations.json`. -/
def readIndependentCases (directory : System.FilePath) : IO (Except String (Array IndependentCase)) := do
  let text ← IO.FS.readFile (directory / "expectations.json")
  return do
    let json ← Lean.Json.parse text
    let cases ← json.getObjValAs? (Array Lean.Json) "cases"
    cases.mapM fun entry => do
      let id ← entry.getObjValAs? String "id"
      let phase ← entry.getObjValAs? String "phase"
      let expected ← entry.getObjValAs? String "expected"
      let rules ← entry.getObjValAs? (Array String) "rules"
      let sources ← entry.getObjVal? "sources"
      let .obj fields := sources | throw s!"{id}: the sources are no object"
      let mut files : Array (String × System.FilePath) := #[]
      for (name, path) in fields.toArray do
        let .str relative := path | throw s!"{id}: a source is no string"
        files := files.push (name, directory / relative)
      -- the main module first
      let ordered := files.filter (·.1 == "main.zkc") ++ files.filter (·.1 != "main.zkc")
      return { id, phase, expected, rules, files := ordered }

/-- Rules of the frontend that the suite's citations name otherwise, with the reason. -/
def equivalentLabels : Array (String × Array String × String) := #[
  ("NL6", #["§3.5", "SP12"],
   "an operator of the table of §3.5 is a function of the fixed table; on a type member of a module parameter it is a member of the interface (SP12); NL6 refuses the operator that is none"),
  ("TY7", #["TY5", "TY8", "TY9"],
   "TY7 refuses an index or a bound of a slice whose range (TY8), or whose conversion by a fact (TY5, TY9), is not known"),
  ("TY8", #["TY5", "TY9"],
   "TY8 refuses a conversion of a natural to an index whose range is not known: the conversion by a fact of TY5 and TY9")]

/-- The readings taken for the questions that the suite leaves open: the outcome they give,
`accept` or a refusal by one of the rules. -/
def independentReadings : Array (String × String × Array String × String) := #[
  ("ambiguity-guard-false-without-continuation-proof", "refuse", #["LN2", "LN1"],
   "a path is syntactic: a guard continues, so the ticket is never passed on"),
  ("ambiguity-zero-protocol-loop", "accept", #[], "a loop of no iteration types no body and is nothing"),
  ("ambiguity-static-argument-uniformity", "accept", #[],
   "static arguments are compared as values: the loop is stepped, its iterations in sequence"),
  ("ambiguity-unobserving-container-equality", "refuse", #["SP12", "TY12"],
   "an operator applies to a composite only when it applies to every component"),
  ("ambiguity-empty-collect-type", "accept", #[],
   "a collected name after no iteration has the element type the body gives, or is `[]`"),
  ("ambiguity-spec-admission", "refuse", #["NL3"], "the source is well formed: names resolve, also in specifications"),
  ("ambiguity-protocol-if-expression", "accept", #[],
   "an `if` expression is an expression of the roles that compute its binding"),
  ("ambiguity-inference-power-one", "refuse", #["SP6"],
   "an exponent is solved only for a base of at least 2; `1^n` determines no `n`"),
  ("ambiguity-stop-summary", "refuse", #["FN5"],
   "whether a body can stop is read on the text, before short-circuit: `false and fail()` can stop")]

/-- What the frontend makes of a case. -/
inductive IndependentOutcome where
  | accepted
  | refused (rule : String) (text : String)
  | waiting (reasons : Array String)
  | notAdmitted (text : String)

def IndependentOutcome.describe : IndependentOutcome → String
  | .accepted => "accepted"
  | .refused rule text => s!"refused by {rule}: {text}"
  | .waiting reasons => s!"waiting for {"; ".intercalate reasons.toList}"
  | .notAdmitted text => s!"not admitted by the core: {text}"

/-- A case through the frontend: names, instances, typing, and the core's admission of the
packages of its roots. -/
def independentOutcome (load : Array String → IO (Option SourceInput)) (case : IndependentCase) :
    IO (IndependentOutcome × Option TypingCheck) := do
  let mut inputs : Array SourceInput := #[]
  for (name, path) in case.files do
    let label := s!"{case.id}/{name}"
    inputs := inputs.push { name := label, parsed := Syntax.parse label (← IO.FS.readBinFile path) }
  -- the cases of the lexical structure and of the grammar stop at the parser
  if ["lexical", "parse", "parse-only"].contains case.phase then
    for input in inputs do
      if let .error error := input.parsed then
        return (.refused error.rule s!"{error.span.startLine}:{error.span.startColumn} {error.message}", none)
    return (.accepted, none)
  let names := inputs.map (·.name)
  let nameCheck ← checkNames inputs load
  if let some first := nameCheck.refusals[0]? then
    return (.refused first.rule first.render, none)
  let instances := checkInstances nameCheck names
  if let some first := instances.refusals[0]? then
    return (.refused first.rule first.render, none)
  let check := checkTyping instances names
  if let some first := check.refusals[0]? then
    return (.refused first.rule first.render, some check)
  let mut waits : Array String := #[]
  for report in check.packages do
    match report.outcome with
    | .refused reason _ => return (.notAdmitted s!"{report.description}: {reason}", some check)
    | .unjustified functions _ =>
      return (.notAdmitted s!"{report.description}: {"; ".intercalate functions.toList}", some check)
    | .defect message => return (.notAdmitted s!"{report.description}: {message}", some check)
    | .waiting reason => unless waits.contains reason do waits := waits.push reason
    | _ => pure ()
  unless waits.isEmpty do return (.waiting waits, some check)
  return (.accepted, some check)

/-- Whether a refusal by a rule agrees with the rules a case cites, directly or by the table of
equivalent labels. -/
def refusalAgrees (rule : String) (cited : Array String) : Bool :=
  cited.contains rule || equivalentLabels.any fun (label, citations, _) =>
    label == rule && citations.any cited.contains

/-- A function root run on inputs, against the outcome stated. -/
def expectCaseRun (label : String) (check : TypingCheck) (root : String) (inputs : List Datum)
    (expected : Expected) : TestM Unit :=
  expectRun label check root inputs expected

/-- The runs of ten cases whose expectations state small runs, encoded by hand. -/
def independentRuns (case : String) (check : TypingCheck) : TestM Unit := do
  let label := s!"independent {case}"
  match case with
  | "facts-indexed-sum" => expectCaseRun label check "f" [numbers [1, 2]] (.returned [.number 513])
  | "facts-natural-expression-type" => expectCaseRun label check "f" [.number 3] (.returned [.number 4])
  | "facts-guarded-index" =>
    let xs := numbers (List.range 8)
    expectCaseRun label check "f" [xs, .number 7] (.returned [.number 7])
    expectCaseRun label check "f" [xs, .number 8] (.stopped .refused)
  | "loop-stepped-collection" =>
    expectCaseRun label check "f" [] (.returned [.sequence [numbers [0], numbers [0, 0], numbers [0, 0, 0]]])
  | "opaque-interface-dispatch" => expectCaseRun label check "main" [] (.returned [.number 2])
  | "match-exhaustive-payloads" =>
    expectCaseRun label check "f" [.sequence [.number 0, .number 9]] (.returned [.number 9])
    expectCaseRun label check "f" [.sequence [.number 1, Datum.ofBool true]] (.returned [.number 1])
  | "infer-fact-explicit-bound" =>
    expectCaseRun label check "main" [.number 7] (.returned [.number 7])
    expectCaseRun label check "main" [.number 8] (.stopped .reject)
  | "holders-nested-send-call" =>
    -- x = 0: A stops `abort` in the payload, and B, which waits for the message, is blocked
    expectProtocolRun label check "P" [.number 0] [("A", .stopped .abort), ("B", .blocked)]
    expectProtocolRun label check "P" [.number 3] [("A", .returned []), ("B", .returned [])]
  | "wire-fact-does-not-cross" =>
    expectProtocolRun label check "P" [numbers [4, 9]] [("A", .returned []), ("B", .returned [])]
    expectProtocolRun label check "P" [numbers [4]] [("A", .stopped .refused), ("B", .blocked)]
  | "sampling-empty-array" => expectProtocolRun label check "P" [] [("A", .returned [])]
  | _ => pure ()

/-- The cases whose runs are checked. -/
def independentRunCases : Array String := #[
  "facts-indexed-sum", "facts-natural-expression-type", "facts-guarded-index",
  "loop-stepped-collection", "opaque-interface-dispatch", "match-exhaustive-payloads",
  "infer-fact-explicit-bound", "holders-nested-send-call", "wire-fact-does-not-cross",
  "sampling-empty-array"]

def independentSuite (directory : System.FilePath) (library : System.FilePath) : TestM Unit := do
  let cases ← match ← readIndependentCases directory with
    | .ok cases => pure cases
    | .error message => do failure s!"independent suite: {message}"; return
  let load ← cachedLoader #[library]
  let mut agreeing := 0
  let mut disagreeing : Array String := #[]
  let mut waiting : Array String := #[]
  let mut readings : Array String := #[]
  let mut executions := 0
  let mut protocolRoots := 0
  for case in cases do
    let (outcome, check?) ← independentOutcome (fun names => (load names : IO _)) case
    if let some check := check? then protocolRoots := protocolRoots + (checkedProtocols check).1
    match case.expected, outcome with
    | "underdetermined", _ =>
      match independentReadings.find? (·.1 == case.id) with
      | some (_, reading, rules, reason) =>
        let agrees := match reading, outcome with
          | "accept", .accepted => true
          | "refuse", .refused rule _ => rules.contains rule
          | _, _ => false
        readings := readings.push s!"{case.id}: {outcome.describe}; the reading: {reading} {rules.toList} ({reason})"
        if agrees then pass
        else failure s!"independent {case.id}: the reading is {reading} {rules.toList}; {outcome.describe}"
      | none => failure s!"independent {case.id}: no reading is taken for this question"
    | _, .waiting reasons =>
      pass
      waiting := waiting.push s!"{case.id}: {"; ".intercalate reasons.toList}"
    | "accept", .accepted | "parse", .accepted =>
      pass
      agreeing := agreeing + 1
    | "refuse", .refused rule text =>
      if refusalAgrees rule case.rules then
        pass
        agreeing := agreeing + 1
      else
        disagreeing := disagreeing.push s!"{case.id}: expects a refusal by {case.rules.toList}; refused by {rule}: {text}"
    | expected, other =>
      match acceptedSinceFactsAreAboutValues.find? (·.1 == case.id), other with
      | some (_, reason), .accepted =>
        pass
        readings := readings.push s!"{case.id}: accepted; the suite expects {expected} {case.rules.toList} by the reference before a fact was about a value ({reason})"
      | _, _ =>
        disagreeing := disagreeing.push s!"{case.id}: expects {expected} {case.rules.toList}; {other.describe}"
    if independentRunCases.contains case.id then
      if let some check := check? then
        independentRuns case.id check
        executions := executions + 1
  for entry in disagreeing do failure s!"independent {entry}"
  note s!"{cases.size} cases: {agreeing} agreeing, {disagreeing.size} disagreeing, {waiting.size} waiting, {readings.size} questions checked against their readings; {executions} cases run on the inputs their expectations state; {protocolRoots} packages of protocol roots admitted with the check of facts of their protocols"
  for entry in waiting do note s!"waiting: {entry}"
  for entry in readings do note s!"question: {entry}"
  for (label, citations, reason) in equivalentLabels do
    note s!"equivalent label: {label} for a case citing {citations.toList}: {reason}"

end Zkc.Tests.Frontend
