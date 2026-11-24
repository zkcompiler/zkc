import Lean.Data.Json
import Zkc.Tests.Frontend.TypingReference

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

An exhausted check is counted separately and fails the suite. A case whose roots wait for a form that is not elaborated yet waits, with the form.
-/

namespace Zkc.Tests.Frontend

open Zkc.Frontend

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
  | incomplete (reason : String)
  | notAdmitted (text : String)

def IndependentOutcome.describe : IndependentOutcome → String
  | .accepted => "accepted"
  | .incomplete reason => s!"incomplete: {reason}"
  | .refused rule text => s!"refused by {rule}: {text}"
  | .waiting reasons => s!"waiting for {"; ".intercalate reasons.toList}"
  | .notAdmitted text => s!"not admitted by the core: {text}"

/-- Classify every executable root of a typed conformance case. -/
def checkedOutcome (check : TypingCheck) : IndependentOutcome := Id.run do
  if let some diagnostic := check.incomplete[0]? then
    return .incomplete (diagnostic.message.renderWith Renderer.plain false)
  if let some first := check.refusals[0]? then
    return .refused first.rule first.render
  let mut waits : Array String := #[]
  for root in Typing.functionRoots check.state do
    -- A primitive declaration names a row. Every other selected root needs its own outcome.
    if check.state.results.body? root matches some (.row _) then continue
    match Typing.rootPackage check.state root with
    | .ok _ => pure ()
    | .error (.waiting reason) | .error (.noPackage reason) =>
      unless waits.contains reason do waits := waits.push reason
    | .error (.exhausted e) => return .incomplete e.describe
    | .error lack => return .notAdmitted s!"{Typing.rootDescription check.state root}: {lack.describe}"
  unless waits.isEmpty do return .waiting waits
  return .accepted

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
  return (checkedOutcome check, some check)

/-- Whether a refusal by a rule agrees with the rules a case cites, directly or by the table of
equivalent labels. -/
def refusalAgrees (rule : String) (cited : Array String) : Bool :=
  cited.contains rule || equivalentLabels.any fun (label, citations, _) =>
    label == rule && citations.any cited.contains

def independentSuite (directory : System.FilePath) (library : System.FilePath) : TestM Unit := do
  let cases ← match ← readIndependentCases directory with
    | .ok cases => pure cases
    | .error message => do failure s!"independent suite: {message}"; return
  let load ← cachedLoader #[library]
  let mut agreeing := 0
  let mut disagreeing : Array String := #[]
  let mut incomplete := 0
  let mut waiting : Array String := #[]
  let mut readings : Array String := #[]
  let mut protocolRoots := 0
  for case in cases do
    let (outcome, check?) ← independentOutcome (fun names => (load names : IO _)) case
    if let some check := check? then protocolRoots := protocolRoots + (checkedProtocols check).1
    match case.expected, outcome with
    | _, .incomplete reason =>
      incomplete := incomplete + 1
      failure s!"independent {case.id}: incomplete: {reason}"
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
  for entry in disagreeing do failure s!"independent {entry}"
  note s!"{cases.size} cases: {agreeing} agreeing, {disagreeing.size} disagreeing, {waiting.size} waiting, {incomplete} incomplete, {readings.size} questions checked against their readings; {protocolRoots} packages of protocol roots admitted with the check of facts of their protocols"
  for entry in waiting do note s!"waiting: {entry}"
  for entry in readings do note s!"question: {entry}"
  for (label, citations, reason) in equivalentLabels do
    note s!"equivalent label: {label} for a case citing {citations.toList}: {reason}"

end Zkc.Tests.Frontend
