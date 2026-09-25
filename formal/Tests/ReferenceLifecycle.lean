import Tools.Interactive.GenericReference
import Tests.Checks

/-! Executable regressions for the in-process reference entry point. Resource
units have no JSON initializer or wire encoding. A host can nevertheless retain
an interpreter-issued unit and supply it to a subsequent entry; these checks
exercise that path without inventing a serializable capability initializer. -/

set_option autoImplicit false

namespace Tests.ReferenceLifecycle
open Lean (Json)
open Tools.Interactive Tools.Interactive.Reference

private def sourceText := r#"[
  "zkc.protocol/1",
  [["create", "resource_unit.create", ["Slot.A"], ""]],
  [["function", "Select", [["n", "index"]], ["index"],
    [["op", "temporary", "create", [], [], ["temporary"]], ["return", ["n"]]], ["Select", []]]],
  [["protocol", "Root", ["P", "V"], ["rounds"],
    [["punit", "P", "resource_unit:Slot.A"], ["pn", "P", "index"],
     ["vunit", "V", "resource_unit:Slot.A"], ["vn", "V", "index"]],
    [["P", "resource_unit:Slot.A"], ["V", "resource_unit:Slot.A"]], [],
    [["return", ["punit", "vunit"]]]]],
  [["instance", "root", "Root", [["rounds", ["ingress", "1",
    [["P", "Select", ["pn"]], ["V", "Select", ["vn"]]]]]], [], [["P", "P"], ["V", "V"]]]],
  [["entry", "main", "root"]]
]"#

private def seed (source : Json) (pn vn : Nat) : Result (Generic.Prepared × Invocation) := do
  let prepared ← Generic.prepareSource source
  let binding ← prepared.source.binding "root"
  let definition ← prepared.source.protocol "Root"
  let location := Location.plain "test" "root" "entry" "joint"
  -- Mint through the same authoritative primitive used by source execution.
  let issue : RunM (Value × Value) := do
    let p ← createResourceUnit { location with scope := { location.scope with role := "P" } } "Slot.A"
    let v ← createResourceUnit { location with scope := { location.scope with role := "V" } } "Slot.A"
    return (p, v)
  let (issued, state) := issue.run {}
  let .ok (p, v) := issued | throw "unit-issuance"
  let environments := [("P", [("punit", p), ("pn", Value.fromArithmetic .bls (.index pn))]),
    ("V", [("vunit", v), ("vn", Value.fromArithmetic .bls (.index vn))])]
  return (prepared, ⟨location, binding, definition, definition.arguments, environments, state⟩)

private def checkFault (checks : Checks.Checks) (expected : String) (prepared : Generic.Prepared) (invocation : Invocation) : IO Unit := do
  let (result, state) := Reference.run prepared none invocation
  let .error fault := result | throw (IO.userError (expected ++ ": expected fault"))
  checks.holds (fault.detail == expected) (expected ++ ": wrong fault " ++ fault.detail)
  checks.holds (state.resources.all (·.payload.kind != "resource_unit")) (expected ++ ": leaked root units")

-- A controlled driver harness: local Select is the identity on its index input.
-- These checks exercise scheduling/finalization, not primitive interpretation.
private def scheduleServices (base : Location) : Control.Services Value RunM where
  typeOf value := value.ty.spelling
  fail scope reason detail := failAt { base with scope } reason detail
  charge scope := charge { base with scope }
  iteration _ := pure ()
  executeLocal _ _ inputs := pure inputs
  send _ _ _ _ := pure ()
  received _ _ _ _ := pure ()
  receive scope _ _ _ := failAt { base with scope } "refused" "unexpected-test-receive"
  enterRegion _ _ := pure ()
  exitRegion _ _ := pure ()

private def scheduleChecks (checks : Checks.Checks) (prepared : Generic.Prepared)
    (initial : Invocation) : IO Unit := do
  let base := initial.location
  let cursor : SourceControl.Cursor := { binding := initial.binding, scope := base.scope, body := [] }
  for (budget, cursors, expected) in [
      (0, [], some 0), (7, [], some 7),
      (0, [cursor], none), (1, [cursor], some 0),
      (1, [{ cursor with body := [.ret []] }], none),
      (2, [{ cursor with body := [.ret []] }], some 0),
      (3, [{ cursor with body := [.ret []] }], some 1)] do
    let (result, _) := (SourceControl.next base prepared.source budget cursors).run initial.state
    let holds := match expected, result with
      | some remaining, .ok (none, [], actual) => remaining == actual
      | none, .error fault => fault.reason == "exhausted" && fault.detail == "source-schedule-work-limit"
      | _, _ => false
    checks.holds holds s!"cursor budget {budget}, stack {cursors.length}, remainder {expected}"
  let .ok select := prepared.source.function "Select" | throw (IO.userError "select-function")
  let mut completedParticipants : List SourceControl.Participant := []
  for (role, name) in [("P", "punit"), ("V", "vunit")] do
    let .ok unit := Control.readValues (Control.roleStore initial.environments role) [name]
      | throw (IO.userError "root-unit")
    completedParticipants := completedParticipants ++ [{ role, script := .done unit }]
  for (budget, cursors, returns) in [
      (0, [], true), (0, [cursor], false), (1, [cursor], true),
      (1, [{ cursor with body := [.ret []] }], false),
      (2, [{ cursor with body := [.ret []] }], true)] do
    let (result, state) := (SourceControl.drive base prepared.source (scheduleServices base)
      budget cursors completedParticipants).run initial.state
    let holds := match result with
      | .ok _ => returns && state.resources.length == 2
      | .error fault => !returns && fault.reason == "exhausted" &&
          fault.detail == "source-schedule-work-limit" && state.resources.isEmpty
    checks.holds holds s!"driver budget {budget}, stack {cursors.length}: root disposal"
  -- One cut, return instruction, and frame pop cost exactly three units. The
  -- last cursor inspection is free, but a remaining frame still costs one.
  let scope := { base.scope with role := "P", site := "select", path := [.localCall "select" "Select"] }
  let participants := completedParticipants.map fun p => if p.role != "P" then p else
    { p with script := (.cut (.local scope select [Value.fromArithmetic .bls (.index 0)])
        (fun _ => p.script)) }
  let cursors := [{ cursor with body := [.localCall "select" "P" "Select" ["pn"] ["selected"], .ret []] }]
  for budget in [2, 3, 4] do
    let (result, state) := (SourceControl.drive base prepared.source (scheduleServices base)
      budget cursors participants).run initial.state
    let holds := match result with
      | .ok _ => budget ≥ 3 && state.resources.length == 2
      | .error fault => budget == 2 && fault.reason == "exhausted" &&
          fault.detail == "source-schedule-work-limit" && state.resources.isEmpty
    checks.holds holds s!"driver cut at budget {budget}: no premature root return"
  -- Seed the real work ledger near its limit instead of executing a million
  -- charges. Resume fuel must leave that limit authoritative, and a later
  -- role's failing charge must preserve an earlier role's returned unit.
  let underlying := scheduleServices base
  let participants := ["P", "V"].map fun role =>
    ({ role, script := (Control.executeBody (SourceControl.services base underlying)
        prepared.source (some role) limits.callDepth initial.binding initial.definition
        { base.scope with role } initial.context
        (initial.environments.filter (·.1 == role)) [.ret ["punit", "vunit"]]) } : SourceControl.Participant)
  for available in [0, 1, 2] do
    let (result, state) := (SourceControl.drive base prepared.source underlying 2
      [{ cursor with body := [.ret ["punit", "vunit"]] }] participants).run
        { initial.state with spent := limits.steps - available }
    let holds := match result with
      | .ok _ => available == 2 && state.resources.length == 2
      | .error fault => available < 2 && fault.reason == "exhausted" &&
          fault.detail == "reference-work-limit" && state.resources.length == available &&
          state.resources.all (·.owner == "P")
    checks.holds (holds && state.spent == limits.steps) s!"resume respects {available} remaining charges"

/-- These are interpreter executions, not a refinement theorem. -/
def run : IO Unit := do
  let checks ← Checks.start
  let .ok source := Json.parse sourceText | throw (IO.userError "fixture-json")
  let .ok (prepared, initial) := seed source 0 0 | throw (IO.userError "fixture-admission")
  scheduleChecks checks prepared initial
  let (success, state) := Reference.run prepared none initial
  checks.holds (success.isOk && state.resources.length == 2) "successful roots retain supplied units"
  let .ok (_, bound) := seed source 2 2 | throw (IO.userError "bound-fixture")
  checkFault checks "interactive-family-bound" prepared bound
  let .ok (_, disagree) := seed source 0 1 | throw (IO.userError "agreement-fixture")
  checkFault checks "interactive-family-disagreement" prepared disagree
  -- Stopping inside the selector must also close units outside that local frame.
  let stoppedText := sourceText.replace
    "[\"return\", [\"n\"]]" "[\"stop\", \"halt\", \"\", \"reject\"]"
  let .ok stoppedSource := Json.parse stoppedText | throw (IO.userError "stop-json")
  let .ok (stoppedPrepared, stopped) := seed stoppedSource 0 0 | throw (IO.userError "stop-fixture")
  checkFault checks "explicit-stop" stoppedPrepared stopped
  -- A public group input invokes validation before any selector/body executes.
  let publicText := sourceText.replace "[\"pn\", \"P\", \"index\"],"
    "[\"pn\", \"P\", \"index\"], [\"g\", \"P\", \"groups:bls12-381.g1\"],"
  let .ok publicSource := Json.parse publicText | throw (IO.userError "public-json")
  let .ok (publicPrepared, publicInvocation) := seed publicSource 0 0
    | throw (IO.userError "public-fixture")
  let .ok group := decodeValue (.arr #[.str "groups:bls12-381.g1", .str "5a4b4356010a00000000"])
    | throw (IO.userError "public-value")
  let publicInvocation := { publicInvocation with
    environments := publicInvocation.environments.map fun (role, store) =>
      (role, if role == "P" then ("g", group) :: store else store) }
  checkFault checks "exact-request-missing" publicPrepared publicInvocation
  for selected in [none, some "P"] do
    let initial := match selected with
      | none => initial
      | some role => { initial with
          location := { initial.location with scope := { initial.location.scope with role } }
          environments := initial.environments.filter (·.1 == role)
          state := { initial.state with resources := initial.state.resources.filter (·.owner == role) } }
    for detail in ["unused-replies", "unused-primitive-replies"] do
      let state := if detail == "unused-replies" then
          { initial.state with replies := [(.str "unrequested", .boolean true)] }
        else { initial.state with answers := initial.state.answers.insert "unrequested" (.arr #[]) }
      let (result, after) := Reference.run prepared selected { initial with state }
      let .error fault := result | throw (IO.userError "postflight expected fault")
      checks.holds (fault.detail == detail && after.resources.length == initial.state.resources.length)
        "postflight must preserve completed roots"

  checks.finish "reference participant lifecycle"

#eval run

end Tests.ReferenceLifecycle
