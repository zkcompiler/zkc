module

public import Zkc.Frontend.Semantics.Instances
public import Zkc.Frontend.Emit.Root

@[expose] public section
namespace Zkc.Frontend
open Instances Static

namespace Typing

/-- The function instances among the roots, once each. -/
def functionRoots (state : Compile.State) : Array InstanceId := Id.run do
  let mut seen : Std.HashSet InstanceId := {}
  let mut result := #[]
  for root in state.roots do
    if seen.contains root then continue
    seen := seen.insert root
    let some entry := state.table.entries[root]? | continue
    let some found := state.program.declarations[entry.key.declaration]? | continue
    if found.kind == .function || found.kind == .relation || found.kind == .law
        || found.kind == .lawMember || found.kind == .protocol then
      result := result.push root
  return result

/-- A root as source writes it, with the words of a default instance. -/
def rootDescription (state : Compile.State) (root : InstanceId) : String :=
  let description := renderInstance state root
  if state.results.isDefault root then s!"default instance `{description}`" else description

/-- What an admitted result holds of a root that is a function or a protocol: the package that
the core admitted, or why it has none: refused (by the frontend or the core), waiting, not checked
to the end, or without a package of its own (a specification item, a function bound to a row). -/
def rootPackage (state : Compile.State) (root : InstanceId) : Except Lack CheckedPackage :=
  let body := state.results.body? root
  let outcome : Option PackageOutcome :=
    (state.results.packageReports.find? (·.root == root)).map (·.outcome)
  match outcome with
  | some (.admitted package) => .ok package
  | some (.refused reason _) => .error (.refused s!"the core refuses its package: {reason}")
  | some (.waiting reason) => .error (.waiting reason)
  | some (.typedOnly reason) => .error (.noPackage reason)
  | some (.defect message) => .error (.defect message)
  | some (.exhausted exhaustion) => .error (.exhausted exhaustion)
  | none =>
    match body with
    | some (.exhausted exhaustion) => .error (.exhausted exhaustion)
    | some (.waiting reason) => .error (.waiting reason)
    | some .failed => .error (.refused "its body is refused")
    | some (.row _) => .error (.noPackage "it is bound to a row of the vocabulary")
    | _ => .error (.defect "no package is emitted for it")

/-- The package of a root and what the core makes of it. -/
def admit (state : Compile.State) (root : InstanceId) : Option PackageOutcome :=
  match state.results.body? root with
  | some (.done _) | some (.protocol _) =>
    match emitRoot state root with
    | .ok emission =>
      let source := emission.package ⟨[], [], [], [], []⟩
      match source.check with
      | .ok checked => some (.admitted checked)
      | .error refusals =>
        let describe {T Raw : Type} (stage : String) (r : Core.Refusal T Raw) :=
          s!"{stage}: {reprStr r.rule} at {reprStr r.place}"
        let reasons := refusals.map fun
          | .definition (.fn r) => describe "function" r
          | .definition (.protocol r) => describe "protocol" r
          | .projection r => describe "projection" r
          | .association r => describe "association" r
        some (.refused ("; ".intercalate reasons) source)
    | .error (.waiting reason) => some (.waiting reason)
    | .error (.defect message) => some (.defect message)
    | .error (.noCoreForm reason) => some (.typedOnly reason)
  | some (.waiting reason) => some (.waiting reason)
  | some (.exhausted exhaustion) => some (.exhausted exhaustion)
  | _ => none

end Typing

/-- The phase of packages: the package of every root that is a function or a protocol, emitted
and admitted by the core, reported in the order of the roots. -/
def Typing.reportPackages : CompileM Unit := do
  let state ← get
  let reports := (Typing.functionRoots state).filterMap fun root =>
    let description := Typing.rootDescription state root
    (Typing.admit state root).map fun outcome => ({ root, description, outcome } : PackageReport)
  modifyResults fun results => { results with packageReports := reports }
  -- every body passed its own check before its package was emitted, so a package that the
  -- core does not admit is a defect of the frontend, and is logged as one: such a program is
  -- not accepted
  for report in reports do
    let reason : Option String := match report.outcome with
      | .refused reason _ => some s!"the core refuses it: {reason}"
      | .defect message => some message
      | _ => none
    if let some reason := reason then
      let span := (((state.table.entries[report.root]?).bind fun entry =>
        state.program.declarations[entry.key.declaration]?).bind (·.name)).map (·.span)
      logError "defect" (span.getD default) (.ofText
        s!"a defect of the frontend: the package of `{report.description}`, whose bodies passed their own checks: {reason}")
        (origin := .core)

end Zkc.Frontend
