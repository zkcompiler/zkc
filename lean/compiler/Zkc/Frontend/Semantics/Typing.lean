module

public import Zkc.Frontend.Semantics.Instances
public import Zkc.Frontend.Emit.Root
public import Zkc.Frontend.Emit.Refusal

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
    let some instanceKey := state.table.allocatedKey? root | continue
    let some found := state.program.declarations[instanceKey.declaration]? | continue
    if found.kind == .function || found.kind == .relation || found.kind == .law
        || found.kind == .lawMember || found.kind == .protocol then
      result := result.push root
  return result

/-- A root as source writes it, with the words of a default instance. -/
def rootDescription (state : Compile.State) (root : InstanceId) (qualified : Bool := false) : String :=
  let name := if qualified then (state.table.allocatedKey? root).map (qualifiedName state.program ·.declaration) else none
  let description := renderInstance state root name
  if state.results.isDefault root then s!"default instance `{description}`" else description

/-- What an admitted result holds of a root that is a function or a protocol: the package that
the core admitted, or why it has none: refused (by the frontend or the core), waiting, not checked
to the end, or without a package of its own (a specification item, a function bound to a row). -/
def rootPackage (state : Compile.State) (root : InstanceId) : Except Lack CheckedPackage :=
  if let some lack := state.rootModuleFailures[root]? then .error lack else
  let body := state.results.body? root
  let outcome : Option PackageOutcome :=
    (state.results.packageReports.find? (·.root == root)).map (·.outcome)
  match outcome with
  | some (.admitted package) => .ok package
  | some (.refused p errors) => .error (.refused s!"the core refuses its package: {p.describeRefusals errors}")
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
      | .ok checked => if state.rootModuleFailures.contains root then none else some (.admitted checked)
      | .error refusals => some (.refused source refusals)
    | .error (.waiting reason) => some (.waiting reason)
    | .error (.defect message) => some (.defect message)
    | .error (.noCoreForm reason) => some (.typedOnly reason)
    | .error (.exhausted exhaustion) => some (.exhausted exhaustion)
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
  for report in reports do
    let diagnostic : Option (String × DiagnosticOrigin × String) := match report.outcome with
      | .refused p errors => some ("core", .core, s!"the core refuses the package: {p.describeRefusals errors}")
      | .defect message => some ("defect", .emission, s!"a defect of the frontend: {message}")
      | _ => none
    if let some (rule, origin, message) := diagnostic then
      let span := (((state.table.allocatedKey? report.root).bind fun key =>
        state.program.declarations[key.declaration]?).bind (·.name)).map (·.span)
      logError rule (span.getD default) (.ofText s!"{report.description}: {message}") (origin := origin)

end Zkc.Frontend
