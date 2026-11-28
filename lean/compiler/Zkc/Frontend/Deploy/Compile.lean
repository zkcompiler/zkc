module

public import Zkc.Frontend.Deploy.Emit
public import Zkc.Frontend.Semantics.Typing
public import Zkc.Core.Run.Specialize.Compiler

@[expose] public section
set_option autoImplicit false

/-!
# End-to-end frontend scheme compilation (`Zkc.Frontend.Deploy.Compile`)

Composes `SuitePlan`, `Emit`, `Core.admit`, `Core.deploy`, `Core.deployIdeal`, and
`Core.schemeIdentity` into a single `CompiledScheme` artifact directly ready for runtime
execution (`ZkcRuntime`), specialization (`Core.specialize`), and formal security proofs
(`Zkc.Subject.Deployed`).
-/

namespace Zkc.Frontend.Deploy

open Zkc.Core
open Zkc.Vocabulary
open Zkc.Vocabulary.Project

/-- A fully admitted and deployed frontend scheme with canonical identity bytes and optional
ideal random-oracle deployment. -/
structure CompiledScheme where
  name : String
  plan : SchemePlan
  bindings : Bindings
  named : Core.NamedProgram bindings.vocabulary
  admitted : Core.Admitted bindings.vocabulary
  declaration : Core.Declaration
  deployed : Core.Deployed bindings.vocabulary
  ideal? : Option (Core.Deployed bindings.vocabulary)
  identity : List Nat
  proverRole? : Option Core.Role
  verifierRole? : Option Core.Role

/-- Format `Core.deploy` refusal errors cleanly. -/
def describeDeployErrors {V : Core.Vocabulary} (errs : List (Core.ProgramRefusal V)) : String :=
  ", ".intercalate (errs.map fun r => s!"{reprStr r.rule}@def#{r.place.definition.number}")

/-- Admit and deploy an already-planned `SchemePlan` against a compiled `Compile.State`. -/
def deployPlan (state : Compile.State) (plan : SchemePlan)
    (idealServiceKey : Core.Key := ⟨999000⟩) : Except String CompiledScheme := do
  let emitted ← emitSchemeProgram state plan
  let admitted ← match Core.admit emitted.named ⟨[], [], [], [], []⟩ with
    | .ok a => .ok a
    | .error errs =>
        let pkg : SourcePackage := ⟨emitted.bindings, emitted.named, ⟨[], [], [], [], []⟩⟩
        .error s!"core refused deployed scheme package `{plan.name}`: {pkg.describeRefusals errs}"
  let enc := Project.linkedEncoder emitted.bindings
  let deployed ← match Core.deploy enc admitted emitted.declaration with
    | .ok d => .ok d
    | .error errs =>
        .error s!"core deploy refused scheme `{plan.name}`: {describeDeployErrors errs}"
  let ideal? : Option (Core.Deployed emitted.bindings.vocabulary) :=
    match emitted.declaration.construction with
    | .derived .. =>
        match Core.deployIdeal enc idealServiceKey admitted emitted.declaration with
        | .ok di => some di
        | .error _ => none
    | _ => none
  let identity := Core.schemeIdentity enc admitted emitted.declaration
  return {
    name := plan.name
    plan
    bindings := emitted.bindings
    named := emitted.named
    admitted
    declaration := emitted.declaration
    deployed
    ideal?
    identity
    proverRole? := emitted.proverRole?
    verifierRole? := emitted.verifierRole?
  }

/-- Plan, emit, admit, and deploy a `SchemeEntry` from `state.results.schemes`. -/
def deploySchemeEntry (state : Compile.State) (scheme : SchemeEntry)
    (sessionTag : Option (List Nat) := none) (application : List Nat := []) :
    Except String CompiledScheme := do
  let plan ← planScheme scheme sessionTag application
  deployPlan state plan

/-- Find and deploy a named scheme in `state` (or the sole scheme when `schemeName == ""`). -/
def deployScheme (state : Compile.State) (schemeName : String := "")
    (sessionTag : Option (List Nat) := none) (application : List Nat := []) :
    Except String CompiledScheme := do
  let scheme ← findSchemeEntry state schemeName
  deploySchemeEntry state scheme sessionTag application

/-- Deploy any compiled protocol root in `state` (even without a `scheme` declaration in source)
with an explicit `ConstructionPlan` and optional layout / contexts / retry. -/
def deployProtocolRoot (state : Compile.State) (rootName : String)
    (construction : ConstructionPlan)
    (contexts : List (String × LinkedType) := [])
    (layout : Option LayoutPlan := none)
    (proverRole : Option String := none)
    (retry : Option (Nat × List String) := none)
    (application : List Nat := []) : Except String CompiledScheme := do
  let roots := Typing.functionRoots state
  let matches_ := roots.filter fun id =>
    match state.results.body? id with
    | some (.protocol _) =>
        let short := Typing.rootDescription state id false
        let full := Typing.rootDescription state id true
        namesRoot rootName short || namesRoot rootName full || short == rootName || full == rootName ||
          short.startsWith s!"{rootName}<" || full.endsWith s!"::{rootName}" ||
          (full.splitOn s!"::{rootName}<").length > 1
    | _ => false
  let some inst := matches_[0]?
    | let avail := roots.toList.filterMap fun id =>
        match state.results.body? id with
        | some (.protocol _) => some (Typing.rootDescription state id false)
        | _ => none
      throw s!"protocol root `{rootName}` not found (available protocols: {", ".intercalate avail})"
  let finalLayout :=
    match construction, layout with
    | .interactive, _ => layout
    | _, some l => some l
    | _, none => some { layoutName := "zkc::layout::canonical" }
  let plan : SchemePlan := {
    name := rootName
    protocol := inst
    construction
    proverRole
    contexts
    layout := finalLayout
    retry
    application
  }
  deployPlan state plan

/-- Convenience wrapper deploying a compiled protocol root with a specific `SuiteSpec`. -/
def deployProtocolWithSuite (state : Compile.State) (rootName : String) (suite : SuiteSpec)
    (sessionTag : Option (List Nat) := none) (application : List Nat := []) :
    Except String CompiledScheme :=
  deployProtocolRoot state rootName (.derived suite sessionTag) (application := application)

mutual
  /-- Count AST nodes in a specialized `ClosedTerm`. -/
  def closedTermNodeCount {V : Core.Vocabulary} {fns : List (FnHeader V)} {procs : List (ClosedProcSig V)}
      {σ : List V.Ty} {Γ : Ctx V.Ty} {outs : List V.Ty} :
      ClosedTerm V fns procs σ Γ outs → Nat
    | .ret _ => 1
    | .letBind first _ rest => 1 + closedTermNodeCount first + closedTermNodeCount rest
    | .seq first second => 1 + closedTermNodeCount first + closedTermNodeCount second
    | .alias _ _ rest => 1 + closedTermNodeCount rest
    | .localOp _ _ _ _ rest => 1 + closedTermNodeCount rest
    | .guard _ _ _ rest => 1 + closedTermNodeCount rest
    | .choose _ _ onTrue onFalse _ rest =>
        1 + closedTermNodeCount onTrue + closedTermNodeCount onFalse + closedTermNodeCount rest
    | .cases _ _ arms _ rest => 1 + closedArmsNodeCount arms + closedTermNodeCount rest
    | .loop _ _ _ _ _ body _ rest => 1 + closedTermNodeCount body + closedTermNodeCount rest
    | .block _ _ body _ rest => 1 + closedTermNodeCount body + closedTermNodeCount rest
    | .frame _ _ _ body _ rest => 1 + closedTermNodeCount body + closedTermNodeCount rest
    | .call _ _ _ _ rest => 1 + closedTermNodeCount rest
    | .withLayer _ _ body => 1 + closedTermNodeCount body
    | .underLayer inner => 1 + closedTermNodeCount inner
    | .effect _ _ _ => 1
    | .retry _ _ _ _ body _ rest => 1 + closedTermNodeCount body + closedTermNodeCount rest

  /-- Count AST nodes across `ClosedArms`. -/
  def closedArmsNodeCount {V : Core.Vocabulary} {fns : List (FnHeader V)} {procs : List (ClosedProcSig V)}
      {σ : List V.Ty} {Γ : Ctx V.Ty} {mid payloads : List V.Ty} :
      ClosedArms V fns procs σ Γ mid payloads → Nat
    | .nil => 0
    | .cons _ arm rest => closedTermNodeCount arm + closedArmsNodeCount rest
end

/-- Count shared procedures in `ClosedProcs`. -/
def closedProcsCount {V : Core.Vocabulary} {fns : List (FnHeader V)} :
    {procs : List (ClosedProcSig V)} → ClosedProcs V fns procs → Nat
  | [], .nil => 0
  | _ :: _, .cons _ _ tail => 1 + closedProcsCount tail

/-- Summarize specialized `ClosedRole` AST size and shared procedure count for reporting/CLI. -/
def CompiledScheme.specializationStats (cs : CompiledScheme) :
    List (Core.Role × Nat × Nat) :=
  let roles := List.range cs.deployed.entry.roles
  roles.filterMap fun r =>
    let stack := cs.deployed.stack r
    if stack.isEmpty && cs.proverRole? != some r && cs.verifierRole? != some r then none
    else
      let cr := Core.specialize cs.deployed r
      some (r, closedTermNodeCount cr.body, closedProcsCount cr.procs)

end Zkc.Frontend.Deploy
