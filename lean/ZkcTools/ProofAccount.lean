module

public import Lean

/-! Measurement of applications in checked proof bodies. This module supplies
no proof rule and is never consulted by receipt acceptance. A method declares
its checkpoints once; actual applications, types, contexts and dependency paths
are read from the environment. Missing attribution is a measurement failure,
not evidence against the proposition being measured.
-/

public meta section
namespace ZkcTools.ProofAccount
open Lean Meta

inductive Route where
  | generalRule | authorLemma | familyPackage

def Route.label : Route → String
  | .generalRule => "general-rule"
  | .authorLemma => "author-lemma"
  | .familyPackage => "family-package"

/-- The argument of an actual application can be the inline proof obligation.
The surrounding telescope is retained, including its hypotheses. -/
inductive Selection where
  | application
  | lastArgument

inductive ArgumentValue where
  | declaration (name : Name)
  | natural (value : Nat)
  | binder (name : Name)

structure ArgumentBinding where
  parameter : Name
  value : ArgumentValue

structure Checkpoint where
  identifier : String
  phase : String
  responsibility : String
  owner : Name
  callee : Name
  selection : Selection := .application
  /-- Besides propositions, a method may measure a typed proof object. -/
  proofObjectHeads : List Name := []
  arguments : List ArgumentBinding := []
  expectedUses : Option Nat := none
  route : Route

/-- A path follows constants in declaration *values*, not imports or standalone
declaration types. It is syntactic provenance, not a minimal dependency claim. -/
structure Reachability where
  paths : NameMap (List Name) := {}

def Reachability.require (graph : Reachability) (name : Name) : MetaM (List Name) := do
  let some path := graph.paths.find? name
    | throwError "proof-account: declaration is not reached by a proof body: {name}"
  return path

def reachable (root : Name) : MetaM Reachability := do
  let env := (← getEnv).setExporting false
  unless (env.find? root).isSome do
    throwError "proof-account: unknown root: {root}"
  let mut paths : NameMap (List Name) := {}
  let mut pending := [(root, [root])]
  while !pending.isEmpty do
    let (name, path) := pending.head!
    pending := pending.tail!
    if paths.contains name then continue
    paths := paths.insert name path
    if let some info := env.find? name then
      if let some value := info.value? (allowOpaque := true) then
        for dependency in value.getUsedConstants do
          if !paths.contains dependency then
            pending := (dependency, path ++ [dependency]) :: pending
  return ⟨paths⟩

private def render (expression : Expr) : MetaM String :=
  withOptions (fun options => options.set `pp.width (120 : Nat) |>.set `pp.universes true) do
    return (← ppExpr expression).pretty

/-- Serialize the actual term and its inferred type under the complete local
context. The closed term is also inferred, preventing dangling local references.
These are diagnostic renderings; the owning checked declaration is authoritative. -/
private def applicationRecord (address : List String) (application : Expr)
    (selection : Selection) (proofObjectHeads : List Name) : MetaM Json := do
  let selected ← match selection with
    | .application => pure application
    | .lastArgument =>
      let some last := application.getAppArgs.back?
        | throwError "proof-account: selected application has no argument"
      pure last
  let selectedType ← inferType selected
  unless (← isProp selectedType) ||
      ((← whnf selectedType).getAppFn.constName?).any proofObjectHeads.contains do
    throwError "proof-account: selected argument is data, not a proof or registered proof object"
  let mut context := #[]
  let mut variables := #[]
  for declaration in ← getLCtx do
    variables := variables.push declaration.toExpr
    let value ← match declaration.value? with
      | none => pure Json.null
      | some value => do pure (toJson (← render value))
    context := context.push <| Json.mkObj [
      ("name", toJson declaration.userName.toString),
      ("type", toJson (← render declaration.type)),
      ("value", value)]
  let closed ← mkLambdaFVars variables selected
  let closedType ← inferType closed
  if closed.hasFVar || closedType.hasFVar || closed.hasMVar || closedType.hasMVar then
    throwError "proof-account: selected proof is not closed over its context"
  return Json.mkObj [
    ("address", toJson address), ("context", Json.arr context),
    ("application", toJson (← render application)),
    ("term", toJson (← render selected)),
    ("type", toJson (← render (← inferType selected))),
    ("closed_type", toJson (← render closedType)),
    ("dependencies", toJson (closed.getUsedConstants.toList.map Name.toString))]

private def argumentsMatch (application : Expr) (bindings : List ArgumentBinding) : MetaM Bool := do
  if bindings.isEmpty then return true
  let info ← getConstInfo application.getAppFn.constName!
  let names ← forallTelescope info.type fun binders _ => binders.mapM fun binder => do
    return (← binder.fvarId!.getDecl).userName
  for binding in bindings do
    let some index := names.toList.idxOf? binding.parameter
      | throwError "proof-account: unknown application parameter: {binding.parameter}"
    let some actual := application.getAppArgs[index]?
      | throwError "proof-account: application is missing a selected parameter"
    let expected ← match binding.value with
      | .declaration name => mkConstWithFreshMVarLevels name
      | .natural value => pure (mkNatLit value)
      | .binder name =>
        let some declaration := (← getLCtx).findFromUserName? name
          | throwError "proof-account: missing local binder: {name}"
        pure declaration.toExpr
    unless ← withTransparency .all (isDefEq actual expected) do return false
  return true

/-- Visit maximal applications, entering lambda/forall/let contexts rather than
printing or inferring expressions with loose bound variables. -/
partial def applications (expression : Expr) (callee : Name) (selection : Selection)
    (proofObjectHeads : List Name := [])
    (bindings : List ArgumentBinding := [])
    (address : List String := []) : MetaM (Array Json) := do
  -- A reference occurring only in a type is not a discharge application.
  if ← isType expression then return #[]
  let mut records := #[]
  if expression.getAppFn.constName? == some callee then
    if ← argumentsMatch expression bindings then
      records := records.push (← applicationRecord address expression selection proofObjectHeads)
  match expression with
  | .app .. =>
    for index in [:expression.getAppArgs.size] do
      records := records ++ (← applications expression.getAppArgs[index]! callee selection proofObjectHeads bindings
        (address ++ ["argument", toString index]))
    -- The head can itself be a lambda or a let-expression.
    if !expression.getAppFn.isConst then
      records := records ++ (← applications expression.getAppFn callee selection proofObjectHeads bindings (address ++ ["head"]))
  | .lam name type body info =>
    records := records ++ (← withLocalDecl name info type fun value =>
      applications (body.instantiate1 value) callee selection proofObjectHeads bindings (address ++ ["body"]))
  | .letE name type value body _ =>
    records := records ++ (← applications value callee selection proofObjectHeads bindings (address ++ ["let-value"]))
    records := records ++ (← withLetDecl name type value fun bound =>
      applications (body.instantiate1 bound) callee selection proofObjectHeads bindings (address ++ ["let-body"]))
  | .mdata _ body =>
    records := records ++ (← applications body callee selection proofObjectHeads bindings (address ++ ["metadata"]))
  | .proj _ index body =>
    records := records ++ (← applications body callee selection proofObjectHeads bindings (address ++ ["projection", toString index]))
  | _ => pure ()
  return records

def account (graph : Reachability) (checkpoint : Checkpoint) : MetaM Json := do
  let path ← graph.require checkpoint.owner
  let env := (← getEnv).setExporting false
  let mut pending := [checkpoint.owner]
  let mut seen : NameSet := {}
  let mut uses := #[]
  let mut count := 0
  while !pending.isEmpty do
    let holder := pending.head!
    pending := pending.tail!
    if seen.contains holder then continue
    seen := seen.insert holder
    let some info := env.find? holder
      | throwError "proof-account: missing owner: {holder}"
    let some value := info.value? (allowOpaque := true)
      | throwError "proof-account: unavailable proof body: {holder}"
    let found ← applications value checkpoint.callee checkpoint.selection checkpoint.proofObjectHeads checkpoint.arguments
    count := count + found.size
    if !found.isEmpty then
      uses := uses.push <| Json.mkObj [
        ("declaration", toJson holder.toString),
        ("root_path", toJson ((← graph.require holder).map Name.toString)),
        ("uses", Json.arr found)]
    -- Lean extracts inline proofs into owner-qualified auxiliary declarations.
    -- Follow only reached auxiliaries of this owner, not arbitrary library bodies.
    for dependency in value.getUsedConstants do
      if checkpoint.owner.isPrefixOf dependency then pending := dependency :: pending
  if uses.isEmpty then
    throwError "proof-account: missing application of {checkpoint.callee} in {checkpoint.owner}"
  if let some expected := checkpoint.expectedUses then
    unless count == expected do
      throwError "proof-account: expected {expected} applications, found {count}"
  return Json.mkObj [
    ("id", toJson checkpoint.identifier), ("phase", toJson checkpoint.phase),
    ("expected_layer", toJson checkpoint.responsibility),
    ("route", toJson checkpoint.route.label),
    ("proof_status", "checked-application"),
    ("owner", toJson checkpoint.owner.toString), ("callee", toJson checkpoint.callee.toString),
    ("root_path", toJson (path.map Name.toString)), ("applications", Json.arr uses)]

end ZkcTools.ProofAccount
