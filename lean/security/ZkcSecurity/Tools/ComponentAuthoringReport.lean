module

public import Zkc.Obligations.Derivation
public import Zkc.Source.Structured.NormalForm.Sites
public meta import Lean.Elab.Tactic

@[expose] public meta section

/-! Diagnostics produced by the component proof builder, not a receipt
classifier. Attribution is deliberately outside the kernel term. In particular
changing an attribution cannot upgrade a request-owned property or its status.
Static builder addresses identify proof obligations, never random-oracle keys.
The existing receipt reporting path remains authoritative for checked receipts. -/

namespace ZkcSecurity.Tools.ComponentAuthoringReport
open Lean Meta Elab Tactic

initialize registerTraceClass `zkc.componentAssembly

structure Entry where
  goal : MVarId
  address : List String
  layer : String
  method : String
  proposition : Expr
  body : Expr
  property : Option Expr
  history : Option Expr

def render (expression : Expr) : MetaM String :=
  withOptions (fun options => options.setBool `pp.fullNames true |>.setBool `pp.explicit true
      |>.setBool `pp.proofs true |>.setBool `pp.universes true) do
    return toString (← ppExpr (← instantiateMVars expression))

def capture (goal : MVarId) (address : List String) (layer method : String) : MetaM Entry :=
    goal.withContext do
  let target ← whnf (← instantiateMVars (← goal.getType))
  let body := if target.isAppOf ``Zkc.Obligations.Derivation then
      target.getAppArgs.back! else target
  let arguments := target.getAppArgs
  let property := if target.isAppOf ``Zkc.Obligations.Derivation then
      some arguments[arguments.size - 3]! else none
  let history := if target.isAppOf ``Zkc.Obligations.Derivation then
      some arguments[arguments.size - 2]! else none
  return ⟨goal, address, layer, method, target, body, property, history⟩

def Entry.recordJson (entry : Entry) : MetaM Json := entry.goal.withContext do
  let value ← instantiateMVars (mkMVar entry.goal)
  let pending := value.hasMVar
  let context ← getLCtx
  let localDependencies := ((collectFVars {} value).fvarIds.toList).filterMap fun identifier =>
    (context.find? identifier).map (·.userName.toString)
  let mut declarations := #[]
  for declaration in context do
    unless declaration.isImplementationDetail do
      declarations := declarations.push <| Json.mkObj [
        ("name", toJson declaration.userName.toString),
        ("type", toJson (← render declaration.type)),
        ("value", ← match declaration.value? with
          | none => pure Json.null
          | some value => pure (toJson (← render value)))]
  return Json.mkObj [
    ("address", toJson entry.address), ("responsibility", toJson entry.layer),
    ("method", toJson entry.method),
    ("authoring_status", toJson (if pending then "pending" else "constructed")),
    ("proposition", toJson (← render entry.proposition)), ("selected_body", toJson (← render entry.body)),
    ("property", toJson (← entry.property.mapM render)),
    ("reached_history", toJson (← entry.history.mapM render)),
    ("context", Json.arr declarations),
    ("local_dependencies", toJson localDependencies),
    ("dependencies", toJson (value.getUsedConstants.toList.map Name.toString))]

/-- Reuse the normal form's structural metadata. A selection may pair the form
with its context and binders; inspect only that tuple, never Process execution.
For a symbolic form the exact `sites` expression remains useful author feedback.
This inventory does not pretend that a proof address is a runtime occurrence. -/
partial def selectedFormSites (selection : Expr) : MetaM (Array Json) := do
  let type ← whnf (← inferType selection)
  if type.isAppOf ``Zkc.Source.Structured.NormalForm.Form then
    let sites ← mkAppM ``Zkc.Source.Structured.NormalForm.sites
      #[selection, ← mkListLit (mkConst ``Nat) []]
    return #[Json.mkObj [
      ("form", toJson (← render selection)),
      ("static_sites", toJson (← render (← reduce sites)))]]
  if type.isAppOf ``Prod then
    let selected := selection.consumeMData
    if selected.isAppOf ``Prod.mk then
      let arguments := selected.getAppArgs
      return (← selectedFormSites arguments[arguments.size - 2]!) ++
        (← selectedFormSites arguments[arguments.size - 1]!)
    return (← selectedFormSites (← mkAppM ``Prod.fst #[selection])) ++
      (← selectedFormSites (← mkAppM ``Prod.snd #[selection]))
  return #[]

/-- Detailed expressions and site inventories are rendered only on request.
Normal proof construction retains lightweight expressions, so a disabled trace
never evaluates the selected form merely to print an unused diagnostic. -/
def emit (association : String) (source request : Expr) (entries : Array Entry) : TacticM Unit := do
  unless ← isTracingEnabledFor `zkc.componentAssembly do return
  let report := Json.mkObj [
    ("schema", toJson "zkc.component-authoring/0"),
    ("request_association", toJson association),
    ("requested_type", toJson (← render request)),
    ("source_selection", toJson (← render source)),
    ("source_selection_type", toJson (← render (← inferType source))),
    ("selected_form_sites", Json.arr (← selectedFormSites source)),
    ("address_meaning", toJson "static proof address; not an oracle key"),
    ("status_scope", toJson "authoring only; receipt classifier unchanged"),
    ("obligations", Json.arr (← entries.mapM fun entry => entry.recordJson))]
  trace[zkc.componentAssembly] "{report.compress}"

end ZkcSecurity.Tools.ComponentAuthoringReport
