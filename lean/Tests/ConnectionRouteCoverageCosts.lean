import Tests.ConnectionRouteCoverageRoots
import Lean.Meta.Check
import Lean.Util.NumObjs
import Lean.Elab.Tactic

/-! Narrow warm costs of installing produced facts on already checked roots.
This excludes root certificate proposal, generic theorem checking and imports.
Pointer memoization is diagnostic only; all measured terms are kernel checked. -/
open Lean Elab Command Term Meta
public meta section

private unsafe def countTree (expression : Expr) : StateM (PtrMap Expr Nat) Nat := do
  if let some count := (← get).find? expression then return count
  let count ← match expression with
    | .app function argument => return 1 + (← countTree function) + (← countTree argument)
    | .lam _ type body _ | .forallE _ type body _ => return 1 + (← countTree type) + (← countTree body)
    | .letE _ type value body _ => return 1 + (← countTree type) + (← countTree value) + (← countTree body)
    | .mdata _ body | .proj _ _ body => return 1 + (← countTree body)
    | _ => pure 1
  modify (·.insert expression count)
  return count

private def treeNodes (expression : Expr) : IO Nat :=
  return unsafe (countTree expression).run' mkPtrMap

run_cmd liftTermElabM do
  for repetition in [:3] do
    for root in [``ZkcExamples.Structured.Generated.Connections.SchnorrRandomized.producer,
        ``ZkcExamples.Structured.Generated.Connections.SchnorrRandomized.validator,
        ``ZkcExamples.Structured.Generated.Connections.BatchOpening.producer,
        ``ZkcExamples.Structured.Generated.Connections.BatchOpening.validator] do
      for method in [``Zkc.Construction.ConnectionRoot.RootCertificate.simulation,
          ``Zkc.Construction.ConnectionRoot.RootCertificate.routeCoverage,
          ``Zkc.Construction.ConnectionRoot.RootCertificate.facts] do
        let start ← IO.monoNanosNow
        let expression ← mkAppM method #[mkConst root]
        let expression ← instantiateMVars expression
        Meta.check expression
        let proposed ← IO.monoNanosNow
        if expression.hasSorry || expression.hasMVar then throwError "unfinished root facts"
        Meta.checkWithKernel expression
        let checked ← IO.monoNanosNow
        let tree ← treeNodes expression
        let allocated ← expression.numObjs
        let rootArguments := expression.getAppArgs.filter (·.isConstOf root)
        let containsDerivation := expression.find? fun term => match term with
          | .const name _ => (``Zkc.Construction.ConnectionCertificate.Derivation).isPrefixOf name
          | _ => false
        logInfo m!"{root}: method={method}; repetition={repetition}; assembly_ns={proposed-start}; kernel_ns={checked-proposed}; expression_tree_nodes={tree}; allocated_expr_objects={allocated}; root_certificate_arguments={rootArguments.size}; contains_new_derivation_constructor={containsDerivation.isSome}"
