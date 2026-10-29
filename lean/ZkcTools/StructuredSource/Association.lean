module

public import Zkc.Source.Structured.Template
public meta import Lean.Elab.Tactic
public meta import Zkc.Source.KernelRfl

public meta section

/-! Discover the admitted declaration of an already selected mathematical body.
Search proposes only a list position. The generated association separately
checks membership, the entire signature and the actual raw body in the kernel.
No declaration position or source equation is authored at each installation.
-/
set_option autoImplicit false
namespace ZkcTools.StructuredSource.Association
open Lean Meta Elab Tactic
open Zkc.Source Zkc.Source.Structured

private def declarationIndex (payload signature body : Expr) : MetaM Nat := do
  let mut remaining ← mkAppM ``UnitPayload.protocols #[payload]
  let mut index := 0
  repeat
    remaining ← withTransparency .all <| whnf remaining
    if remaining.isAppOf ``List.nil then
      throwError "source association: no admitted declaration has the complete selected signature and body"
    unless remaining.isAppOf ``List.cons do
      throwError "source association: the declaration list is not statically known"
    let arguments := remaining.getAppArgs
    let actual ← mkAppM ``CheckedProtocol.signature #[arguments[1]!]
    let saved ← saveState
    if ← withTransparency .all <| isDefEq actual signature then
      let raw ← mkAppM ``CheckedProtocol.raw #[arguments[1]!]
      let erased ← mkAppM ``Region.erase #[body]
      if ← withTransparency .all <| isDefEq raw erased then
        return index
    saved.restore
    remaining := arguments[2]!
    index := index + 1

/-- A successful proposal returns an ordinary checked Association. Unknown
signatures and mismatched bodies remain explicit proof obligations. -/
elab "derive_source_association" : tactic => withMainContext do
  Term.withoutErrToSorry <| withoutRecover do
    let expected ← instantiateMVars (← getMainTarget)
    unless expected.isAppOf ``Zkc.Source.Structured.Template.Association do
      throwError "derive_source_association: expected a fixed source template association"
    let arguments := expected.getAppArgs
    let payload := arguments[0]!
    let signature := arguments[1]!
    let position ← declarationIndex payload signature arguments[2]!
    let source ← Term.exprToSyntax payload
    let index := Syntax.mkNumLit (toString position)
    evalTactic (← `(tactic|
      refine {
        definition := ($source).protocols[$index]'(by decide +kernel)
        member := List.getElem_mem _
        signature_eq := by kernel_rfl
        body_eq := by kernel_rfl
      }))

/-- Infer only the data witness of a typed template selection. The association
proposer searches the complete signature and body together, so an unconstrained
name cannot authorize a same-ABI replacement. Both resulting fields are kernel
checked. This also supports several templates with identical role/input ABIs. -/
elab "infer_source_template" : tactic => withMainContext do
  Term.withoutErrToSorry <| withoutRecover do
    let pending := (← getGoals).drop 1
    let mut data : List MVarId := []
    for _ in [:16] do
      let expected ← instantiateMVars (← getMainTarget)
      if expected.isAppOf ``Zkc.Source.Structured.Template.Association then
        evalTactic (← `(tactic| derive_source_association))
        for parameter in data do
          if (← instantiateMVars (mkMVar parameter)).hasMVar then
            throwError "infer_source_template: a template parameter remains unassociated"
        setGoals pending
        return
      unless expected.isAppOf ``Sigma do
        throwError "infer_source_template: expected dependent template data followed by an association, got {expected.getAppFn}"
      let fields ← (← getMainGoal).constructor
      let some association ← fields.findM? (fun field => do
        let type ← instantiateMVars (← field.getType)
        return type.isAppOf ``Sigma || type.isAppOf ``Zkc.Source.Structured.Template.Association)
        | throwError "infer_source_template: expected a dependent association field"
      data := fields.filter (· != association) ++ data
      setGoals [association]
    throwError "infer_source_template: template parameter nesting exceeds search depth"

end ZkcTools.StructuredSource.Association
