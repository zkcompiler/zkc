module

public import Zkc.Construction.RetainedTarget
public import Zkc.Source.Structured.ContractElaboration
public meta import Lean.Elab.Tactic

@[expose] public section

/-! Recover the fixed target of a compiled Entry from its retained clause.
Only source metadata and policy compatibility are constructed. The formula's
mathematical interpretation and every execution or security law remain separate.
-/

namespace Zkc.Construction
open Zkc.Source.Structured

/-- Bind only a retained helper or the exact result of the fixed registry.
Unsupported or missing entries cannot be synthesized as arbitrary predicates. -/
elab "bind_retained_meaning" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic|
  first
    | exact .formula (by bind_contract)
    | apply RelationMeaning.opaque
      exact (OpaqueRegistry.resolve _ _).get (by kernel_rfl)))

/-- Bind one uniquely named retained target. Missing or ambiguous clauses,
unsupported selectors, residual targets and incompatible policies fail in the
kernel-checked fields of `RetainedTarget`; there is no default target. -/
elab "bind_target " name:str : tactic => Lean.Elab.Tactic.withMainContext do
  let target ← Lean.Meta.whnf (← Lean.Elab.Tactic.getMainTarget)
  unless target.getAppFn.constName? == some ``RetainedTarget do
    Lean.throwError "bind_target: expected RetainedTarget"
  let arguments := target.getAppArgs
  unless arguments.size == 4 do
    Lean.throwError "bind_target: unexpected RetainedTarget parameters"
  let imported ← Lean.Elab.Term.exprToSyntax arguments[1]!
  let term ← `(let owner : ContractBinding $imported := by bind_contract
               let clauseIndex := owner.namedClause $name
               let application : ApplicationBinding owner (owner.clause clauseIndex).subject :=
                 by bind_contract
               { owner := owner
                 entry := by rfl
                 clauseIndex := clauseIndex
                 target := by rfl
                 noResidual := by rfl
                 decision := by decide +kernel
                 application := application
                 booleanOutput := by rfl
                 publicTypes := by decide +kernel
                 publicArity := by decide +kernel
                 supported := by decide +kernel })
  let generated ← Lean.Elab.Term.elabTermEnsuringType term target
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  (← Lean.Elab.Tactic.getMainGoal).assign (← Lean.instantiateMVars generated)
  Lean.Elab.Tactic.replaceMainGoal []

end Zkc.Construction
