module

public import Zkc.Source.Structured.NormalizedRoot
public meta import Zkc.Source.KernelRfl

public meta section
open Lean Elab Tactic

/-- Propose only a checked normal form, never a source-layout equality premise.
All fields are checked by the kernel and ordinary finite normalizer. -/
elab "derive_normalized_source_root" : tactic => withMainContext do
  let target ← Lean.instantiateMVars (← getMainTarget)
  let some target ← Lean.Meta.whnfUntil target ``Zkc.Source.Structured.NormalizedRoot.CheckedOn
    | throwError "expected a checked source normal form"
  unless target.isAppOf ``Zkc.Source.Structured.NormalizedRoot.CheckedOn do
    throwError "expected a checked source normal form"
  let arguments := target.getAppArgs
  let program ← Lean.Elab.Term.exprToSyntax arguments[0]!
  let role ← Lean.Elab.Term.exprToSyntax arguments[1]!
  let signature ← Lean.Elab.Term.exprToSyntax arguments[2]!
  let inputPattern ← Lean.Elab.Term.exprToSyntax arguments[3]!
  evalTactic (← `(tactic| exact {
    form := (Zkc.Source.Structured.NormalForm.normalize $signature ($program).payload.entry.body
      $role ($program).payload.entry.roles.length
      ($inputPattern)).toOption.get (by decide +kernel)
    normalized := by kernel_rfl
    matched := by kernel_rfl
    visible := by decide +kernel
    distinct := by intro index _ different; exact different
  }))
