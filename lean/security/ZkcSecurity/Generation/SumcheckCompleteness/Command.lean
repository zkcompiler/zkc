module

public meta import ZkcSecurity.Generation.SumcheckCompleteness

@[expose] public section
namespace ZkcSecurity.Generation.SumcheckCompleteness

/-- Materialize source output from admitted metadata, including noncomputable
subject records. This command creates data only; every emitted theorem must
subsequently pass the kernel and the canonical receipt checks. -/
syntax (name := generateSumcheckCompleteness) "derive_sumcheck_completeness " ident " from " term : command

@[command_elab generateSumcheckCompleteness] meta unsafe def elaborateCompleteness : Lean.Elab.Command.CommandElab
  | `(derive_sumcheck_completeness $name:ident from $input:term) => do
    let data ← Lean.Elab.Command.liftTermElabM do
      let expression ← Lean.Elab.Term.elabTerm input (some (Lean.mkConst ``Input))
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let reduced ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce (← Lean.instantiateMVars expression)
      Lean.Meta.evalExpr Input (Lean.mkConst ``Input) reduced
    match source data with
    | .error reason => Lean.throwError m!"honest assembly generation refused: {reason}"
    | .ok text => Lean.Elab.Command.elabCommand (← `(def $name : String := $(Lean.quote text)))
  | _ => Lean.Elab.throwUnsupportedSyntax

end ZkcSecurity.Generation.SumcheckCompleteness
