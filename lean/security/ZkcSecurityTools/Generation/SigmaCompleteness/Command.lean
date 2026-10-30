module

public meta import ZkcSecurityTools.Generation.SigmaCompleteness

@[expose] public section
namespace ZkcSecurity.Generation.SigmaCompleteness

/-- Materialize candidate source from the actual admitted Subject metadata.
Only subsequent checking of the output supplies proof or canonical evidence. -/
syntax (name := generateSigmaCompleteness) "derive_sigma_completeness " ident " from " term : command

@[command_elab generateSigmaCompleteness] meta unsafe def elaborateCompleteness : Lean.Elab.Command.CommandElab
  | `(derive_sigma_completeness $name:ident from $input:term) => do
    let data ← Lean.Elab.Command.liftTermElabM do
      let expression ← Lean.Elab.Term.elabTerm input (some (Lean.mkConst ``Input))
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let reduced ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce (← Lean.instantiateMVars expression)
      Lean.Meta.evalExpr Input (Lean.mkConst ``Input) reduced
    match source data with
    | .error reason => Lean.throwError m!"Sigma assembly refused: {reason}"
    | .ok text => Lean.Elab.Command.elabCommand (← `(def $name : String := $(Lean.quote text)))
  | _ => Lean.Elab.throwUnsupportedSyntax

end ZkcSecurity.Generation.SigmaCompleteness
