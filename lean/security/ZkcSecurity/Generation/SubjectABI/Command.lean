module

public meta import ZkcSecurity.Generation.SubjectABI

@[expose] public section
namespace ZkcSecurity.Generation.SubjectABI

/-- Evaluate the printer by kernel reduction of the selected Subject's data.
The command defines printer output data without writing files during elaboration.
This also supports noncomputable Subjects: no executable instance of a proof
record is required, and no root solution is imported by the generated view. -/
syntax (name := generateSubjectABI) "derive_subject_abi " ident " for " term " module " str
    " from " str : command

@[command_elab generateSubjectABI] meta unsafe def elaborateSubjectABI : Lean.Elab.Command.CommandElab
  | `(derive_subject_abi $name:ident for $subject:term module $outputModule:str from $subjectModule:str) => do
    let data ← Lean.Elab.Command.liftTermElabM do
      let term ← `(metadata $subject)
      let expression ← Lean.Elab.Term.elabTerm term none
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let reduced ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce (← Lean.instantiateMVars expression)
      Lean.Meta.evalExpr Metadata (Lean.mkConst ``Metadata) reduced
    let result := source data { moduleName := outputModule.getString, subjectModule := subjectModule.getString }
    match result with
    | .error reason => Lean.throwError m!"subject ABI generation refused: {reason}"
    | .ok text =>
        Lean.Elab.Command.elabCommand (← `(def $name : String := $(Lean.quote text)))
  | _ => Lean.Elab.throwUnsupportedSyntax


end ZkcSecurity.Generation.SubjectABI
