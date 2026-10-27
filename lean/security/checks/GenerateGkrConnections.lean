import ZkcSecurity.Generation.GkrConnections
import ZkcSecurity.Realizations.Gkr.LayoutVariant

/-! One focused owner for the registered full GKR structural installation.
The source and artifact descriptors are evaluated only to propose syntax;
every generated view equation and connection is independently kernel checked. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 32000000
open ZkcSecurity.Generation
open ZkcSecurity.Realizations.Gkr

private meta def require {α : Type} : Except String α → Lean.Elab.Command.CommandElabM α
  | .ok value => pure value
  | .error reason => Lean.throwError reason

run_cmd do
  let configurations ← Lean.Elab.Command.liftTermElabM do
    let term ← `(show List GkrConnections.Installation from [
      { provenance := .canonicalExport
        modulePrefix := "ZkcSecurity.Realizations.Gkr"
        pairModule := "ZkcSecurity.Realizations.Gkr.CanonicalPair"
        producerExpression := "ZkcSecurity.Realizations.Gkr.CanonicalPair.Producer.participant"
        validatorExpression := "ZkcSecurity.Realizations.Gkr.CanonicalPair.Validator.participant"
        producer := CanonicalPair.Producer.participant
        validator := CanonicalPair.Validator.participant
        producerOrder := List.range CanonicalPair.Producer.participant.inputs.length
        validatorOrder := List.range CanonicalPair.Validator.participant.inputs.length },
      { provenance := .formalLayoutPerturbation
        modulePrefix := "ZkcSecurity.Realizations.Gkr.Rebound"
        pairModule := "ZkcSecurity.Realizations.Gkr.LayoutVariant"
        producerExpression := "ZkcSecurity.Realizations.Gkr.LayoutVariant.producer"
        validatorExpression := "ZkcSecurity.Realizations.Gkr.LayoutVariant.validator"
        producer := LayoutVariant.producer
        validator := LayoutVariant.validator
        producerOrder := LayoutVariant.producerOrder
        validatorOrder := LayoutVariant.validatorOrder }])
    let expression ← Lean.Elab.Term.elabTerm term none
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let expression ← Lean.Meta.withTransparency .all <|
      Lean.Meta.reduce (← Lean.instantiateMVars expression)
    Lean.Meta.evalExpr (List GkrConnections.Installation)
      (Lean.mkApp (Lean.mkConst ``List [Lean.Level.zero]) (Lean.mkConst ``GkrConnections.Installation)) expression
  let mut sources := []
  let mut descriptions := []
  for installation in configurations do
    sources := sources ++ (← require (GkrConnections.sources installation))
    descriptions := descriptions ++ [← require (GkrConnections.describe installation)]
  Lean.Elab.Command.elabCommand (← `(def $(Lean.mkIdent `sources) : List (String × String) := $(Lean.quote sources)))

  let descriptionText := (Lean.Json.arr descriptions.toArray).pretty
  Lean.Elab.Command.elabCommand (← `(def $(Lean.mkIdent `descriptions) : String := $(Lean.quote descriptionText)))

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected output directory")
  IO.FS.createDirAll directory
  IO.FS.writeFile (System.FilePath.mk directory / "descriptors.json") descriptions
  for (name, source) in sources do
    let path := System.FilePath.mk directory / (name.replace "." "/" ++ ".lean")
    IO.FS.createDirAll path.parent.get!
    IO.FS.writeFile path source
    IO.println s!"generated {name}"
