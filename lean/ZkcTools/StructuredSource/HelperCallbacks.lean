module

public import Zkc.Source.Structured.HelperCallbacks
public meta import ZkcTools.Generation.Commands
public meta import Lean.Elab.Command
public meta import Lean.Elab.Term
public meta import Lean.Meta.Reduce

@[expose] public section

/-! `helper_callback name from actualBody` selects a unique actual counted loop
and derives the callback's entire type. `at path` disambiguates occurrences by a
checked structural path. Generated declarations are ordinary Lean constants;
there is no registry, interpretation, or protocol-specific selection rule. -/

public meta section
namespace ZkcTools.StructuredSource.HelperCallbacks
open Lean Meta Elab Command Term
open Zkc.Source Zkc.Source.Structured.HelperCallbacks

/-- Materialize the selected syntax once, rather than asking each downstream
conversion check to redo selection. The command separately proves that this
ordinary declaration is exactly the selected body. -/
elab "selected_callback_body% " selection:term:max : term => withoutErrToSorry do
  let selection ← elabTermEnsuringType selection (mkConst ``Located)
  synthesizeSyntheticMVarsNoPostponing
  let callback ← mkAppM ``Located.callback #[← instantiateMVars selection]
  reduce (← mkAppM ``Callback.body #[callback])

syntax (name := helperCallback) "helper_callback " ident " from " term
  (" at " term)? : command

def generate : CommandElab := fun stx => do
  let `(helper_callback $name:ident from $source:term $[at $path:term]?) := stx
    | throwUnsupportedSyntax
  let path ← match path with
    | none => `(term| (none : Option Path))
    | some path => `(term| (some ($path) : Option Path))
  -- Inspect only to issue a useful refusal. The generated association below
  -- is checked again by the kernel against the original source expression.
  let checkedPath ← liftTermElabM <| withoutErrToSorry do
    let expression ← elabTerm (← `(term| select $source $path)) none
    synthesizeSyntheticMVarsNoPostponing
    let expression ← instantiateMVars expression
    if expression.hasFVar || expression.hasMVar then
      throwError "helper-callback-open-source: instantiate the helper's static parameters first"
    let result ← whnf expression
    if result.isAppOf ``Except.error then
      let failure ← whnf result.getAppArgs.back!
      if failure.isConstOf ``Failure.missing then
        throwError "helper-callback-missing: no counted loop at the requested source/path"
      if failure.isConstOf ``Failure.ambiguous then
        throwError "helper-callback-ambiguous: select an explicit checked path"
      throwError "helper-callback-selection: could not determine selection failure"
    unless result.isAppOf ``Except.ok do
      throwError "helper-callback-selection: source must have statically known loop structure"
    let found := result.getAppArgs.back!
    let actualPath ← reduce (← mkAppM ``Located.path #[found])
    PrettyPrinter.delab actualPath
  let selection := mkIdent (name.getId.appendAfter "_selection")
  let association := mkIdent (name.getId.appendAfter "_association")
  let bodyAssociation := mkIdent (name.getId.appendAfter "_body_association")
  elabCommand (← `(command| def $selection : Located :=
    ⟨$checkedPath, (atPath $source $checkedPath).get (by decide +kernel)⟩))
  elabCommand (← `(command| theorem $association : Selected $source $path $selection := by rfl))
  elabCommand (← `(command| abbrev $name := selected_callback_body% $selection))
  elabCommand (← `(command| theorem $bodyAssociation : $name = ($selection).callback.body := by rfl))

/-- A failed command must not leave a half-installed callback in the environment. -/
@[command_elab helperCallback]
def elabHelperCallback : CommandElab := fun stx =>
  ZkcTools.Generation.Commands.atomic "helper-callback-generation" (generate stx)

end ZkcTools.StructuredSource.HelperCallbacks
