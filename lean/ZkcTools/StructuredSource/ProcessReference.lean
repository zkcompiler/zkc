module

public meta import ZkcTools.Generation.Commands
public meta import ZkcTools.StructuredSource.Composition
public meta import ZkcTools.StructuredSource.ReferenceRules
public meta import Lean.Elab.Command
public meta import Lean.Elab.Term
public meta import Lean.Meta.Tactic.Simp.Main
public meta import Lean.Meta.Transform
public import Zkc.Semantics.Interaction

public meta section

/-! A readable process reference and its equation are produced together from
an existing process and explicitly selected laws. The simplifier constructs the
equation; it is not an execution oracle. No global simp set or companion search
can change the selected source or omit an output, effect, or stopped branch. -/
namespace ZkcTools.StructuredSource.ProcessReference
open Lean Meta Elab Term

-- The selected source form and mathematical laws remain explicit. This set
-- only removes the common typed normal-form plumbing when requested.
attribute [zkc_source_structure]
  Zkc.Source.Structured.NormalForm.Form.denoteOn
  Zkc.Source.Structured.NormalForm.Form.denoteWithOn
  Zkc.Source.Structured.NormalForm.Comps.eval
  Zkc.Source.Structured.NormalForm.Comp.eval
  Zkc.Source.Structured.NormalForm.Term.eval
  Zkc.Source.Structured.NormalForm.Terms.eval
  Zkc.Source.Structured.NormalForm.entryAt
  Zkc.Source.Structured.NormalForm.firstEntry
  Zkc.Source.Structured.NormalForm.laterEntries
  Zkc.Source.Structured.NormalForm.Arguments.eval
  Zkc.Source.Structured.NormalForm.Argument.eval
  Zkc.Source.Structured.ProtocolPresentation.callees
  Zkc.Source.Structured.NormalForm.calleeAt
  Zkc.Source.Structured.NormalForm.InputPattern.environment
  Zkc.Source.Structured.Bindings.optionalPattern
  Zkc.Source.Structured.Op.evalTotal
  Zkc.Source.Values.get

private def rewriteContext (laws : Array (TSyntax `term)) : TermElabM Simp.Context := do
  let mut theorems : SimpTheorems := {}
  let mut selectedSets : Array SimpTheorems := #[]
  for law in laws do
    if law.raw.isIdent then
      if let some extension ← getSimpExtension? law.raw.getId then
        selectedSets := selectedSets.push (← extension.getTheorems)
        continue
      let name ← resolveGlobalConstNoOverload law
      let info ← getConstInfo name
      -- Public module imports need not expose a theorem's stored proof body.
      -- Classify its type, not the particular ConstantInfo constructor.
      theorems ← if ← isProp info.type then theorems.addConst name
        else theorems.addDeclToUnfold name
    else
      let proof ← elabTerm law none
      synthesizeSyntheticMVarsNoPostponing
      let proof ← instantiateMVars proof
      if proof.hasExprMVar then
        throwError "process reference law leaves unresolved arguments"
      theorems ← theorems.add (.stx (← mkFreshId) law) #[] proof
  Simp.mkContext (simpTheorems := #[theorems] ++ selectedSets)

/-- Reduce source row access beneath dependent applications and optional
branches. Ordinary simp intentionally avoids some dependent arguments. These
reductions use only typed row evaluators and descriptor projections, never a
helper's implementation or a callee's process. The resulting equation is checked by definitional
equality, including the complete dependent indices. -/
private def compactRowArguments (expression : Expr) : MetaM Expr :=
  Meta.transform expression (pre := fun expression => do
    if expression.isForall || expression.isSort then return .done expression
    let evaluators := #[``Zkc.Source.Structured.NormalForm.Arguments.eval,
      ``Zkc.Source.Structured.NormalForm.Argument.eval,
      ``Zkc.Source.Structured.NormalForm.Comps.eval,
      ``Zkc.Source.Structured.NormalForm.Comp.eval,
      ``Zkc.Source.Structured.NormalForm.Terms.eval,
      ``Zkc.Source.Structured.NormalForm.Term.eval,
      ``Zkc.Source.Structured.NormalForm.entryAt,
      ``Zkc.Source.Structured.NormalForm.firstEntry,
      ``Zkc.Source.Structured.NormalForm.laterEntries,
      ``Zkc.Source.Structured.NormalForm.InputPattern.environment,
      ``Zkc.Source.Values.get,
      ``Zkc.Source.Structured.NormalForm.CalleeKey.signature,
      ``Zkc.Source.Structured.NormalForm.CalleeKey.role,
      ``Zkc.Source.Structured.ProtocolSignature.inputs,
      ``Zkc.Source.Structured.ProtocolSignature.outputs]
    if evaluators.any expression.isAppOf then
      let reduced ← withTransparency .default <| whnf expression
      if reduced != expression then return .visit reduced
    return .continue) (skipConstInApp := true)

elab "checked_process_reference% " source:term " using " "[" laws:term,* "]" : term => do
  withoutErrToSorry do
    let original ← elabTerm source none
    synthesizeSyntheticMVarsNoPostponing
    let original ← instantiateMVars original
    let originalType ← inferType original
    let context ← rewriteContext laws.getElems
    let (reference, proof) ← forallTelescopeReducing originalType fun parameters resultType => do
      unless resultType.isAppOf ``PIR.Process do
        throwError "process reference requires a process or a function returning a process"
      let application := mkAppN original parameters
      let (result, _) ← Meta.simp application context
      let body ← compactRowArguments result.expr
      let mut proof ← result.getProof' application
      for parameter in parameters.reverse do
        proof ← mkAppM ``funext #[← mkLambdaFVars #[parameter] proof]
      return (← mkLambdaFVars parameters body, proof)
    let predicate ← withLocalDeclD `reference originalType fun reference => do
      mkLambdaFVars #[reference] (← mkEq original reference)
    let value ← mkAppOptM ``Subtype.mk #[some originalType, some predicate,
      some reference, some proof]
    if value.hasExprMVar then
      throwError "process reference leaves unresolved mathematical arguments"
    return value

elab "process_reference_value% " certificate:term:max " against " source:term : term => do
  let original ← elabTerm source none
  synthesizeSyntheticMVarsNoPostponing
  let original ← instantiateMVars original
  let type ← inferType original
  let predicate ← withLocalDeclD `reference type fun reference => do
    mkLambdaFVars #[reference] (← mkEq original reference)
  let expected ← mkAppM ``Subtype #[predicate]
  let checked ← elabTermEnsuringType certificate expected
  return ← mkAppM ``Subtype.val #[checked]

/-- Reuse an existing checked source equation. Its full telescope stays on the
correspondence theorem. Only parameters unused by the process are omitted from
the generated value; in particular, applicability proofs do not become runtime
arguments. No premise is discharged or removed from the equation. -/
syntax (name := checkedProcessEquation) "checked_process_equation% " term " using " "[" term,* "]"
  (" atoms " "[" ident,* "]")? : term

elab_rules : term
  | `(checked_process_equation% $equation:term using [$laws:term,*]
      $[atoms [$atomNames:ident,*]]?) => withoutErrToSorry do
    let original ← elabTerm equation none
    synthesizeSyntheticMVarsNoPostponing
    let original ← instantiateMVars original
    let context ← rewriteContext laws.getElems
    forallTelescopeReducing (← inferType original) fun parameters conclusion => do
      let some (_, left, right) := conclusion.eq? |
        throwError "process equation requires an equality theorem"
      unless (← whnf (← inferType right)).isAppOf ``PIR.Process do
        throwError "process equation must retain a complete process"
      let (rewritten, _) ← Meta.simp right context
      let compacted ← compactRowArguments rewritten.expr
      let (referenceBody, refinement) ← match atomNames with
        | none => pure (compacted, ← mkEqRefl compacted)
        | some atomNames =>
            ZkcTools.StructuredSource.Composition.checkedPresentation
              (← atomNames.getElems.mapM resolveGlobalConstNoOverload) compacted
      let correspondence ← mkAppM ``Eq.trans #[← rewritten.getProof' right, refinement]
      let (_, used) ← (do
        referenceBody.collectFVars
        get >>= (·.addDependencies) >>= set
        : StateRefT CollectFVars.State MetaM Unit).run {}
      let selected := parameters.filter fun parameter => used.fvarSet.contains parameter.fvarId!
      let reference ← mkLambdaFVars selected referenceBody
      let referenceType ← inferType reference
      let predicate ← withLocalDeclD `reference referenceType fun reference => do
        let equation ← mkEq left (mkAppN reference selected)
        mkLambdaFVars #[reference] (← mkForallFVars parameters equation)
      let proof ← mkAppM ``Eq.trans #[mkAppN original parameters, correspondence]
      let proof ← mkLambdaFVars parameters proof
      let value ← mkAppOptM ``Subtype.mk #[some referenceType, some predicate, some reference, some proof]
      if value.hasExprMVar then throwError "process equation leaves unresolved mathematical arguments"
      return value

elab "process_equation_value% " certificate:term : term => withoutErrToSorry do
  let certificate ← elabTerm certificate none
  synthesizeSyntheticMVarsNoPostponing
  mkAppM ``Subtype.val #[← instantiateMVars certificate]

elab "process_equation_type% " certificate:term : term => withoutErrToSorry do
  let certificate ← elabTerm certificate none
  synthesizeSyntheticMVarsNoPostponing
  inferType (← mkAppM ``Subtype.property #[← instantiateMVars certificate])

syntax (name := sourceReference) "source_reference " ident " from " term
  " using " "[" term,* "]" : command
syntax (name := sourceEquationReference) "source_reference " ident " from_equation " term
  " using " "[" term,* "]" (" atoms " "[" ident,* "]")? : command

/-- Both commands install their complete interface atomically. The certificate
is shared by the generated value and its ordinary correspondence theorem. -/
@[command_elab sourceReference, command_elab sourceEquationReference]
def elaborateReference : Command.CommandElab := fun stx =>
  ZkcTools.Generation.Commands.atomic "source_reference" do
    let (name, source, laws, fromEquation, atomNames) ← match stx with
      | `(source_reference $name:ident from $source:term using [$laws:term,*]) =>
          pure (name, source, laws, false, none)
      | `(source_reference $name:ident from_equation $source:term using [$laws:term,*]
          $[atoms [$atomNames:ident,*]]?) => pure (name, source, laws, true, atomNames)
      | _ => throwUnsupportedSyntax
    let certificate := mkIdent (name.getId.appendAfter "_certificate")
    let equation := mkIdent (name.getId.appendAfter "_equation")
    if fromEquation then
      Command.elabCommand (← `(command| noncomputable def $certificate :=
        checked_process_equation% $source using [$laws,*] $[atoms [$atomNames,*]]?))
      Command.elabCommand (← `(command| noncomputable abbrev $name := process_equation_value% ($certificate)))
      Command.elabCommand (← `(command| theorem $equation : process_equation_type% ($certificate) :=
        @Subtype.property _ _ ($certificate)))
    else
      Command.elabCommand (← `(command| noncomputable def $certificate :=
        checked_process_reference% $source using [$laws,*]))
      Command.elabCommand (← `(command| noncomputable abbrev $name :=
        process_reference_value% ($certificate) against ($source)))
      Command.elabCommand (← `(command| theorem $equation : $source =
        (process_reference_value% ($certificate) against ($source)) := ($certificate).property))

end ZkcTools.StructuredSource.ProcessReference
