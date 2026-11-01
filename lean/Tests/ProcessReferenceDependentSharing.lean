import ZkcExamples.Structured.GkrGateCompanion
import ZkcTools.StructuredSource.ProcessReference
import Lean.Meta.Check

/-! A bounded dependent-index sharing gate. The source is the retained typed
GKR value helper, with its complete named row, actual BodyIn association and
linked dependency table. The wrapper keeps missing inputs and stopped outcomes.
This is a Lean fixture, not a native GKR performance benchmark. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Tests.ProcessReferenceDependentSharing
open Zkc.Source Zkc.Source.Structured
open ZkcExamples.Structured GkrGateGoals

/-- A complete optional source row, with two separate stopping controls. -/
def source (model : DomainModel) (definitions : List CheckedDefinition)
    (input : Option (Value.Inputs.View model.Value)) (stop : Option Bool) :
    PIR.Process closedInterface (Values model.Value GkrSourceBodies.helper31Helper.outputs) :=
  match stop, input with
  | none, _ => .halt .incomplete
  | some true, _ => .halt .reject
  | some false, none => .halt .incomplete
  | some false, some arguments => Structured.invoke
      (definitions.foldl (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
      GkrSourceBodies.helper31Helper (Value.Inputs.pack arguments)

def reference (model : DomainModel)
    (input : Option (Value.Inputs.View model.Value)) (stop : Option Bool) :
    PIR.Process closedInterface (Values model.Value GkrSourceBodies.helper31Helper.outputs) :=
  match stop, input with
  | none, _ => .halt .incomplete
  | some true, _ => .halt .reject
  | some false, none => .halt .incomplete
  | some false, some arguments => .done (.cons
      (Zkc.Protocols.AlgebraicRounds.Gate.value arguments.addWeight arguments.mulWeight
        arguments.left arguments.right) .nil)

/-- An applicability premise remains on the whole equation, including stops. -/
def admittedSource (model : DomainModel) (definitions : List CheckedDefinition)
    (permit : Bool) (input : Option (Value.Inputs.View model.Value)) (stop : Option Bool) :
    PIR.Process closedInterface (Values model.Value GkrSourceBodies.helper31Helper.outputs) :=
  if permit then source model definitions input stop else .halt .refused

/-- This checked theorem retains actual source selection and dependency linking.
Every placement below uses this complete equation, rather than a row type alias. -/
theorem installed (model : DomainModel) (definitions : List CheckedDefinition)
    (linked : DeclarationsLinked [] definitions)
    (associated : BodyIn definitions GkrSourceBodies.helper31Helper Value.body)
    (permit : Bool) (applicable : permit = true)
    (input : Option (Value.Inputs.View model.Value)) (stop : Option Bool) :
    admittedSource model definitions permit input stop = reference model input stop := by
  subst permit
  cases stop with
  | none => rfl
  | some stop => cases stop with
    | true => rfl
    | false => cases input with
      | none => rfl
      | some arguments =>
        exact (GkrGateCompanion.valueLaw model).invoke (helper := GkrSourceBodies.helper31Helper) definitions linked associated
          (Value.Inputs.pack arguments) trivial

source_reference checked from_equation @installed using []

/-- Each syntactic placement has the same complete result index. -/
def placements {α : Type} (count : Nat) (process : PIR.Process closedInterface α) :
    PIR.Process closedInterface α :=
  match count with
  | 0 => process
  | 1 => process
  | n + 2 => process.bind fun _ => placements (n + 1) process

-- Complete branches: missing control, rejection, missing row and returned row.
example (model : DomainModel) (input : Option (Value.Inputs.View model.Value)) :
    reference model input none = .halt .incomplete := rfl
example (model : DomainModel) (input : Option (Value.Inputs.View model.Value)) :
    reference model input (some true) = .halt .reject := rfl
example (model : DomainModel) :
    reference model none (some false) = .halt .incomplete := rfl
example (model : DomainModel) (arguments : Value.Inputs.View model.Value) :
    reference model (some arguments) (some false) = .done (.cons
      (Zkc.Protocols.AlgebraicRounds.Gate.value arguments.addWeight arguments.mulWeight
        arguments.left arguments.right) .nil) := rfl

/-- Equal field types do not authorize reversing the ordered weights. -/
theorem reordered_refused :
    reference (ringModel Int Int) (some ⟨2, 3, 5, 7⟩) (some false) ≠
      reference (ringModel Int Int) (some ⟨3, 2, 5, 7⟩) (some false) := by
  intro wrong
  have same := congrArg (fun row => row.get .here) (PIR.Process.done.inj wrong)
  norm_num [reference, Zkc.Protocols.AlgebraicRounds.Gate.value] at same

/-- Without applicability the equation is false, even on a stopped row. -/
theorem missing_applicability_refused (model : DomainModel)
    (definitions : List CheckedDefinition) :
    admittedSource model definitions false none none ≠ reference model none none := by
  intro wrong
  cases wrong

/-- Count theorem constants in the expression tree, including repeated edges.
The allocated-object count is measured separately by the private cost harness. -/
private def theoremUses : Lean.Expr → Nat
  | .const name _ => if name == ``installed then 1 else 0
  | .app f a => theoremUses f + theoremUses a
  | .lam _ t b _ | .forallE _ t b _ => theoremUses t + theoremUses b
  | .letE _ t v b _ => theoremUses t + theoremUses v + theoremUses b
  | .mdata _ b | .proj _ _ b => theoremUses b
  | _ => 0

open Lean Elab Command Term Meta in
run_cmd liftTermElabM do
  let law ← getConstInfo ``installed
  unless ← isDefEq law.type (← getConstInfo ``checked_equation).type do
    throwError "generated equation changed a source/dependency/applicability premise"
  forallTelescopeReducing law.type fun parameters conclusion => do
    let some (_, left, right) := conclusion.eq? | throwError "expected complete equation"
    let application := mkAppN (mkConst ``installed) parameters
    let lawSyntax ← Term.exprToSyntax application
    let leftSyntax ← Term.exprToSyntax left
    for count in [1, 2, 4] do
      let numeral := Syntax.mkNumLit (toString count)
      let original ← mkAppM ``placements #[mkNatLit count, left]
      let target ← mkAppM ``placements #[mkNatLit count, right]
      let processType ← inferType left
      let binder ← withLocalDeclD `first processType fun first => do
        withLocalDeclD `rest processType fun rest => do
          -- The ignored result has the source's complete dependent output type.
          let resultType := processType.getAppArgs.back!
          let continuation ← withLocalDeclD `ignored resultType fun ignored =>
            mkLambdaFVars #[ignored] rest
          mkLambdaFVars #[first, rest] (← mkAppM ``PIR.Process.bind #[first, continuation])
      let mut directProof := application
      for _ in [:count - 1] do
        directProof ← mkAppM ``congrArg₂ #[binder, application, directProof]
      let predicate ← withLocalDeclD `result processType fun result => do
        mkLambdaFVars #[result] (← mkEq original result)
      let direct ← mkAppOptM ``Subtype.mk #[some processType, some predicate,
        some target, some directProof]
      let generated ← withoutErrToSorry <| elabTerm
        (← `(term| checked_process_reference% (placements $numeral $leftSyntax)
          using [placements, $lawSyntax])) none
      synthesizeSyntheticMVarsNoPostponing
      let generated ← instantiateMVars generated
      unless generated.isAppOf ``Subtype.mk do throwError "expected complete certificate"
      let runtime := generated.getAppArgs[2]!
      if runtime.getUsedConstants.contains ``admittedSource ||
          runtime.getUsedConstants.contains ``source then
        throwError "generated value still contains the source invocation"
      for (method, expression) in [("direct", direct), ("generated", generated)] do
        let expression ← mkLambdaFVars parameters expression
        if expression.hasSorry || expression.hasMVar then throwError "unfinished certificate"
        checkWithKernel expression
        unless expression.getUsedConstants.contains ``installed do
          throwError "{method}/{count} does not share the complete installed theorem"
        unless theoremUses expression == count do
          throwError "{method}/{count} has {theoremUses expression} installed theorem uses"
      unless ← isDefEq (← inferType direct) (← inferType generated) do
        throwError "comparison changed the complete source goal at {count} placements"

#print axioms installed
#print axioms checked_equation
end Tests.ProcessReferenceDependentSharing
