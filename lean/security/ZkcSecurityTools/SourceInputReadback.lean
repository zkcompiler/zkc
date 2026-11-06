module

public import ZkcSecurity.Bindings.Subjects.HonestPair
public import Zkc.Source.Structured.DomainLinking
public import Zkc.Source.Structured.UnitViews

@[expose] public section

/-! Read each retained input application before interpreting its formula. The
linking theorem relates lookup in the complete table to execution of the selected
body. Materializing that body leaves the mathematical inputs symbolic and avoids
re-evaluating source admission during every operation. -/
set_option autoImplicit false
namespace ZkcSecurity.Tools.SourceInputReadback
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcSecurity.Claims.HonestPair

private theorem read_predicate {A : Type} (read : Option A) (P : A → Prop) :
    (∃ args, read = some args ∧ P args) = read.elim False P := by
  cases read <;> simp

/-- Decide a retained clause by reading its arguments before evaluating its meaning. -/
theorem input_read {model : DomainModel} {original : Snapshot} {imported : Imported original}
    {selected : AuthoredPair.Selection original} (subject : Subject model original imported selected)
    (inputs : subject.Inputs) (index : Fin subject.target.owner.contract.clauses.length)
    (h : (subject.target.owner.clause index).kind = .input) :
    subject.inputClause inputs index h =
      ((subject.inputMeanings index h).binding.read {} (subject.boundary inputs)
        (subject.assignments inputs)).elim False
        ((subject.inputMeanings index h).meaning.HoldsOn (subject.inputMeanings index h).booleanOutput) :=
  read_predicate _ _

/-- Retain the complete checked body at the relation ABI selected by the source. -/
def atSignature (definition : CheckedDefinition) (helper : Helper) (h : definition.helper = helper) :
    Region dialect helper.inputs helper.outputs := h ▸ definition.body

theorem atSignature_raw (definition : CheckedDefinition) (helper : Helper) (h : definition.helper = helper) :
    definition.raw = (atSignature definition helper h).erase := by
  subst helper
  exact definition.exactBody.symm

/-- Execution of a formula is execution of its selected, linked definition. -/
theorem formula_body {source : Snapshot} {imported : Imported source} {application : RelationApplication}
    {relation : RelationBinding source application} (model : DomainModel) (binding : FormulaBinding imported relation)
    (arguments : Values model.Value relation.declaration.inputs) :
    binding.invokeRelationOn model arguments =
      (atSignature binding.definition _ binding.signature_eq).denote
        (Evaluation.meaningOn model SiteObservations.closed (closedMeaningsOn model imported.program.payload.definitions))
        arguments.get :=
  Evaluation.definitions_invoke_body_view_asOn model SiteObservations.closed _ imported.program.payload.linked
    binding.definition (List.get_mem ..) _ binding.signature_eq _ (atSignature_raw ..) arguments

end ZkcSecurity.Tools.SourceInputReadback

@[expose] public meta section
namespace ZkcSecurity.Tools.SourceInputReadback
open Lean Meta Zkc.Source Zkc.Source.Structured ZkcSecurity.Claims.HonestPair

/-- An absent selector fails the clause immediately. An opaque meaning retains
its installed predicate. A formula uses its own admitted helper and arguments. -/
def expandInput (term : Expr) : MetaM Simp.Result := do
  let readLaw := mkAppN (mkConst ``input_read) term.getAppArgs
  let some (_, _, read) := (← inferType readLaw).eq?
    | throwError "source-input-clauses: expected the selector read equation"
  let holdClause := fun _ (declaration : ConstantInfo) => pure (declaration.name != ``RelationMeaning.HoldsOn)
  let truth ← withCanUnfoldPred holdClause <| withTransparency .all <| whnf read
  if !truth.isAppOf ``RelationMeaning.HoldsOn then return { expr := truth, proof? := some readLaw }
  let equation ← withTransparency .all <| whnf truth
  let some (_, call, rhs) := equation.eq? | return { expr := truth, proof? := some readLaw }
  unless call.isAppOf ``FormulaBinding.invokeRelationOn do return { expr := truth, proof? := some readLaw }
  let bodyLaw ← mkAppM ``formula_body (call.getAppArgs.extract (call.getAppNumArgs - 3) call.getAppNumArgs)
  let result ← withLocalDeclD `outcome (← inferType call) fun out => do
    let predicate ← mkLambdaFVars #[out] (← mkEq out rhs)
    mkAppM ``congrArg #[predicate, bodyLaw]
  let some (_, _, presentation) := (← inferType result).eq?
    | throwError "source-input-clauses: expected the formula body equation"
  let some (_, value, target) := presentation.eq?
    | throwError "source-input-clauses: expected a returned-value equation"
  let arguments := value.getAppArgs
  let some position := arguments.findIdx? (·.isAppOf ``atSignature)
    | throwError "source-input-clauses: selected formula body is missing"
  let body ← UnitViews.normalize arguments[position]!
  let actual := mkAppN value.getAppFn (arguments.set! position body)
  return { expr := ← mkEq actual target, proof? := some (← mkEqTrans readLaw result) }

end ZkcSecurity.Tools.SourceInputReadback
