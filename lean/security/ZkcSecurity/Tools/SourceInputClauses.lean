module

public import ZkcSecurity.Tools.SubjectABI
public meta import Lean.Elab.Tactic

@[expose] public section

/-! Checked presentation of retained source input clauses. Interpretation uses
Lean reduction of the admitted helper table, not a second source evaluator.
The resulting equivalence covers optional values at every source coordinate. -/
set_option autoImplicit false
namespace ZkcSecurity.Tools.SourceInputClauses
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims.HonestPair

/-- Existential rows are split in source order, including repeated sorts. -/
theorem exists_cons {types : List Ty} {type : Ty} {Value : Ty → Type}
    (predicate : Values Value (type :: types) → Prop) :
    (∃ row, predicate row) ↔ ∃ head rest, predicate (.cons head rest) := by
  constructor
  · rintro ⟨row, holds⟩
    cases row with | cons head rest => exact ⟨head, rest, holds⟩
  · rintro ⟨head, rest, holds⟩; exact ⟨.cons head rest, holds⟩

theorem exists_nil {Value : Ty → Type} (predicate : Values Value [] → Prop) :
    (∃ row, predicate row) ↔ predicate .nil := by
  constructor
  · rintro ⟨⟨⟩, holds⟩; exact holds
  · exact fun holds => ⟨.nil, holds⟩

theorem option_elim_constant {α : Type} (value : Option α) (proposition : Prop) :
    value.elim proposition (fun _ => proposition) = proposition := by
  cases value <;> rfl

end ZkcSecurity.Tools.SourceInputClauses

@[expose] public meta section
namespace ZkcSecurity.Tools.SourceInputClauses
open Lean Meta Elab Term Tactic
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims.HonestPair

/-- Keep mathematical leaves visible while reducing the source interpreter. -/
def protectedConstants : List Name :=
  [``Eq, ``HEq, ``And, ``Or, ``Not, ``Exists, ``Iff, ``decide,
   ``Bool.and, ``Bool.or, ``Bool.xor, ``Bool.not,
   ``Nat.lt, ``Nat.le, ``Nat.pow, ``List.length, ``naturalPowerOfTwo]

/-- Normalize dependent binder and constructor types as well as the values.
Otherwise opaque source projections can obstruct constructor injectivity even
when the value expressions have already reduced to mathematical leaves. -/
def exposeRowType (type : Expr) : MetaM Expr :=
  withTransparency .all <| reduce type (skipTypes := false)

partial def reduceSemantics (expression : Expr) : MetaM Expr := do
  if expression.isAppOf ``OfNat.ofNat then return expression
  if (← isProof expression) then return expression
  if (← isType expression) && !(← isProp expression) then return ← exposeRowType expression
  let type ← whnf (← inferType expression)
  let expression ← if type.isConstOf ``Bool || type.isConstOf ``Nat || (← isProp expression) then
    withCanUnfoldPred (fun _ declaration => pure (!protectedConstants.contains declaration.name)) <|
      withTransparency .all <| whnf expression
    else withTransparency .all <| whnf expression
  match expression with
  | .app .. =>
      let mut arguments := expression.getAppArgs
      let info ← getFunInfoNArgs expression.getAppFn arguments.size
      for index in [:arguments.size] do
        if let some parameter := info.paramInfo[index]? then
          if parameter.isInstImplicit then continue
        arguments := arguments.set! index (← reduceSemantics arguments[index]!)
      return mkAppN expression.getAppFn arguments
  | .lam name domain body info =>
      withLocalDecl name info (← exposeRowType domain) fun value => do
        mkLambdaFVars #[value] (← reduceSemantics (body.instantiate1 value))
  | .forallE name domain body info =>
      withLocalDecl name info (← exposeRowType domain) fun value => do
        mkForallFVars #[value] (← reduceSemantics (body.instantiate1 value))
  | .proj name index value => return .proj name index (← reduceSemantics value)
  | _ => return expression

/-- Instantiate the Boolean decision law with the original decision instance.
Its operands may contain source aliases that ordinary simp matching does not
unfold. The proof uses the generic decision theorem, not a chosen evaluator. -/
simproc_decl sourceDecision (decide _ = true) := fun expression => do
  let some (_, left, right) := expression.eq? | return .continue
  unless left.isAppOf ``decide && right.isConstOf ``Bool.true do return .continue
  let arguments := left.getAppArgs
  -- Preserve the original instance without re-elaborating its source aliases.
  -- The final presentation theorem is still checked by the kernel.
  let law := mkAppN (mkConst ``decide_eq_true_eq) arguments
  return .done { expr := arguments[0]!, proof? := some law }

simproc_decl sourceDecisionFalse (decide _ = false) := fun expression => do
  let some (_, left, right) := expression.eq? | return .continue
  unless left.isAppOf ``decide && right.isConstOf ``Bool.false do return .continue
  let arguments := left.getAppArgs
  let negative := mkApp (mkConst ``Not) arguments[0]!
  let law := mkAppN (mkConst ``decide_eq_false_iff_not) arguments
  let equality := mkAppN (mkConst ``propext) #[expression, negative, law]
  return .done { expr := negative, proof? := some equality }

def normalizationSimprocs : CoreM Simp.SimprocsArray := do
  let procedures ← (← Simp.getSimprocs).add ``sourceDecision true
  let procedures ← procedures.add ``sourceDecisionFalse true
  return #[procedures]

/-- The simplifier supplies ordinary equality proofs for every nondefinitional
step, including the all-natural correctness of the power-of-two decision. -/
def normalizationContext : MetaM Simp.Context := do
  let mut theorems ← getSimpTheorems
  for name in [``Fin.forall_fin_succ, ``exists_cons, ``exists_nil,
      ``naturalPowerOfTwo_eq_true, ``Option.some.injEq, ``Values.cons.injEq,
      ``PIR.Process.done.injEq, ``decide_eq_true_eq, ``Bool.and_eq_true,
      ``option_elim_constant] do
    theorems ← theorems.addConst name
  Simp.mkContext { maxSteps := 100000 } #[theorems] (← getSimpCongrTheorems)

partial def normalize (expression : Expr) : MetaM Simp.Result := do
  let context ← normalizationContext
  let expression ← transform expression (pre := fun term => do
    if let .forallE name domain body info := term then
      let domain ← whnf domain
      if domain.isAppOf ``Fin then
        let count ← withTransparency .all <| reduce domain.getAppArgs[0]!
        unless count.rawNatLit?.isSome do
          throwError "source-input-clauses: clause count is not closed"
        return .continue (some (.forallE name (mkApp (mkConst ``Fin) count) body info))
    return .continue)
  let mut finite : SimpTheorems := {}
  finite ← finite.addConst ``Fin.forall_fin_succ
  finite ← finite.addConst ``Fin.forall_fin_zero
  let (initial, _) ← simp expression (← Simp.mkContext {} #[finite] (← getSimpCongrTheorems))
  let pruned ← transform initial.expr (pre := fun term => do
    if let .forallE name domain body info := term then
      if !domain.hasFVar && (← isProp domain) then
        let domain ← withTransparency .all <| reduce domain (skipTypes := false)
        return .continue (some (.forallE name domain body info))
    return .continue)
  let (prunedResult, _) ← simp pruned context (← normalizationSimprocs)
  let mut result ← initial.mkEqTrans prunedResult
  for _ in [:8] do
    let reduced ← reduceSemantics result.expr
    let (next, _) ← simp reduced context (← normalizationSimprocs)
    let changed := next.expr != result.expr
    result ← result.mkEqTrans next
    unless changed do return result
  throwError "source-input-clauses: semantic normalization did not finish"

end ZkcSecurity.Tools.SourceInputClauses

@[expose] public meta section
namespace ZkcSecurity.Tools.SourceInputClauses
open Lean Meta Elab Term Tactic
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims.HonestPair

/-- Refuse residual interpreter computations. Leaving such a computation in a
presentation would conceal a missing mathematical interpretation. -/
partial def checkFinished (expression : Expr) : MetaM Unit := do
  if (← isProof expression) then return
  if (← isType expression) && !(← isProp expression) then return
  if let .const name _ := expression.getAppFn then
    if name == ``FormulaBinding.invokeRelationOn || name == ``invoke ||
        name == ``Evaluation.operationOn || name == ``Region.denote ||
        name == ``Subject.inputClause || name == ``Subject.inputFormulas ||
        name.toString.startsWith "PIR.Process." then
      throwError "source-input-clauses: unsupported residual formula semantics: {name}\npresentation: {expression}"
  match expression with
  | .app .. =>
      for argument in expression.getAppArgs do checkFinished argument
  | .lam .. => lambdaTelescope expression fun _ body => checkFinished body
  | .forallE .. => forallTelescope expression fun _ body => checkFinished body
  | .proj _ _ value => checkFinished value
  | _ => pure ()

def clausesExpression (subject inputs : Expr) : TermElabM Expr := do
  let clause ← mkAppM ``Subject.inputClause #[subject, inputs]
  forallTelescope (← inferType clause) fun binders _ =>
    mkForallFVars binders (mkAppN clause binders)

partial def withRow (family types : Expr) (locals : Array Expr)
    (continuation : Array Expr → Expr → TermElabM Expr) : TermElabM Expr := do
  let types ← whnf types
  if types.isAppOf ``List.nil then
    let row ← mkAppOptM ``Values.nil #[none, some family]
    continuation locals row
  else if types.isAppOf ``List.cons then
    let arguments := types.getAppArgs
    let type := arguments[1]!
    withLocalDeclD (Name.mkSimple s!"input{locals.size}") (mkApp family type) fun head => do
      withRow family arguments[2]! (locals.push head) fun locals tail => do
        let row ← mkAppM ``Values.cons #[head, tail]
        continuation locals row
  else throwError "source-input-clauses: input sorts are not a closed typed row"

/-- Branch only on typed input presence, never on formula truth. Every leaf
is reduced from the actual retained selectors and helper invocation. -/
partial def splitPresence (row : Expr) (finish : Expr → TermElabM Expr) : TermElabM Expr := do
  let row ← whnf row
  if row.isAppOf ``Values.nil then return ← finish row
  unless row.isAppOf ``Values.cons do
    throwError "source-input-clauses: expected a constructor input row"
  let arguments := row.getAppArgs
  let head := arguments[4]!
  let tail := arguments[5]!
  let advance (value : Expr) := splitPresence tail fun rest => do
    finish (mkAppN row.getAppFn ((arguments.set! 4 value).set! 5 rest))
  let present ← whnf head
  if present.isAppOf ``Option.none || present.isAppOf ``Option.some then
    return ← advance head
  let optionType ← whnf (← inferType head)
  unless optionType.isAppOf ``Option do
    throwError "source-input-clauses: component is not optional"
  let valueType := optionType.getAppArgs[0]!
  let absent ← advance (← mkAppOptM ``Option.none #[some valueType])
  let present ← withLocalDeclD `value valueType fun value => do
    let body ← advance (← mkAppM ``Option.some #[value])
    mkLambdaFVars #[value] body
  mkAppM ``Option.elim #[head, absent, present]

def interpretRow (subject row : Expr) : TermElabM Expr := do
  let expression ← splitPresence row fun row => do
    let result ← normalize (← clausesExpression subject row)
    checkFinished result.expr
    return result.expr
  -- A constructor row may still contain arbitrary optional service or unused
  -- data values. Prune constant presence branches in this path as well.
  let (simplified, _) ← simp expression (← normalizationContext) (← normalizationSimprocs)
  return simplified.expr

/-- The typed input tuple determines the lambda arity. Every clause is read
through its retained role selectors and evaluated in the admitted helper table. -/
elab "source_input_condition " subject:term:max " on " inputs:term:max : term => do
  let subject ← elabTerm subject none
  let inputs ← elabTerm inputs none
  let inputType ← whnf (← inferType inputs)
  unless inputType.isAppOf ``Values do
    throwError "source-input-clauses: expected typed optional source inputs"
  let present ← whnf inputs
  if present.isAppOf ``Values.cons || present.isAppOf ``Values.nil then
    return ← interpretRow subject inputs
  let family := inputType.getAppArgs[1]!
  let types := inputType.getAppArgs[2]!
  let function ← withRow family types #[] fun locals row => do
    let result ← interpretRow subject row
    mkLambdaFVars locals result
  mkAppOptM ``TypedABI.apply #[some inputType.getAppArgs[0]!, some family,
    some (mkSort Level.zero), some types, some function, some inputs]

/-- Recompute the presentation and check the complete equivalence. Structural
row elimination is generic; optional values remain arbitrary throughout. -/
elab "source_input_clauses" : tactic => Term.withoutErrToSorry <| withoutRecover do
  ZkcSecurity.Tools.SubjectABI.casesValues true
  for goal in ← getGoals do
    goal.withContext do
      let target ← whnf (← goal.getType)
      unless target.isAppOfArity ``Iff 2 do
        throwError "source-input-clauses: expected a clause presentation equivalence"
      let left := target.getAppArgs[0]!
      let right := target.getAppArgs[1]!
      let result ← normalize left
      checkFinished result.expr
      let requested ← normalize right
      unless ← withTransparency .all <| isDefEq result.expr requested.expr do
        throwError "source-input-clauses: presentation differs from retained clauses\nactual: {result.expr}\nrequested: {right}"
      let equality ← mkEqTrans (← result.getProof) (← mkEqSymm (← requested.getProof))
      goal.assign (← mkAppM ``Iff.of_eq #[equality])
  setGoals []

end ZkcSecurity.Tools.SourceInputClauses
