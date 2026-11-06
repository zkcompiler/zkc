module

public import ZkcSecurityTools.SubjectABI
public import ZkcSecurityTools.SourceInputReadback
public import Zkc.Semantics.ExactRefinement
public meta import Lean.Elab.Tactic

@[expose] public section

/-! Checked presentation of retained source input clauses. Interpretation uses
Lean reduction of the admitted helper table, not a second source evaluator.
The resulting equivalence covers optional values at every source coordinate. -/
set_option autoImplicit false
namespace ZkcSecurity.Tools.SourceInputClauses
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims.HonestPair

theorem option_elim_constant {α : Type} (value : Option α) (proposition : Prop) :
    value.elim proposition (fun _ => proposition) = proposition := by
  cases value <;> rfl

/-- A present optional value satisfying equality has the same compact presentation
as equality to `some`; this law does not assume presence. -/
theorem option_elim_eq_some {α : Type} (value : Option α) (expected : α) :
    value.elim False (fun actual => actual = expected) ↔ value = some expected := by
  cases value <;> simp

/-- Lift independently checked presence branches without assuming input presence. -/
theorem option_presentation {α : Type} (value : Option α) (source : Option α → Prop)
    (absent : Prop) (present : α → Prop)
    (absentLaw : source none = absent)
    (presentLaw : ∀ x, source (some x) = present x) :
    source value = value.elim absent present := by
  cases value with
  | none => exact absentLaw
  | some x => exact presentLaw x

/-- Each clause supplies its own presence coordinates. Unrelated clauses do not
multiply one another's optional-input cases. -/
def clauseCoordinates {model : DomainModel} {original : Snapshot} {imported : Imported original}
    {selected : AuthoredPair.Selection original}
    (subject : Subject model original imported selected)
    (index : Fin subject.target.owner.contract.clauses.length) : List Nat :=
  let clause := subject.target.owner.clause index
  if clause.kind == .input then (clause.subject.selectors.filterMap fun selector =>
    if selector.direction == .input then some selector.port else none).eraseDups
  else []

/-- A selected callback receives the same captured tuple in either arm. -/
theorem selected_apply {A B : Type} (p : Prop) [Decidable p] (yes no : A → B) (a : A) :
    (if p then yes else no) a = if p then yes a else no a := by split <;> rfl

theorem selected_equal {A : Type} (p : Prop) [Decidable p] (yes no value : A) :
    ((if p then yes else no) = value) = (if p then yes = value else no = value) := by
  split <;> rfl

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

/-- Reduce completed process steps without opening a symbolic selection or the
continuation of an unreached step. Each replacement is definitionally equal
to the original expression. -/
partial def exposeSemantics (expression : Expr) (mathematical : Bool) : MetaM Expr := do
  if expression.isAppOf ``ite then return expression
  let head ← withCanUnfoldPred (fun _ declaration => pure
      (declaration.name != ``OpaqueInstance.holds && declaration.name != ``Evaluation.invokeCallbackOn &&
       declaration.name != ``Evaluation.invokeCallback && declaration.name != ``PIR.Process.bind &&
        !(mathematical && protectedConstants.contains declaration.name))) <|
    withTransparency .all <| whnf expression
  if head.isAppOf ``Evaluation.invokeCallbackOn || head.isAppOf ``Evaluation.invokeCallback then
    let args := head.getAppArgs
    let callback := args[args.size - 2]!
    if callback.isAppOf ``ite then return mkApp callback args.back!
    return ← exposeSemantics (mkApp callback args.back!) mathematical
  unless head.isAppOfArity ``PIR.Process.bind 5 do return head
  let arguments := head.getAppArgs
  let source ← exposeSemantics arguments[3]! false
  if source.isAppOf ``PIR.Process.done then
    return ← exposeSemantics (mkApp arguments[4]! source.getAppArgs.back!) mathematical
  if source.isAppOf ``PIR.Process.halt then
    return mkAppN (mkConst ``PIR.Process.halt) #[arguments[0]!, arguments[2]!, source.getAppArgs.back!]
  return mkAppN head.getAppFn (arguments.set! 3 source)

partial def reduceSemantics (expression : Expr) : MetaM Expr := do
  if expression.isAppOf ``OfNat.ofNat then return expression
  if (← isProof expression) then return expression
  if (← isType expression) && !(← isProp expression) then return ← exposeRowType expression
  let type ← whnf (← inferType expression)
  let mathematical := type.isConstOf ``Bool || type.isConstOf ``Nat || (← isProp expression)
  let expression ← exposeSemantics expression mathematical
  if expression.isAppOf ``OpaqueInstance.holds then return expression
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
step. Keep a readback row intact so the standard existential-equality rules
can substitute it before evaluating the retained relation. -/
def normalizationContext : MetaM Simp.Context := do
  let mut theorems ← getSimpTheorems
  for name in [``Fin.forall_fin_succ,
      ``naturalPowerOfTwo_eq_true, ``Option.some.injEq, ``Values.cons.injEq,
      ``PIR.Process.done.injEq, ``decide_eq_true_eq, ``Bool.and_eq_true,
      ``option_elim_constant, ``option_elim_eq_some, ``selected_equal,
      ``PIR.Process.bind_ite, ``PIR.Process.bind.eq_1, ``PIR.Process.bind.eq_2,
      ``ite_false_right, ``ite_false_left] do
    theorems ← theorems.addConst name
  Simp.mkContext { maxSteps := 100000 } #[theorems] (← getSimpCongrTheorems)

/-- Push application through an actual conditional callback. The callback
type and decision instance come directly from the term. The kernel checks
the resulting equality even when the row type has a source-specific alias. -/
def simplifySemantics (expression : Expr) (context : Simp.Context) : MetaM Simp.Result := do
  let methods := Simp.mkDefaultMethodsCore (← normalizationSimprocs)
  let (result, _) ← Simp.main expression context (methods := { methods with pre := fun term => do
    if term.isAppOf ``OpaqueInstance.holds then return .done { expr := term }
    if term.isAppOfArity ``ite 6 then
      let args := term.getAppArgs
      let type ← whnf args[0]!
      if type.isForall && !type.bindingBody!.hasLooseBVars then
        let law := mkAppN (mkConst ``selected_apply)
          #[type.bindingDomain!, type.bindingBody!, args[1]!, args[2]!, args[3]!, args[4]!, args[5]!]
        let some (_, _, right) := (← inferType law).eq?
          | throwError "source-input-clauses: invalid conditional application law"
        return .visit { expr := right, proof? := some law }
    methods.pre term })
  return result

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
  let reads ← Simp.mkContext {} #[{}] (← getSimpCongrTheorems)
  let methods := Simp.mkDefaultMethodsCore #[]
  let (readback, _) ← Simp.main prunedResult.expr reads (methods := { methods with pre := fun term => do
    if term.isAppOf ``Subject.inputClause then return .done (← SourceInputReadback.expandInput term)
    return .continue })
  let mut result ← (← initial.mkEqTrans prunedResult).mkEqTrans readback
  for _ in [:8] do
    let reduced ← reduceSemantics result.expr
    let next ← simplifySemantics reduced context
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
  if expression.isAppOf ``OpaqueInstance.holds then return ← checkFinished expression.getAppArgs.back!
  if let .const name _ := expression.getAppFn then
    if name == ``FormulaBinding.invokeRelationOn || name == ``invoke ||
        name == ``Evaluation.operationOn || name == ``Region.denote ||
        name == ``Subject.inputClause || name == ``Subject.inputMeanings ||
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

partial def coordinateList (expression : Expr) : MetaM (List Nat) := do
  let expression ← whnf expression
  if expression.isAppOf ``List.nil then return []
  unless expression.isAppOf ``List.cons do throwError "source-input-clauses: open coordinates"
  let arguments := expression.getAppArgs
  let some position := arguments[1]!.rawNatLit? | throwError "source-input-clauses: open coordinate"
  return position :: (← coordinateList arguments[2]!)

/-- Expand only the finite clause quantifier, preserving each source clause. -/
def expandClauses (expression : Expr) : MetaM Simp.Result := do
  let expression ← transform expression (pre := fun term => do
    if let .forallE name domain body info := term then
      let domain ← whnf domain
      if domain.isAppOf ``Fin then
        let count ← withTransparency .all <| reduce domain.getAppArgs[0]!
        unless count.rawNatLit?.isSome do throwError "source-input-clauses: open clause count"
        return .continue (some (.forallE name (mkApp (mkConst ``Fin) count) body info))
    return .continue)
  let mut finite : SimpTheorems := {}
  finite ← finite.addConst ``Fin.forall_fin_succ
  finite ← finite.addConst ``Fin.forall_fin_zero
  return (← simp expression (← Simp.mkContext {} #[finite] (← getSimpCongrTheorems))).1

partial def clauseIndex (expression : Expr) : Option Expr :=
  if expression.isAppOf ``Subject.inputClause then
    some expression.getAppArgs[expression.getAppArgs.size - 2]!
  else match expression with
  | .app f a => (clauseIndex f).orElse fun _ => clauseIndex a
  | .forallE _ _ b _ | .lam _ _ b _ => clauseIndex b
  | _ => none

/-- Focus one coordinate of the actual typed input row without splitting the
other options. Replacing it reconstructs the original constructor spine. -/
def rowCoordinate (row : Expr) (position : Nat) : MetaM (Expr × (Expr → Expr)) := do
  let row ← whnf row
  unless row.isAppOf ``Values.cons do
    throwError "source-input-clauses: selector is outside the input row"
  let arguments := row.getAppArgs
  match position with
  | 0 => return (arguments[4]!, fun value => mkAppN row.getAppFn (arguments.set! 4 value))
  | n + 1 =>
    let (value, put) ← rowCoordinate arguments[5]! n
    return (value, fun newValue => mkAppN row.getAppFn (arguments.set! 5 (put newValue)))
termination_by position

/-- Visit input coordinates in the retained selector order. A missing argument
makes the ordered read fail, independently of every later coordinate. The proof
for that arm checks the original clause with the remaining values symbolic. -/
def splitPresentation (positions : List Nat) (row : Expr)
    (source : Expr → TermElabM Expr) : TermElabM Simp.Result := do
  let finish (value : Expr) := do
    let result ← normalize (← source value)
    checkFinished result.expr
    return result
  match positions with
  | [] => finish row
  | pos :: rest =>
    let (head, put) ← rowCoordinate row pos
    let actual ← whnf head
    if actual.isAppOf ``Option.none then return ← finish row
    if actual.isAppOf ``Option.some then return ← splitPresentation rest row source
    let optionType ← whnf (← inferType head)
    let valueType := optionType.getAppArgs[0]!
    let absent ← finish (put (← mkAppOptM ``Option.none #[some valueType]))
    let (present, presentProof) ← withLocalDeclD `value valueType fun value => do
      let result ← splitPresentation rest (put (← mkAppM ``Option.some #[value])) source
      return (← mkLambdaFVars #[value] result.expr, ← mkLambdaFVars #[value] (← result.getProof))
    let predicate ← withLocalDeclD `input optionType fun value => do
      mkLambdaFVars #[value] (← source (put value))
    let proof ← mkAppM ``option_presentation
      #[head, predicate, absent.expr, present, ← absent.getProof, presentProof]
    return { expr := ← mkAppM ``Option.elim #[head, absent.expr, present], proof? := some proof }

partial def interpretExpanded (subject row inputRow expression : Expr) : TermElabM Simp.Result := do
  if expression.isAppOfArity ``And 2 then
    let left ← interpretExpanded subject row inputRow expression.getAppArgs[0]!
    let right ← interpretExpanded subject row inputRow expression.getAppArgs[1]!
    let law ← mkAppM ``and_congr
      #[← mkAppM ``Iff.of_eq #[← left.getProof], ← mkAppM ``Iff.of_eq #[← right.getProof]]
    let proof ← mkAppM ``propext #[law]
    return { expr := mkApp2 (mkConst ``And) left.expr right.expr, proof? := some proof }
  let positions ← if let some index := clauseIndex expression then do
    coordinateList (← withTransparency .all <| reduce (← mkAppM ``clauseCoordinates #[subject, index]))
    else pure []
  splitPresentation positions row (fun value => pure (expression.replaceFVar inputRow value))

/-- Factor the retained conjunction before expanding presence branches. This
changes proof construction cost, not the interpreted source input contract. -/
def interpretRowProved (subject row : Expr) : TermElabM Simp.Result := do
  withLocalDeclD `sourceInputs (← inferType row) fun inputRow => do
    let expanded ← expandClauses (← clausesExpression subject inputRow)
    let substitute (expression : Expr) (value : Expr) := expression.replaceFVar inputRow value
    let result ← interpretExpanded subject row inputRow expanded.expr
    let expansionProof := substitute (← expanded.getProof) row
    let result := { result with proof? := some (← mkEqTrans expansionProof (← result.getProof)) }
    let (simplified, _) ← simp result.expr (← normalizationContext) (← normalizationSimprocs)
    result.mkEqTrans simplified

def interpretRow (subject row : Expr) : TermElabM Expr := do
  return (← interpretRowProved subject row).expr

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

/-- Locate the actual subject and row below the clause quantifiers. -/
partial def clauseArguments (expression : Expr) : Option (Expr × Expr) :=
  if expression.isAppOf ``Subject.inputClause then
    let arguments := expression.getAppArgs
    some (arguments[arguments.size - 4]!, arguments[arguments.size - 3]!)
  else match expression with
  | .app function argument => (clauseArguments function).orElse fun _ => clauseArguments argument
  | .forallE _ _ body _ | .lam _ _ body _ => clauseArguments body
  | _ => none

/-- Split only used coordinates. Irrelevant options stay universally quantified;
no presence or formula truth is assumed when proving the complete equivalence. -/
def proveClauses (goal : MVarId) : TermElabM Unit := goal.withContext do
  let target ← whnf (← goal.getType)
  let some (subject, row) := clauseArguments target
    | throwError "source-input-clauses: expected retained clauses"
  unless target.isAppOfArity ``Iff 2 do
    throwError "source-input-clauses: expected presentation equivalence"
  let result ← interpretRowProved subject row
  let requested ← normalize target.getAppArgs[1]!
  unless ← withTransparency .all <| isDefEq result.expr requested.expr do
    throwError "source-input-clauses: presentation differs from retained clauses\nactual: {result.expr}\nrequested: {requested.expr}"
  let equality ← mkEqTrans (← result.getProof) (← mkEqSymm (← requested.getProof))
  goal.assign (← mkAppM ``Iff.of_eq #[equality])

/-- Recompute the presentation and check the complete equivalence. Structural
row elimination is generic; optional values remain arbitrary throughout. -/
elab "source_input_clauses" : tactic => Term.withoutErrToSorry <| withoutRecover do
  ZkcSecurity.Tools.SubjectABI.casesValues false
  for goal in ← getGoals do proveClauses goal
  setGoals []

end ZkcSecurity.Tools.SourceInputClauses
