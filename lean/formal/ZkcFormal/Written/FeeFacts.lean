module

public import ZkcFormal.Written.Views
public import ZkcFormal.Written.Fees
public import ZkcFormal.Written.SiteCaps
public meta import Lean

/-!
The facts of a subject's tables of caps that a proof by fees needs, declared by a command over
the subject.

`publish_fees S` decides, for each goal row of the subject `S` at the path `p`, while it
elaborates and before it declares anything of the row: that the row's table of caps counts as the
stored program does (`CapTable.counted`), and that the table's budget is at most the row's bound
(`Fees.within`). Both are closed definitions of the library, evaluated by the kernel. A row for
which one evaluates to `false` gets no fee facts and a line that says which; the other rows are
not affected. A decision that the kernel does not evaluate is an error. For a row where both hold,
it declares under `<space>.<p>.fees`:

* `counted`: the table counts as the stored program does;
* `budget`: the table's budget as a number, `count / total`, at the bound's numbers where the
  budget is the bound and at the budget's own in lowest terms otherwise (`Fees.budgetNumerator`,
  `Fees.budgetDenominator`, evaluated by the kernel);
* `total_eq_limit`, where the budget is the bound: the table's total is the bound's limit;
* `judged.view` and `judged.view_iff`: the named view of the fee judgment within that budget,
  `Fees.JudgedAt` at the row's short application, its table and those numbers
  (`ZkcFormal.Written.Views`);
* `installed_of_judged`: from that view, the installed bound at the limit of the row's bound.

Each fact is a theorem of `ZkcFormal.Written.Fees` applied to the row's constants, to numerals and
to the value of a decision; the kernel checks each when it is declared. The command's terms are
applications of the library's constants: it synthesizes no instance where it is called, so an
instance, a notation or a variable of the caller's does not change what it decides or declares.

A row is read as `ZkcFormal.Written.Publish` reads it. The table of caps is the expression that
the row's fields hold, named or written in place; the bound is a constant, as in a published
statement. The fee facts are those of a proof of soundness: a subject with a row of a property
that publishes nothing is refused, as `publish_goals` refuses it, and a row of another published
property (there is none today) gets no fee facts and a line.

A site's cap is read from the table in the judgment's term (`CapTable.allowance`): the command
declares no cap equation, no site's name and no label. A fees module is its imports and that line.
It is for proofs, not for a challenge: the repository's challenges do not import it.

The naming of views unfolds the fee judgment because this module registers it (`view_unfold`).
-/

attribute [view_unfold] ZkcFormal.Written.Fees.JudgedWithin ZkcFormal.Written.Fees.JudgedAt

public meta section

namespace ZkcFormal.Written.FeeFacts
open Lean Meta Elab Term Command

private def kernelValue (e : Expr) : MetaM Expr := do
  ofExceptKernelException (Kernel.whnf (← getEnv) (← getLCtx) e)

/-- A decision of the library evaluated by the kernel; a decision that the kernel does not
evaluate to a truth value is an error, not a refusal. -/
private def decided (what : String) (e : Expr) : MetaM Bool := do
  let r ← kernelValue e
  if r.isConstOf ``Bool.true then return true
  if r.isConstOf ``Bool.false then return false
  throwError "publish_fees: the kernel did not evaluate {what}{indentExpr e}\nit stopped at{indentExpr r}"

/-- A number of the library evaluated by the kernel. -/
private def kernelNat (e : Expr) : MetaM Nat := do
  match ← kernelValue e with
  | .lit (.natVal n) => return n
  | r => throwError "publish_fees: the kernel did not evaluate{indentExpr e}\nto a number; it stopped at{indentExpr r}"

/-- The proof `rfl` of `decision = true`, stated at that type: the kernel evaluates the decision
when the fact that holds this proof is declared. -/
private def byEvaluation (decision : Expr) : MetaM Expr := do
  let holds ← mkEq decision (Lean.mkConst ``Bool.true)
  let rfl := mkApp2 (Lean.mkConst ``Eq.refl [1]) (Lean.mkConst ``Bool) (Lean.mkConst ``Bool.true)
  return mkApp2 (Lean.mkConst ``id [0]) holds rfl

/-- Declare a theorem, with the type of its proof. -/
private def declareTheorem (name : Name) (value : Expr) (type? : Option Expr := none) : MetaM Unit := do
  if (← getEnv).contains name then throwError "publish_fees: {name} is already declared"
  let type ← match type? with
    | some type => pure type
    | none => inferType value
  addDecl (.thmDecl { name, levelParams := [], type, value })

/-- The fee facts of one row, or the reason that it gets none. -/
def rowFacts (subject : Name) (space : Name) (row : Publish.Row) : CommandElabM Unit := do
  let base := Publish.theoremName space row "fees"
  let pathText := ".".intercalate row.path
  let reason ← liftTermElabM do
    -- a property that publishes nothing is refused, as the other commands refuse it
    discard <| Publish.theoremsOf row
    unless row.isSoundness do
      return some m!"publish_fees: {pathText}: the fee facts are those of a soundness goal; none for the property {row.property}"
    let model := Lean.mkConst ``ZkcFormal.Written.StandardInterpretation.model
    let draws := Lean.mkConst ``ZkcFormal.Written.StandardInterpretation.draws
    let app := Lean.mkConst row.application
    let bound := Lean.mkConst (← row.bound)
    let caps ← Publish.fieldOf row.fields ``Zkc.Subject.GoalFields `caps
    let root := (← whnf (← inferType app)).appArg!
    let pkg := (← whnf (← inferType root)).appArg!
    let stored ← mkProjection pkg `stored
    let rootKey ← mkProjection (← mkProjection (← mkProjection root `entry) `header) `key
    -- the two decisions, before anything is declared
    let counted ← mkAppM ``Zkc.Subject.CapTable.counted #[caps, stored, rootKey]
    unless ← decided "whether the table counts as the stored program" counted do
      return some m!"publish_fees: {pathText}: the table {caps} does not count as the stored program; no fee facts"
    let within ← mkAppM ``ZkcFormal.Written.Fees.within #[caps, bound]
    unless ← decided "whether the budget is within the bound" within do
      let numerator ← kernelNat (← mkProjection bound `numerator)
      let denominator ← kernelNat (← mkProjection bound `denominator)
      return some m!"publish_fees: {pathText}: the budget of {caps} is above the bound {numerator}/{denominator}; no fee facts"
    let atBound ← mkAppM ``ZkcFormal.Written.Fees.atBound #[caps, bound]
    let equal ← decided "whether the budget is the bound" atBound
    let count := mkNatLit (← kernelNat (← mkAppM ``ZkcFormal.Written.Fees.budgetNumerator #[caps, bound]))
    let total := mkNatLit (← kernelNat (← mkAppM ``ZkcFormal.Written.Fees.budgetDenominator #[caps, bound]))
    let is ← byEvaluation (← mkAppM ``ZkcFormal.Written.Fees.budgetIs #[caps, count, total])
    -- the declarations of the row
    declareTheorem (base ++ `counted) (← byEvaluation counted) (← mkEq counted (Lean.mkConst ``Bool.true))
    declareTheorem (base ++ `budget) (← mkAppM ``ZkcFormal.Written.Fees.budget_eq #[caps, count, total, is])
    if equal then
      declareTheorem (base ++ `total_eq_limit)
        (← mkAppM ``ZkcFormal.Written.Fees.total_eq_limit_of_atBound #[caps, bound, ← byEvaluation atBound])
    let judged ← mkAppM ``ZkcFormal.Written.Fees.JudgedAt #[model, app, draws, caps, count, total]
    Views.declareView (base ++ `judged) (← Views.viewOf subject judged) judged
    let view := Lean.mkConst (base ++ `judged ++ `view)
    let step ← withLocalDeclD `judged view fun h => do
      let raw ← mkAppM ``Iff.mp #[Lean.mkConst (base ++ `judged ++ `view_iff), h]
      mkLambdaFVars #[h] (← mkAppM ``ZkcFormal.Written.Fees.installed_of_judgedAt
        #[model, app, draws, caps, raw, is, bound, ← byEvaluation within])
    declareTheorem (base ++ `installed_of_judged) step
    return none
  if let some reason := reason then logInfo reason

/-- **Declare the fee facts of the goals of a subject.** -/
elab "publish_fees " s:ident : command => do
  let subject ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo s
  let space := subject.getPrefix
  let t ← liftTermElabM (Publish.tables subject)
  for index in [:t.goals] do
    rowFacts subject space (← liftTermElabM (Publish.rowAt t index))

end ZkcFormal.Written.FeeFacts
