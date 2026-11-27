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
stored program does (`CapTable.counted`, reduced by the kernel), and that the table's budget is at
most the row's bound (`decide`, reduced by the kernel). A row for which
either fails gets no fee facts and a line that says which; the other rows are not affected. For a
row where both hold, it declares under `<space>.<p>.fees`:

* `counted`: the table counts as the stored program does (by `rfl`, which the kernel decides);
* `budget`: the table's budget as a number, at the bound's numbers where the budget is the bound
  and at the table's otherwise (its total at the root in the rationals, reduced by the kernel);
  decided by the kernel;
* `total_eq_limit`, where the budget is the bound: the table's total is the bound's limit;
* `judged.view` and `judged.view_iff`: the named view of `Fees.JudgedWithin` at the row's short
  application, its table and that budget (`ZkcFormal.Written.Views`);
* `installed_of_judged`: from that view, the installed bound at the limit of the row's bound.

A site's cap is read from the table in the judgment's term (`CapTable.allowance`): the command
declares no cap equation, no site's name and no label. A fees module is its imports and that line.
It is for proofs, not for a challenge: the repository's challenges do not import it.

The naming of views unfolds the fee judgment because this module registers it (`view_unfold`).
-/

attribute [view_unfold] ZkcFormal.Written.Fees.JudgedWithin

public meta section

namespace ZkcFormal.Written.FeeFacts
open Lean Meta Elab Term Command

/-- A number that the kernel reduces an expression of type `Nat` to. -/
private def kernelNat (e : Expr) : MetaM Nat := do
  match ← ofExceptKernelException (Kernel.whnf (← getEnv) (← getLCtx) e) with
  | .lit (.natVal n) => return n
  | r => throwError "publish_fees: the kernel did not reduce{indentExpr e}\nto a number, but to{indentExpr r}"

/-- Whether the kernel decides a proposition true: `decide p` reduces to `true`. -/
private def kernelDecides (p : Expr) : MetaM Bool := do
  let r ← ofExceptKernelException (Kernel.whnf (← getEnv) (← getLCtx) (← mkDecide p))
  return r.isConstOf ``Bool.true

private def numeral (e : Expr) : MetaM Nat := do
  let some n ← getNatValue? (← whnf e) | throwError "publish_fees: expected a number in{indentExpr e}"
  return n

/-- `((n : ℕ) : ℚ≥0) / (d : ℕ)`. -/
private def ratio (n d : Nat) : MetaM Expr := do
  let cast (k : Nat) := mkAppOptM ``Nat.cast #[Lean.mkConst ``NNRat, none, mkNatLit k]
  mkAppM ``HDiv.hDiv #[← cast n, ← cast d]

/-- Declare a theorem. -/
private def declareTheorem (name : Name) (type value : Expr) : MetaM Unit := do
  if (← getEnv).contains name then throwError "publish_fees: {name} is already declared"
  addDecl (.thmDecl { name, levelParams := [], type, value })

/-- The fee facts of one row, or the reason that it gets none. -/
def rowFacts (subject : Name) (space : Name) (row : Publish.Row) : CommandElabM Unit := do
  let base := Publish.theoremName space row "fees"
  let pathText := ".".intercalate row.path
  let declared ← liftTermElabM do
    let model := Lean.mkConst ``ZkcFormal.Written.StandardInterpretation.model
    let draws := Lean.mkConst ``ZkcFormal.Written.StandardInterpretation.draws
    let app := Lean.mkConst row.application
    let bound := Lean.mkConst (← row.bound)
    let capsName ← Publish.constName (← Publish.fieldOf row.fields ``Zkc.Subject.GoalFields `caps)
    let caps := Lean.mkConst capsName
    let appType ← whnf (← inferType app)
    let root := appType.appArg!
    let rootType ← whnf (← inferType root)
    let pkg := rootType.appArg!
    let stored ← mkProjection pkg `stored
    let rootKey ← mkProjection (← mkProjection (← mkProjection root `entry) `header) `key
    -- the count, decided by the kernel before anything is declared
    let countedTerm ← mkAppM ``Zkc.Subject.CapTable.counted #[caps, stored, rootKey]
    let counted ← ofExceptKernelException (Kernel.whnf (← getEnv) (← getLCtx) countedTerm)
    unless counted.isConstOf ``Bool.true do
      return some m!"publish_fees: {pathText}: the table {capsName} does not count as the stored program; no fee facts"
    -- the budget against the bound, decided by the kernel
    let boundNumerator ← numeral (← Publish.fieldOf bound ``Zkc.Subject.Bound `numerator)
    let boundDenominator ← numeral (← Publish.fieldOf bound ``Zkc.Subject.Bound `denominator)
    let budgetTerm ← mkAppM ``Zkc.Subject.CapTable.budget #[caps]
    let boundRatio ← ratio boundNumerator boundDenominator
    unless ← kernelDecides (← mkAppM ``LE.le #[budgetTerm, boundRatio]) do
      return some m!"publish_fees: {pathText}: the budget of {capsName} is above the bound {boundNumerator}/{boundDenominator}; no fee facts"
    let atBound ← kernelDecides (← mkEq budgetTerm boundRatio)
    -- below the bound, the table's own numbers: its total at the root in the rationals, reduced
    let (n, d) ← if atBound then pure (boundNumerator, boundDenominator) else do
      let total ← mkAppM ``Zkc.Subject.CapTable.totalAt
        #[caps, Lean.mkConst ``Rat, ← mkAppM ``Zkc.Subject.CapTable.root #[caps]]
      pure (← kernelNat (← mkAppM ``Int.toNat #[← mkAppM ``Rat.num #[total]]),
        ← kernelNat (← mkAppM ``Rat.den #[total]))
    let number ← ratio n d
    let positive ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit 0, mkNatLit d])
    -- the declarations of the row
    declareTheorem (base ++ `counted) (← mkEq countedTerm (Lean.mkConst ``Bool.true))
      (← mkEqRefl (Lean.mkConst ``Bool.true))
    let budgetFact ← mkEq budgetTerm number
    declareTheorem (base ++ `budget) budgetFact (← mkDecideProof budgetFact)
    let budgetProof := Lean.mkConst (base ++ `budget)
    let limitTerm ← mkAppM ``Zkc.Subject.Bound.limit #[bound]
    if atBound then
      declareTheorem (base ++ `total_eq_limit)
        (← mkEq (← mkAppM ``Zkc.Subject.CapTable.total #[caps]) limitTerm)
        (← mkAppM ``ZkcFormal.Written.Fees.total_eq_limit #[caps, positive, budgetProof])
    let judged ← mkAppM ``ZkcFormal.Written.Fees.JudgedWithin #[model, app, draws, caps, number]
    let installed ← mkAppM ``ZkcFormal.Written.Soundness.Installed #[model, app, draws, limitTerm]
    -- the budget is at most the bound: equal to its limit, or within it by the table's total
    let numberProbability ← mkAppM ``ZkcFormal.ProbabilisticProcess.toProbability #[number]
    let within ← if atBound then
        mkAppM ``le_of_eq
          #[← mkAppOptM ``ZkcFormal.Written.Fees.toProbability_eq_limit #[mkNatLit n, mkNatLit d, positive]]
      else do
        let boundPositive ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit 0, mkNatLit boundDenominator])
        let withinFact ← mkAppM ``LE.le #[budgetTerm, ← ratio boundNumerator boundDenominator]
        let totalWithin ← mkAppM ``Zkc.Subject.CapTable.total_le_div
          #[caps, mkNatLit boundNumerator, mkNatLit boundDenominator, boundPositive, ← mkDecideProof withinFact]
        let atNumber ← mkCongrArg (Lean.mkConst ``ZkcFormal.ProbabilisticProcess.toProbability) budgetProof
        mkAppM ``Eq.trans_le #[← mkEqSymm atNumber, totalWithin]
    let judgedView ← Views.viewOf subject judged
    Views.declareView (base ++ `judged) judgedView judged
    let view := Lean.mkConst (base ++ `judged ++ `view)
    let installedProof ← withLocalDeclD `judged view fun h => do
      let le ← mkExpectedTypeHint within (← mkAppM ``LE.le #[numberProbability, limitTerm])
      let raw ← mkAppM ``Iff.mp #[Lean.mkConst (base ++ `judged ++ `view_iff), h]
      mkLambdaFVars #[h] (← mkAppM ``ZkcFormal.Written.Fees.installed_of_judged
        #[model, app, draws, caps, raw, le])
    let installedType ← withLocalDeclD `judged view fun h => mkForallFVars #[h] installed
    declareTheorem (base ++ `installed_of_judged) installedType installedProof
    return none
  match declared with
  | some reason => logInfo reason
  | none => pure ()

/-- **Declare the fee facts of the goals of a subject.** -/
elab "publish_fees " s:ident : command => do
  let subject ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo s
  let space := subject.getPrefix
  let t ← liftTermElabM (Publish.tables subject)
  for index in [:t.goals] do
    rowFacts subject space (← liftTermElabM (Publish.rowAt t index))

end ZkcFormal.Written.FeeFacts
