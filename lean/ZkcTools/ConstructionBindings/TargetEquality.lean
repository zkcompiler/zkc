module

public import Zkc.Construction.ConnectionTargetPlacement
public meta import Lean.Elab.Tactic

public meta section

/-! A syntax-directed equality proposal for existing target views. Only
primitive operand equalities become interface parameters. Equality of blocks
is built by congruence and the proved coordinate-splicing equations; it is
never an interface premise. No process execution or relocation rule is used. -/
set_option autoImplicit false
namespace ZkcTools.ConstructionBindings.TargetEquality
open Lean Meta
open Zkc.Construction Zkc.Source.Structured

private def view (expression : Expr) : Bool :=
  expression.getAppFn.constName?.any fun name =>
    "Zkc.Construction.Domain.View.".isPrefixOf name.toString

private def child (name : Name) (index : Nat) : Bool :=
  (name == ``Domain.View.sequence && (index == 1 || index == 2)) ||
  (name == ``Domain.View.loop && index == 6)

private partial def expose (expression : Expr) : MetaM Expr := do
  let expression := (← instantiateMVars expression).headBeta.consumeMData
  if expression.isAppOf ``ConnectionTargetPrefix.Prefix.plug ||
      expression.isAppOf ``ConnectionTargetPrefix.Prefix.block then
    if let some next ← unfoldDefinition? expression then return ← expose next
  if let some next ← withTransparency .all <| reduceRecMatcher? expression then
    return ← expose next
  return expression

/-- Infer finite placement operands without unfolding the execution of target
views. A different instruction shape refuses this proposal; it is not a claim
that the two processes are semantically inequivalent. The complete indexed
association remains checked after inference. -/
private partial def matchView (shapeOnly : Bool) (proposed actual : Expr) : MetaM Bool := do
  let proposed ← expose proposed
  let actual ← expose actual
  if proposed == actual then return true
  if let .lam name domain body bi := proposed then
    if let .lam _ otherDomain otherBody _ := actual then
      unless ← isDefEq domain otherDomain do return false
      return ← withLocalDecl name bi domain fun value =>
        matchView shapeOnly (body.instantiate1 value) (otherBody.instantiate1 value)
  if view proposed && view actual then
    unless proposed.getAppFn == actual.getAppFn &&
        proposed.getAppArgs.size == actual.getAppArgs.size do return false
    let name := proposed.getAppFn.constName!
    let left := proposed.getAppArgs
    let right := actual.getAppArgs
    -- Inspect the instruction schedule before expensive fixed-owner operands.
    for index in [:left.size] do
      if child name index then
        unless ← matchView shapeOnly left[index]! right[index]! do return false
    if shapeOnly then return true
    for index in [:left.size] do
      unless child name index do
        unless ← withTransparency .all <| isDefEq left[index]! right[index]! do return false
    return true
  if shapeOnly then return true
  withTransparency .all <| isDefEq proposed actual

/-- Match the finite prefix rather than reducing a mismatched loop to its
Process implementation. This shares the view vocabulary with target equality;
no second execution interpretation or semantic premise is introduced. -/
private partial def matchPrefixCore (shapeOnly : Bool) (proposed actual : Expr) : MetaM Bool := do
  let proposed ← whnf proposed
  let actual ← whnf actual
  if proposed == actual then return true
  if proposed.isAppOf ``ConnectionTargetPrefix.Prefix.empty then
    if actual.isAppOf ``ConnectionTargetPrefix.Prefix.empty then return true
    if actual.isAppOf ``ConnectionTargetPrefix.Prefix.step then return false
    if shapeOnly then return true
    return ← withTransparency .all <| isDefEq proposed actual
  if proposed.isAppOf ``ConnectionTargetPrefix.Prefix.step then
    unless actual.isAppOf ``ConnectionTargetPrefix.Prefix.step do
      if actual.isAppOf ``ConnectionTargetPrefix.Prefix.empty then return false
      if shapeOnly then return true
      return ← withTransparency .all <| isDefEq proposed actual
    let left := proposed.getAppArgs
    let right := actual.getAppArgs
    unless ← matchPrefixCore shapeOnly left[1]! right[1]! do return false
    return ← matchView shapeOnly left[0]! right[0]!
  if shapeOnly then return true
  withTransparency .all <| isDefEq proposed actual

/-- Infer finite operands while retaining the target combinator boundary. -/
def matchPrefix (proposed actual : Expr) : MetaM Bool :=
  matchPrefixCore false proposed actual

/-- A search filter only: unknown shapes remain candidates. Operand equations
and the full indexed association are checked by the ordinary matching path. -/
def compatiblePrefixShape (proposed actual : Expr) : MetaM Bool :=
  matchPrefixCore true proposed actual

private def replaceArgument (expression : Expr) (index : Nat) (equality : Expr) : MetaM Expr := do
  let args := expression.getAppArgs
  withLocalDeclD `operand (← inferType args[index]!) fun operand => do
    let function ← mkLambdaFVars #[operand]
      (mkAppN expression.getAppFn (args.set! index operand))
    mkCongrArg function equality

private def rhs (equality : Expr) : MetaM Expr := do
  let type ← whnf (← inferType equality)
  unless type.isAppOf ``Eq do throwError "connection-target-equality-proof"
  return (← instantiateMVars type.getAppArgs[2]!).headBeta

/-- Expand only the known finite coordinate certificate, using its own
equation theorems. In particular this does not unfold Domain.View semantics. -/
private partial def normalize (expression : Expr) : MetaM Expr := do
  let expression ← instantiateMVars expression
  if (expression.find? (·.isAppOf ``ConnectionFrame.CoordinatePrefix.prepend)).isNone then
    return ← mkEqRefl expression
  if let .lam name domain body bi := expression then
    return ← withLocalDecl name bi domain fun value => do
      let equality ← normalize (body.instantiate1 value)
      mkAppM ``funext #[← mkLambdaFVars #[value] equality]
  if expression.isAppOf ``ConnectionFrame.CoordinatePrefix.prepend then
    let args := expression.getAppArgs
    let certificate ← whnf args[4]!
    let fields := certificate.getAppArgs
    let name := certificate.getAppFn.constName!
    let mut equality ←
      if name == ``ConnectionFrame.CoordinatePrefix.empty then
        mkAppOptM ``ConnectionFrame.CoordinatePrefix.prepend.eq_1
          #[some args[0]!, some args[1]!, some args[5]!]
      else if name == ``ConnectionFrame.CoordinatePrefix.indicesEmpty then
        mkAppOptM ``ConnectionFrame.CoordinatePrefix.prepend.eq_2
          #[some args[0]!, some args[1]!, some args[2]!, some args[5]!,
            some fields[3]!, some fields[4]!]
      else if name == ``ConnectionFrame.CoordinatePrefix.indicesAppend then
        mkAppOptM ``ConnectionFrame.CoordinatePrefix.prepend.eq_3
          (#[some args[0]!, some args[1]!, some args[2]!, some args[5]!] ++
            (fields.extract 3 fields.size).map some)
      else throwError "connection-target-prefix-constructor"
    for argument in args.extract 6 args.size do equality ← mkAppM ``congrFun #[equality, argument]
    let next ← normalize (← rhs equality)
    return ← mkEqTrans equality next
  if view expression then
    let mut current := expression
    let mut equality ← mkEqRefl expression
    for index in [:expression.getAppArgs.size] do
      if child expression.getAppFn.constName! index then
        let argumentEquality ← normalize current.getAppArgs[index]!
        if (← rhs argumentEquality) == current.getAppArgs[index]! then continue
        let step ← replaceArgument current index argumentEquality
        equality ← mkEqTrans equality step
        current ← rhs step
    return equality
  let reduced := expression.headBeta
  if reduced != expression then return ← normalize reduced
  if let some reduced ← withTransparency .all <| reduceRecMatcher? expression then
    return ← normalize reduced
  return ← mkEqRefl expression

private def operandType (type : Expr) : Bool :=
  [``Nat, ``String, ``Bool, ``Template].any type.isConstOf ||
    (type.isAppOf ``List && type.getAppArgs.back!.isConstOf ``Nat)

private partial def compare (proposed actual : Expr) : MetaM Expr := do
  let proposed ← expose proposed
  let actual ← expose actual
  if proposed == actual then return ← mkEqRefl actual
  if let .lam name domain body bi := proposed then
    if let .lam _ otherDomain otherBody _ := actual then
      unless ← isDefEq domain otherDomain do throwError "connection-target-model-mismatch"
      return ← withLocalDecl name bi domain fun value => do
        let equality ← compare (body.instantiate1 value) (otherBody.instantiate1 value)
        mkAppM ``funext #[← mkLambdaFVars #[value] equality]
  if view proposed && view actual then
    unless proposed.getAppFn == actual.getAppFn && proposed.getAppArgs.size == actual.getAppArgs.size do
      throwError "connection-target-instruction-mismatch"
    let mut current := proposed
    let mut equality ← mkEqRefl proposed
    for index in [:proposed.getAppArgs.size] do
      let left := current.getAppArgs[index]!
      let right := actual.getAppArgs[index]!
      if left == right then continue
      let argumentEquality ← if child proposed.getAppFn.constName! index then compare left right else do
        let type ← whnf (← inferType left)
        -- Reducing a symbolic layout lookup/length during proposal repeatedly
        -- expands its inherited prefix. Keep that finite equation explicit.
        if operandType type && !left.isMVar && !right.isMVar then
          mkFreshExprMVar (← mkEq left right)
        else
          unless ← isDefEq left right do
            throwError "connection-target-field-mismatch: {proposed.getAppFn.constName!}[{index}]"
          mkEqRefl right
      let step ← replaceArgument current index argumentEquality
      equality ← mkEqTrans equality step
      current ← rhs step
    return equality
  unless ← isDefEq proposed actual do
    throwError "connection-target-spine-mismatch: proposed={proposed.getAppFn.constName?}, actual={actual.getAppFn.constName?}, lambda={proposed.isLambda}/{actual.isLambda}"
  mkEqRefl actual

/-- Every open premise has a finite operand type. The returned block equality
is a proof term assembled from those premises, not an assumed association. -/
def propose (typed actual : Expr) : MetaM Expr := do
  let normalization ← normalize typed
  let association ← compare (← rhs normalization) actual
  mkEqTrans normalization association

end ZkcTools.ConstructionBindings.TargetEquality
