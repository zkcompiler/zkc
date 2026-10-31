module

public import Zkc.Construction.ConnectionFrameLookup
public meta import Lean.Elab.Tactic.Omega
public meta import ZkcTools.ConstructionBindings.Syntax

public meta section

/-! Proof-producing queries of exact finite layouts, before readback enumeration.

`select? layout index` returns the selected cell and a proof of
`layout[index]? = some cell`. `propose goal` additionally matches that cell
against the expected cell, allowing typed operand holes to be inferred. Both
are transactional `MetaM` APIs: refusal restores the metavariable state.
Enable `trace.zkc.connection.layoutLookup` for refusal reasons.

Only the index, list spine on the selected path, and selected cell are inspected.
Arithmetic uses length laws and then generalizes remaining Nat atoms before
calling Omega. Neither the caller prefix nor ambient semantic hypotheses are
given to Omega. No cache survives assignments or backtracking. These are proof
proposals: their eventual containing declaration is checked by Lean's kernel.
-/
set_option autoImplicit false
namespace ZkcTools.ConstructionBindings.LayoutLookup
open Lean Meta
open Zkc.Construction Zkc.Source Zkc.Source.Structured

initialize registerTraceClass `zkc.connection.layoutLookup

structure Selection where
  cell : Expr
  proof : Expr

private structure Normalized where
  value : Expr
  proof : Expr

private def unchanged (value : Expr) : MetaM Normalized :=
  return ⟨value, ← mkEqRefl value⟩

/-- Reduce only the notation's partially applied operator, never its operands. -/
private partial def canonicalHead (value : Expr) : MetaM Expr := do
  if [``HAdd.hAdd, ``HSub.hSub, ``HAppend.hAppend, ``GetElem?.getElem?,
      ``Add.add, ``Sub.sub, ``Append.append].any value.isAppOf then
    let args := value.getAppArgs
    if args.size ≥ 2 then
      let operator ← whnf (mkAppN value.getAppFn (args.extract 0 (args.size - 2)))
      let next := mkAppN operator (args.extract (args.size - 2) args.size) |>.headBeta
      if next != value then return ← canonicalHead next
  return value.headBeta.consumeMData

private def owner (value : Expr) : Bool :=
  [``ConnectionCertificate.receiveLayout, ``ConnectionCertificate.GuardReadback.refine,
    ``ConnectionComputation.tupleLayout, ``ConnectionComputation.resultsLayout,
    ``ConnectionFrame.observedLayout, ``ConnectionFrame.queryLayout,
    ``ConnectionFrame.observedReceiveLayout, ``ConnectionFrame.deliveryLayout,
    ``ConnectionFrame.projectedLayout, ``ConnectionFrame.projectedExitLayout,
    ``ConnectionFrame.repeatLayout, ``ConnectionFrame.repeatExitLayout].any value.isAppOf

private def unfoldOwner (value : Expr) : MetaM (Option Expr) := do
  unless owner value do return none
  withOptions (smartUnfolding.set · false) <| unfoldDefinition? value (ignoreTransparency := true)

private def length (xs : Expr) : MetaM Expr := mkAppM ``List.length #[xs]

private def rhs (proof : Expr) : MetaM Expr := do
  let type ← inferType proof
  return type.getAppArgs.back!

private def lengthLaw (xs : Expr) : MetaM (Option Expr) := do
  let xs ← canonicalHead xs
  let args := xs.getAppArgs
  let names := [
    (``ConnectionCertificate.receiveLayout, ``ConnectionFrameLookup.receive_length, 2),
    (``ConnectionComputation.tupleLayout, ``ConnectionFrameLookup.tuple_length, 2),
    (``ConnectionComputation.resultsLayout, ``ConnectionFrameLookup.results_length, 2),
    (``ConnectionCertificate.GuardReadback.refine, ``ConnectionFrameLookup.guard_length, 1),
    (``ConnectionFrame.observedLayout, ``ConnectionFrameLookup.observed_length, 2),
    (``ConnectionFrame.queryLayout, ``ConnectionFrameLookup.query_length, 3),
    (``ConnectionFrame.observedReceiveLayout, ``ConnectionFrameLookup.observed_receive_length, 3),
    (``ConnectionFrame.deliveryLayout, ``ConnectionFrameLookup.delivery_length, 3),
    (``ConnectionFrame.projectedLayout, ``ConnectionFrameLookup.projectedLayout_length, 5),
    (``ConnectionFrame.projectedExitLayout, ``ConnectionFrameLookup.projectedExitLayout_length, 5),
    (``ConnectionComputation.cells, ``ConnectionFrameLookup.calculationCells_length, 1)]
  for (head, law, count) in names do
    if xs.isAppOf head then return some (← mkAppM law (args.extract (args.size - count) args.size))
  if xs.isAppOf ``List.map then
    return some (← mkAppOptM ``List.length_map
      #[some args[0]!, some args[1]!, some args[3]!, some args[2]!])
  if xs.isAppOf ``List.append then
    return some (← mkAppOptM ``List.length_append #[some args[0]!, some args[1]!, some args[2]!])
  if xs.isAppOf ``List.set then
    return some (← mkAppOptM ``List.length_set #[some args[0]!, some args[1]!, some args[2]!, some args[3]!])
  if xs.isAppOf ``List.cons then
    return some (← mkAppOptM ``List.length_cons #[some args[0]!, some args[1]!, some args[2]!])
  if xs.isAppOf ``List.nil then
    return some (← mkAppOptM ``List.length_nil #[some args[0]!])
  return none

/-- Normalize only Nat arithmetic and length projections, never a whole layout. -/
private partial def normalizeNat (input : Expr) (fuel : Nat) : MetaM Normalized := do
  if fuel == 0 then throwError "layout-lookup-normalization-fuel"
  let value ← canonicalHead (← instantiateMVars input)
  for (name, arity) in [(``Nat.add, 2), (``Nat.sub, 2), (``Nat.succ, 1)] do
    if value.isAppOf name && value.getAppNumArgs != arity then
      trace[zkc.connection.layoutLookup] "malformed arithmetic: {name}, arity={value.getAppNumArgs}"
      throwError "layout-lookup-arithmetic-arity: {name}"
  if value.isAppOfArity ``Nat.sub 2 && value.getAppArgs[0]! == value.getAppArgs[1]! && !value.hasExprMVar then
    return ⟨mkNatLit 0, ← mkAppM ``Nat.sub_self #[value.getAppArgs[0]!]⟩
  if value.isAppOf ``List.length then
    let xs := value.getAppArgs.back!
    if let some law ← lengthLaw xs then
      let next ← normalizeNat (← rhs law) (fuel - 1)
      return ⟨next.value, ← mkEqTrans law next.proof⟩
    if let some expanded ← unfoldOwner xs then
      return ← normalizeNat (← length expanded) (fuel - 1)
    if value.hasExprMVar then throwError "layout-lookup-undetermined-length"
    -- A closed cached prefix has a concrete length. Keeping that length as
    -- an opaque arithmetic atom loses its relation to a literal target index.
    -- Reduction inspects only the list spine; the proof is still conversion.
    if !value.hasFVar then
      let reduced ← whnf value
      if reduced.isRawNatLit then return ⟨reduced, ← mkEqRefl value⟩
    return ← unchanged value
  if value.isAppOfArity ``Nat.add 2 || value.isAppOfArity ``Nat.sub 2 || value.isAppOfArity ``Nat.succ 1 then
    let mut proof ← mkEqRefl value.getAppFn
    let mut result := value.getAppFn
    for argument in value.getAppArgs do
      let next ← normalizeNat argument (fuel - 1)
      proof ← mkCongr proof next.proof
      result := mkApp result next.value
    if result.isAppOfArity ``Nat.sub 2 && result.getAppArgs[0]! == result.getAppArgs[1]! then
      let cancel ← mkAppM ``Nat.sub_self #[result.getAppArgs[0]!]
      return ⟨mkNatLit 0, ← mkEqTrans proof cancel⟩
    return ⟨result, proof⟩
  if value.hasExprMVar then throwError "layout-lookup-undetermined-index-operand"
  if value.isAppOf ``OfNat.ofNat then return ← unchanged (← whnf value)
  return ← unchanged value

private partial def atoms (value : Expr) (found : Array Expr := #[]) : Array Expr :=
  if value.isRawNatLit then found
  else if value.isAppOfArity ``Nat.add 2 || value.isAppOfArity ``Nat.sub 2 || value.isAppOfArity ``Nat.succ 1 then
    value.getAppArgs.foldl (fun found argument => atoms argument found) found
  else if found.contains value then found else found.push value

-- Omega's frontend recognizes the standard overloaded arithmetic syntax.
private partial def omegaNat (value : Expr) : MetaM Expr := do
  if let some n := value.rawNatLit? then return mkNatLit n
  let args := value.getAppArgs
  if value.isAppOfArity ``Nat.add 2 || value.isAppOfArity ``Nat.sub 2 then
    return ← mkAppM (if value.isAppOf ``Nat.add then ``HAdd.hAdd else ``HSub.hSub)
      #[← omegaNat args[0]!, ← omegaNat args[1]!]
  if value.isAppOfArity ``Nat.succ 1 then
    return ← mkAppM ``HAdd.hAdd #[← omegaNat args[0]!, mkNatLit 1]
  return value

/-- A theorem over fresh Nat parameters prevents conversion from opening atoms. -/
private def arithmetic (relation left right : Expr) (fuel : Nat) : MetaM Expr := do
  let left ← normalizeNat left fuel
  let right ← normalizeNat right fuel
  let original := mkApp2 relation (← omegaNat left.value) (← omegaNat right.value)
  let parameters := atoms right.value (atoms left.value)
  let proof ← if left.value == right.value && relation.isAppOf ``Eq then
      mkEqRefl left.value
    else if left.value == right.value && relation.isAppOf ``LE.le then
      mkAppM ``Nat.le_refl #[left.value]
    else do
      let generalized ← withLCtx {} {} <|
        withLocalDeclsDND (parameters.map fun _ => (`size, mkConst ``Nat)) fun locals => do
          let target := original.replace fun expression =>
            (parameters.idxOf? expression).map (locals[·]!)
          let goal ← mkFreshExprSyntheticOpaqueMVar target
          if let some contra ← goal.mvarId!.falseOrByContra then
            contra.withContext do
              Lean.Elab.Tactic.Omega.omega (← getLocalHyps).toList contra
          let value ← instantiateMVars goal
          if value.hasExprMVar then throwError "layout-lookup-arithmetic-unfinished"
          return ← mkLambdaFVars locals value
      pure (mkAppN generalized parameters)
  let converted ← mkCongr (← mkCongrArg relation left.proof) right.proof
  return ← mkEqMPR converted proof

private def natRelation (name : Name) : MetaM Expr := do
  if name == ``Eq || name == ``Ne then
    return mkApp (mkConst name [.succ .zero]) (mkConst ``Nat)
  if name == ``Nat.le then return ← mkAppOptM ``LE.le #[some (mkConst ``Nat), none]
  if name == ``Nat.lt then return ← mkAppOptM ``LT.lt #[some (mkConst ``Nat), none]
  throwError "layout-lookup-unsupported-relation"

private def arithmetic? (name : Name) (left right : Expr) (fuel : Nat) : MetaM (Option Expr) := do
  let saved ← saveState
  try
    -- The common fresh-cell query should not even normalize its caller length.
    if left == right then
      if name == ``Eq then return some (← mkEqRefl left)
      if name == ``Nat.le then return some (← mkAppM ``Nat.le_refl #[left])
    return some (← arithmetic (← natRelation name) left right fuel)
  catch error =>
    saved.restore
    if error.isRuntime || error.isInterrupt then throw error
    trace[zkc.connection.layoutLookup] "arithmetic {name}: {error.toMessageData}"
    return none

private def requireArithmetic (name : Name) (left right : Expr) (fuel : Nat) : MetaM Expr := do
  let some proof ← arithmetic? name left right fuel
    | throwError "layout-lookup-undetermined-arithmetic: {name}"
  return proof

/-- Prove a finite size equation through the existing length laws. This keeps
unknown cell operands out of conversion: their values do not determine the
length of a typed result row. Refusal leaves all metavariables unchanged. -/
def proposeLengthEquality (goal : MVarId) (fuel : Nat := 256) : MetaM Bool := goal.withContext do
  let type ← instantiateMVars (← goal.getType)
  unless type.isAppOfArity ``Eq 3 && type.getAppArgs[0]!.isConstOf ``Nat do
    return false
  let some proof ← arithmetic? ``Eq type.getAppArgs[1]! type.getAppArgs[2]! fuel
    | return false
  goal.assign proof
  return true

private def checkedCell (cell proof : Expr) : MetaM Selection := do
  let cell ← instantiateMVars cell
  -- Expose the selected constructor only. Recursive reduction also traverses
  -- dependent scope indices and unresolved presence substitutions, although
  -- those values may be determined by a later interface fact.
  let cell ← if cell.hasExprMVar then
    withTransparency .all <| whnf cell
    else pure cell
  if cell.hasExprMVar then throwError "layout-lookup-undetermined-predecessor-cell"
  return ⟨cell, proof⟩

private partial def selectCore (input index : Expr) (fuel : Nat) : MetaM Selection := do
  if fuel == 0 then throwError "layout-lookup-descent-fuel"
  let fuel := fuel - 1
  let xs ← canonicalHead (← instantiateMVars input)
  let args := xs.getAppArgs
  if xs.isAppOf ``List.map then
    let f := args[args.size - 2]!
    let source := args.back!
    let selected ← selectCore source index fuel
    return ← checkedCell (mkApp f selected.cell)
      (← mkAppM ``ConnectionFrameLookup.map_some #[f, source, index, selected.cell, selected.proof])
  if xs.isAppOf ``List.append then
    let left := args[args.size - 2]!
    let right := args.back!
    let size ← length left
    if let some bound ← arithmetic? ``Nat.le size index fuel then
      let offset := mkApp2 (mkConst ``Nat.sub) index size
      let normalized ← normalizeNat offset fuel
      let next := normalized.value
      let selected ← selectCore right next fuel
      return ⟨selected.cell, ← mkAppM ``ConnectionFrameLookup.append_right
        #[left, right, index, next, selected.cell, bound, normalized.proof, selected.proof]⟩
    let bound ← requireArithmetic ``Nat.lt index size fuel
    let selected ← selectCore left index fuel
    return ⟨selected.cell, ← mkAppM ``ConnectionFrameLookup.append_left
      #[left, right, index, selected.cell, bound, selected.proof]⟩
  if xs.isAppOf ``List.set then
    let source := args[1]!
    let position := args[2]!
    let cell := args[3]!
    if let some same ← arithmetic? ``Eq index position fuel then
      let bound ← requireArithmetic ``Nat.lt index (← length source) fuel
      return ← checkedCell cell (← mkAppM ``ConnectionFrameLookup.set_self
        #[source, index, position, cell, same, bound])
    let different ← requireArithmetic ``Ne position index fuel
    let selected ← selectCore source index fuel
    return ⟨selected.cell, ← mkAppM ``ConnectionFrameLookup.set_other
      #[source, index, position, cell, selected.cell, different, selected.proof]⟩
  if xs.isAppOf ``List.cons then
    let cell := args[1]!
    let tail := args[2]!
    -- Concrete placements need no arithmetic search at each list cell. The
    -- same compositional laws check literal predecessors directly.
    let literal := if index.isAppOfArity ``OfNat.ofNat 3 then
      index.getAppArgs[1]!.rawNatLit? else index.rawNatLit?
    if let some literal := literal then
      if literal == 0 then
        return ← checkedCell cell (← mkAppM ``ConnectionFrameLookup.cons_zero
          #[cell, tail, index, ← mkEqRefl index])
      let previous := mkRawNatLit (literal - 1)
      let selected ← selectCore tail previous fuel
      return ⟨selected.cell, ← mkAppM ``ConnectionFrameLookup.cons_next
        #[cell, tail, index, previous, selected.cell, ← mkEqRefl index, selected.proof]⟩
    if let some same ← arithmetic? ``Eq index (mkNatLit 0) fuel then
      return ← checkedCell cell (← mkAppM ``ConnectionFrameLookup.cons_zero #[cell, tail, index, same])
    let _ ← requireArithmetic ``Nat.lt (mkNatLit 0) index fuel
    let previous := mkApp2 (mkConst ``Nat.sub) index (mkNatLit 1)
    let same ← requireArithmetic ``Eq index (mkApp2 (mkConst ``Nat.add) previous (mkNatLit 1)) fuel
    let selected ← selectCore tail previous fuel
    return ⟨selected.cell, ← mkAppM ``ConnectionFrameLookup.cons_next
      #[cell, tail, index, previous, selected.cell, same, selected.proof]⟩
  if xs.isAppOf ``List.nil then throwError "layout-lookup-out-of-bounds"
  if let some expanded ← unfoldOwner xs then return ← selectCore expanded index fuel
  -- These finite suffix builders contain no caller layout. Reduce only their
  -- spine, after all determining data is known.
  if [``ConnectionComputation.cells, ``ConnectionFrame.profileCells,
      ``ConnectionFrame.roleCells].any xs.isAppOf && !xs.hasExprMVar then
    let expanded ← whnf xs
    if expanded != xs then return ← selectCore expanded index fuel
  -- Checked syntax declarations form a DAG of finite data. Open just the
  -- selected node, retaining all shared predecessor nodes as constants.
  if let .const name _ := xs then
    if (Syntax.checkedSyntax.getState (← getEnv)).contains name then
      if let some expanded ← unfoldDefinition? xs then
        return ← selectCore expanded index fuel
  if let .letE _ _ value body _ := xs then
    return ← selectCore (body.instantiate1 value) index fuel
  throwError "layout-lookup-unsupported-or-opaque-spine: {xs.getAppFn}"

/-- Select before enumerating a readback frame. Refusal has no metavariable
effects. Only `Layout scope` is admitted, even though the proof laws are generic. -/
def select? (layout index : Expr) (fuel : Nat := 256) : MetaM (Option Selection) := do
  let saved ← saveState
  try
    let type ← whnf (← inferType layout)
    unless type.isAppOf ``List && type.getAppArgs.back!.isAppOf ``ConnectionFrame.Cell do
      throwError "layout-lookup-not-a-cell-layout"
    let index ← instantiateMVars index
    if index.hasExprMVar then
      let _ ← normalizeNat index fuel
    let selected ← selectCore layout index fuel
    return some selected
  catch error =>
    saved.restore
    if error.isRuntime || error.isInterrupt then throw error
    trace[zkc.connection.layoutLookup] "selection refused: {error.toMessageData}"
    return none

/-- Solve only `layout[index]? = some expectedCell`. Only the selected cell
is unified; unknown determining indices and predecessors defer unchanged. -/
def propose (goal : MVarId) : MetaM Bool := goal.withContext do
  let saved ← saveState
  try
    let type ← instantiateMVars (← goal.getType)
    unless type.isAppOf ``Eq do return false
    let left ← canonicalHead type.getAppArgs[1]!
    let right := type.getAppArgs[2]!
    trace[zkc.connection.layoutLookup] "query heads: {left.getAppFn} / {right.getAppFn}"
    unless left.isAppOf ``List.get?Internal && right.isAppOf ``Option.some do return false
    let arguments := left.getAppArgs
    let some selected ← select? arguments[arguments.size - 2]! arguments.back!
      | saved.restore; return false
    unless ← isDefEq selected.cell right.getAppArgs.back! do
      throwError "layout-lookup-concrete-cell-mismatch"
    goal.assign selected.proof
    return true
  catch error =>
    saved.restore
    if error.isRuntime || error.isInterrupt then throw error
    trace[zkc.connection.layoutLookup] "goal refused: {error.toMessageData}"
    return false

/-- Infer an internal reference from an already fixed cell in a fully explicit
finite frame. This is separate from selection: an unknown cell or opaque caller
prefix is never guessed. The chosen index is checked by kernel conversion. -/
def inferIndex (goal : MVarId) (fuel : Nat := 256) : MetaM Bool := goal.withContext do
  let saved ← saveState
  try
    let type ← instantiateMVars (← goal.getType)
    unless type.isAppOf ``Eq do return false
    let left ← canonicalHead type.getAppArgs[1]!
    let right := type.getAppArgs[2]!
    unless left.isAppOf ``List.get?Internal && right.isAppOf ``Option.some do return false
    let args := left.getAppArgs
    let layout := args[args.size - 2]!
    let index := args.back!
    let expected := right.getAppArgs.back!
    let layoutType ← whnf (← inferType layout)
    unless layoutType.isAppOf ``List && layoutType.getAppArgs.back!.isAppOf ``ConnectionFrame.Cell do
      return false
    trace[zkc.connection.layoutLookup] "reference inference: hole={index.isMVar}, layoutOpen={layout.hasExprMVar}, cellOpen={expected.hasExprMVar}"
    unless index.isMVar && !layout.hasExprMVar && !expected.hasExprMVar do return false
    let mut rest := layout
    for position in [:fuel] do
      rest ← whnf rest
      unless rest.isAppOf ``List.cons do
        saved.restore
        return false
      let cell := rest.getAppArgs[1]!
      if ← isDefEq cell expected then
        trace[zkc.connection.layoutLookup] "reference inferred: {position}"
        index.mvarId!.assign (mkNatLit position)
        goal.refl
        return true
      rest := rest.getAppArgs[2]!
    saved.restore
    return false
  catch error =>
    saved.restore
    if error.isRuntime || error.isInterrupt then throw error
    trace[zkc.connection.layoutLookup] "reference inference refused: {error.toMessageData}"
    return false

end ZkcTools.ConstructionBindings.LayoutLookup
