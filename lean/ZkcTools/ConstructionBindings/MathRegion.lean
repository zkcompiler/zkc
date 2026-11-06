module

public import Zkc.Construction.ConnectionMathApplication
public meta import ZkcTools.ConstructionBindings.TargetEquality
public meta import Lean.Elab.Tactic

public meta section

/-! Search finite source syntax against actual physical instructions. This
producer proposes only structural evidence; the kernel checks operation identity,
all inputs, both closed arms and every returned coordinate in the core rules.
No invocation result or semantic equality is proposed. -/
set_option autoImplicit false
namespace ZkcTools.ConstructionBindings.MathRegion
open Lean Meta Elab Tactic
open Zkc.Source Zkc.Source.Structured Zkc.Construction

structure Slice where
  spine : Expr
  suffixBlock : Expr
  yielded : Expr
  extent : Expr
  certificate : Expr

private def selected (locations operands : Expr) : MetaM (Expr × Expr) := do
  let actual ← whnf (← mkAppM ``ConnectionCalculations.operandReferences #[locations, operands])
  unless actual.isAppOf ``Option.some do throwError "alignment-computation-operand-not-data"
  return (actual.getAppArgs.back!, ← mkEqRefl actual)

private def extension (locations extent types : Expr) : MetaM (Expr × Expr) := do
  let count ← mkAppM ``List.length #[types]
  let added ← mkAppM ``ConnectionMathFrames.allocated #[extent, count]
  return (← mkAppM ``List.append #[added, locations], ← mkAppM ``Nat.add #[extent, count])

private def variant (expr : Expr) (head : Name) (failure : String) : MetaM (Array Expr) := do
  let value ← whnf expr
  unless value.isAppOf head do throwError "alignment-computation-{failure}"
  return value.getAppArgs

/-- Return the first unconsumed actual instruction along with a proof of the
exact consumed prefix. A callback must consume its entire own block. -/
partial def propose (definitions model locations extent source target : Expr) : TacticM Slice := withIncRecDepth do
  let source ← whnf source
  let parts := source.getAppArgs
  if source.isAppOf ``Region.ret then
    let positions := parts.back!
    let (references, read) ← selected locations positions
    let certificate ← mkAppOptM ``ConnectionMathRegion.Alignment.returned
      #[some definitions, none, none, some positions, some locations, some extent, some references, some read]
    return ⟨mkConst ``ConnectionTargetPrefix.Prefix.empty, target, references, extent, certificate⟩
  unless source.isAppOf ``Region.letOp do throwError "alignment-computation-source-region: {source.getAppFn}"
  let op ← whnf parts[parts.size - 4]!
  let operands := parts[parts.size - 3]!
  let regions := parts[parts.size - 2]!
  let next := parts.back!
  let target ← TargetEquality.expose target
  unless target.isAppOf ``Domain.View.sequence do throwError "alignment-computation-missing-step"
  let first := target.getAppArgs[1]!
  let rest := target.getAppArgs[2]!
  let view ← TargetEquality.expose first
  let physical := view.getAppArgs
  let yes ← mkEqRefl (mkConst ``Bool.true)
  let finish (tail : Slice) (certificate : Expr) : TacticM Slice := do
    let spine ← mkAppM ``ConnectionTargetPrefix.Prefix.step #[← mkLambdaFVars #[model] first, tail.spine]
    return {tail with spine, certificate}
  if op.isAppOf ``Op.branch then
    unless view.isAppOf ``Domain.View.mathBranch do throwError "alignment-computation-branch-mismatch"
    let captures := op.getAppArgs[0]!
    let results := op.getAppArgs[1]!
    let args ← variant operands ``Values.cons "branch-operands"
    let arm0 ← variant regions ``Regions.cons "branch-first-arm"
    let arm1 ← variant arm0.back! ``Regions.cons "branch-second-arm"
    let yesSource := arm0[arm0.size - 2]!
    let noSource := arm1[arm1.size - 2]!
    let (references, read) ← selected locations operands
    let physicalReferences ← mkAppM ``List.cons #[physical[2]!, physical[3]!]
    unless ← isDefEq references physicalReferences do throwError "alignment-computation-operand-mismatch"
    let count ← mkAppM ``List.length #[captures]
    let armLocations ← mkAppM ``ConnectionMathRegion.arguments #[count]
    let yesSlice ← propose definitions model armLocations count yesSource physical[7]!
    let noSlice ← propose definitions model armLocations count noSource physical[8]!
    for arm in [yesSlice, noSlice] do
      unless (← TargetEquality.expose arm.suffixBlock).isAppOf ``Domain.View.empty do
        throwError "alignment-computation-unconsumed-arm"
    let (extended, nextExtent) ← extension locations extent results
    let tail ← propose definitions model extended nextExtent next rest
    let yesInputs ← mkEqRefl (← mkAppM ``InstructionRegion.inputs #[physical[5]!])
    let noInputs ← mkEqRefl (← mkAppM ``InstructionRegion.inputs #[physical[6]!])
    let formed ← mkEqRefl (← mkAppOptM ``Except.ok #[some (mkConst ``String), some (mkConst ``Unit), some (mkConst ``Unit.unit)])
    let certificate ← mkAppOptM ``ConnectionMathRegion.Alignment.selected
      #[some definitions, none, some captures, some results, none, some physical[1]!,
        some args[args.size - 2]!, some args.back!, some yesSource, some noSource, some next,
        some locations, some extent, some physical[2]!, some physical[3]!, some read, some yes, some yes,
        some physical[5]!, some physical[6]!, some yesInputs, some noInputs, some formed,
        some (← mkLambdaFVars #[model] physical[7]!), some (← mkLambdaFVars #[model] physical[8]!),
        none, none, none, none, none, some yesSlice.certificate, some noSlice.certificate, some tail.certificate]
    return ← finish tail certificate
  let operation ← variant (← mkAppM ``Calculation.ofOp? #[op]) ``Option.some "unsupported-operation"
  let operation := operation.back!
  unless view.isAppOf ``Domain.View.calculation do
    throwError "alignment-computation-expected-calculation"
  unless ← isDefEq operation physical[1]! do
    throwError "alignment-computation-operation-mismatch: expected {operation}, actual {view.getAppFn}"
  let (references, read) ← selected locations operands
  unless ← isDefEq references physical[2]! do throwError "alignment-computation-operand-mismatch"
  let results ← mkAppM ``Op.results #[op]
  let (extended, nextExtent) ← extension locations extent results
  let tail ← propose definitions model extended nextExtent next rest
  let certificate ← mkAppOptM ``ConnectionMathRegion.Alignment.calculation
    #[some definitions, none, none, some operation, some operands, some next,
      some locations, some extent, some references, some read, some yes, some yes,
      none, none, none, some tail.certificate]
  finish tail certificate

end ZkcTools.ConstructionBindings.MathRegion
