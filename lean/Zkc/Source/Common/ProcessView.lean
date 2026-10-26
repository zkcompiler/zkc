module

public import Zkc.Source.Common.Import
public meta import Lean.Elab.Term
public meta import Lean.Elab.SyntheticMVars
public meta import Lean.Meta.Transform

@[expose] public section

namespace Zkc.Source.Common
open Lean Meta Elab Term

/-- Weak-head reduction that keeps unresolved conditionals and decisions readable.
Scalar operators retain the notation recognized by the algebraic tactics.
Known decisions still reduce through Lean's ordinary evaluator. -/
private meta partial def presentationWhnf (expression : Expr) : MetaM Expr := do
  let reduced ← whnfHeadPred expression fun expression =>
    return ![``ite, ``dite, ``decide, ``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul,
      ``HSMul.hSMul, ``OfNat.ofNat, ``NatCast.natCast, ``Neg.neg,
      ``Bool.and, ``Bool.or, ``Bool.xor].contains (expression.getAppFn.constName?.getD .anonymous)
  let args := reduced.getAppArgs
  let decision? :=
    if (reduced.isAppOf ``ite || reduced.isAppOf ``dite) && args.size == 5 then
      some args[2]!
    else if reduced.isAppOf ``decide && args.size == 2 then some args[1]!
    else none
  if let some decision := decision? then
    -- In Lean 4.35, Decidable stores its result in the first Boolean projection.
    let decision ← whnf (mkProj ``Decidable 0 decision)
    if decision.isConstOf ``Bool.true || decision.isConstOf ``Bool.false then
      return ← presentationWhnf (← unfoldDefinition reduced)
  return reduced

/-- Normalize an actual Common denotation with Lean reduction, without a second
operation or instruction evaluator. Carrier types and proofs stay shared;
propositions are normalized because runtime decisions contain scalar terms. -/
elab "common_process% " source:term : term <= expectedType => do
  let original ← elabTerm source expectedType
  synthesizeSyntheticMVarsNoPostponing
  let original ← instantiateMVars original
  let (generated, _) ← Meta.transformWithCache original {}
    (skipInstances := true) (skipConstInApp := true)
    (pre := fun expression => do
      if (← isProof expression) || ((← isType expression) && !(← isProp expression)) then
        return .done expression
      return .continue (some (← presentationWhnf expression)))
    (post := fun expression => do
      let reduced ← presentationWhnf expression
      return if reduced == expression then .done expression else .visit reduced)
  unless ← isDefEq original generated do
    throwError "common_process%: generated view differs from the actual process"
  return generated

end Zkc.Source.Common
