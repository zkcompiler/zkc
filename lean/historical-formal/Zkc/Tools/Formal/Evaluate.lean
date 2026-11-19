import Lean
import Zkc.Core.Meaning
import Zkc.Formal.Abstract.Provider

/-! A tactic for statements that are proved along a region.

A step along a region binds the values that an operation returns (`Zkc.Formal.EveryRun.step`,
`Zkc.Formal.denote_step`). The values are given by an equation, and are written with the
environment they were read in. `evaluate_bound` replaces the values that the goal's environment
binds last by the values themselves: a reference into the environment by the value it names, a
row of the model of an arithmetic by the operation of the arithmetic, an operation on numbers by
its result. The environment of a long body then stays a list of values, each written once. The
goal it leaves is the goal it found, by evaluation.

The evaluation is from the leaves: an operation on numbers is computed once its operands are
numbers, which Lean's evaluator from the head does not do for a number that is a reference.
-/

open Lean Meta Elab Tactic

namespace Zkc.Formal

/-- The functions that only read or build values: an application of one, on evaluated
arguments, is replaced by what it evaluates to. -/
def structuralFunctions : List Name :=
  [``Zkc.Source.Environment.bindAll, ``Zkc.Source.Environment.push,
    ``Zkc.Source.Environment.ofValues, ``Zkc.Source.Values.get, ``Zkc.Source.Values.tail,
    ``Zkc.Source.Operands.eval, ``Zkc.Source.Var.cases, ``Zkc.Core.unmapValues,
    ``Zkc.Core.remapValues, ``Zkc.Core.Literal.value, ``Zkc.Core.Held.of, ``Zkc.Core.Model.pure,
    ``Zkc.Core.Ty.elements, ``Zkc.Core.Ty.pack, ``Zkc.Core.Ty.component, ``Zkc.Core.Ty.collect,
    ``Zkc.Core.Ty.concat, ``Zkc.Formal.Kind.asScalar, ``Zkc.Formal.Kind.ofScalar,
    ``Zkc.Formal.Kind.asPoint, ``Zkc.Formal.Kind.ofPoint, ``Zkc.Formal.Kind.asScalars,
    ``Zkc.Formal.Kind.ofScalars, ``Zkc.Formal.Kind.inhabitant, ``Prod.fst, ``Prod.snd, ``Subtype.val]

/-- The operations on numbers that are computed on numerals. -/
def numberFunctions : List Name :=
  [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HPow.hPow, ``HDiv.hDiv, ``HMod.hMod, ``Nat.add,
    ``Nat.sub, ``Nat.mul, ``Nat.pow]

/-- A numeral. -/
def isNumeral (e : Expr) : Bool :=
  e.isRawNatLit || (e.isAppOfArity ``OfNat.ofNat 3 && e.appFn!.appArg!.isRawNatLit)

/-- An application with the functions at its head applied, however many times one application
gives another. An annotation on a function does not hide it. -/
partial def applyHead (e : Expr) : Expr :=
  let function := e.getAppFn.consumeMData
  if function.isLambda && e.isApp then
    applyHead (mkAppN function e.getAppArgs).headBeta
  else e

/-- A value with the references and the structural functions in it evaluated, from the
leaves. Types, proofs and the bodies of functions are left as they are. -/
partial def evaluate (e : Expr) : MetaM Expr := do
  let e := applyHead (← instantiateMVars e).consumeMData
  unless e.isApp do return e
  let function := e.getAppFn
  let arguments := e.getAppArgs
  let info ← getFunInfoNArgs function arguments.size
  let mut evaluated := arguments
  for index in [0:arguments.size] do
    let explicit := match info.paramInfo[index]? with
      | some parameter => parameter.isExplicit
      | none => true
    if explicit && !(← isProof arguments[index]!) then
      evaluated := evaluated.set! index (← evaluate arguments[index]!)
  let applied := applyHead (mkAppN function evaluated)
  let head := applied.getAppFn
  let reads := match head with
    | .const name _ => structuralFunctions.contains name
    | .proj .. => true
    | _ => false
  let computes := match head with
    | .const name _ =>
        numberFunctions.contains name &&
          (applied.getAppArgs.extract (applied.getAppNumArgs - 2) applied.getAppNumArgs).all isNumeral
    | _ => false
  if reads || computes then
    let reduced ← whnf applied
    if reduced == applied then return applied else evaluate reduced
  else
    return applied

/-- The values that the goal's environment binds last, replaced by the values themselves. -/
elab "evaluate_bound" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let some binding := target.find? fun e =>
        e.getAppFn.isConstOf ``Zkc.Source.Environment.bindAll && e.getAppNumArgs ≥ 6
      | throwError "no environment of the goal binds values"
    let arguments := binding.getAppArgs
    let values := arguments[5]!
    if values.hasLooseBVars then
      throwError "the values that the environment binds depend on a bound variable"
    let reduced ← evaluate values
    let replaced := mkAppN binding.getAppFn (arguments.set! 5 reduced)
    let evaluated := target.replace fun e => if e == binding then some replaced else none
    replaceMainGoal [← goal.replaceTargetDefEq evaluated]

end Zkc.Formal
