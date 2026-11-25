module

public import ZkcFormal.ComputedTypes
public meta import Lean

public meta section
open Lean Meta Elab Tactic

/-!
The binders of a generated proposition, under the names that the generator gave them.

In a generated judgment, `claim_intro` introduces `path`, each verifier input as
`input_<port>` with its `valid_input_<port>` hypothesis, and the rejection premise
`rejected`. The statements module opens `F`, `G`, `D`, `model`, `samplers`, `served` and
`large` from the standard interpretation. The tactic takes each binder's name from the
proposition and leaves an anonymous premise anonymous. A binder of
data (an input, the path) is introduced at its computed type, as a reply of the walk is, so
that a law about a value of the field or about a list of them applies to it as it stands.
-/

namespace ZkcFormal.Written

/-- How many binders a proposition begins with. -/
private def leadingBinders : Expr → Nat
  | .forallE _ _ body _ => leadingBinders body + 1
  | .mdata _ e => leadingBinders e
  | _ => 0

/-- **Introduce what a generated proposition binds, by its own names.** A goal that is the name
of a proposition is replaced by the proposition first, as often as it takes to reach its
binders. -/
elab "claim_intro" : tactic => liftMetaTactic fun goal => do
  let mut goal := goal
  let mut target ← whnfCore (← instantiateMVars (← goal.getType))
  let mut fuel := 8
  while !target.isForall && fuel > 0 do
    let some unfolded ← unfoldDefinition? target
      | throwError "claim_intro: the goal binds nothing and is no name of a proposition{indentExpr target}"
    target ← whnfCore unfolded
    fuel := fuel - 1
  unless target.isForall do
    throwError "claim_intro: the goal binds nothing{indentExpr target}"
  goal ← goal.replaceTargetDefEq target
  let (binders, introduced) ← goal.introNP (leadingBinders target)
  let mut introduced := introduced
  for binder in binders do
    let type ← introduced.withContext do instantiateMVars (← binder.getType)
    if ← introduced.withContext do isProp type then continue
    let computed ← introduced.withContext do ZkcFormal.computedTypes type
    unless computed == type do
      introduced ← introduced.replaceLocalDeclDefEq binder computed
  return [introduced]

end ZkcFormal.Written
