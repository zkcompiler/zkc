module

public meta import Lean

public meta section
open Lean Meta Elab Tactic

/-!
The binders of a generated proposition, under the names that the generator gave them.

A statement that is generated for a goal is a proposition with named binders: what the model is
built from, the path, each input of the deciding role with its validity, and the premise. A
proof of it begins by introducing them. `intro` with a list of names counts positions, and a
text written that way changes whenever the generator adds a binder; `claim_intro` introduces
every binder with the name that the proposition has for it.
-/

namespace Zkc.Formal.Written

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
  let (_, introduced) ← goal.introNP (leadingBinders target)
  return [introduced]

end Zkc.Formal.Written
