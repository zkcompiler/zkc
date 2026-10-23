module

public meta import Lean

@[expose] public meta section

/-! Read closed string data from checked expressions. Only standard string
concatenation and natural-number formatting are interpreted; unresolved terms
are refused. Pretty-printed text is never treated as a semantic identifier. -/
namespace ZkcTools.ClosedString
open Lean Meta

/-- Reduction can discard irrelevant semantic fields of a noncomputable record.
Only the selected closed data must normalize; no proof or runtime evaluator is
used to decide a proposition. The fuel bounds diagnostic extraction. -/
def read : Nat → Expr → MetaM String
  | 0, _ => throwError "closed string exceeds extraction limit"
  | fuel + 1, expression => do
    let expression ← instantiateMVars expression
    if let some value := getStringValue? expression then return value
    let arguments := expression.getAppArgs
    if expression.isAppOfArity ``HAppend.hAppend 6 ||
        expression.isAppOfArity ``String.append 2 then
      let left := arguments[arguments.size - 2]!
      let right := arguments.back!
      unless ← isDefEq expression (← mkAppM ``String.append #[left, right]) do
        throwError "closed string uses a nonstandard append"
      return (← read fuel left) ++ (← read fuel right)
    if expression.isAppOfArity ``toString 3 || expression.isAppOfArity ``Nat.repr 1 then
      let natural := arguments.back!
      unless ← isDefEq expression (← mkAppM ``Nat.repr #[natural]) do
        throwError "closed string uses a nonstandard natural conversion"
      let some value ← getNatValue? (← withTransparency .all (whnf natural))
        | throwError "closed string contains an unresolved natural"
      return toString value
    let reduced ← withTransparency .all <| withCanUnfoldPred (fun config info => do
      if [``HAppend.hAppend, ``String.append, ``toString, ``Nat.repr].contains info.name then
        return false
      canUnfoldDefault config info)
      (whnf expression)
    if reduced == expression then
      throwError "claim data contains an unresolved string: {expression}"
    read fuel reduced

end ZkcTools.ClosedString
