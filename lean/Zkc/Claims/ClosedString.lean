module

public meta import Lean

@[expose] public meta section

/-! Read closed string data from checked expressions. Only standard string
concatenation and natural-number formatting are interpreted; unresolved terms
are refused. Pretty-printed text is never treated as a semantic identifier. -/
namespace Zkc.Claims.ClosedString
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
    if expression.isAppOfArity ``toString 3 then
      let value := arguments.back!
      let ty ← withTransparency .all (whnf (← inferType value))
      if ty.isConstOf ``String then
        unless ← isDefEq expression value do
          throwError "closed string uses a nonstandard string conversion"
        return ← read fuel value
    if expression.isAppOfArity ``toString 3 || expression.isAppOfArity ``Nat.repr 1 then
      let natural := arguments.back!
      unless ← isDefEq expression (← mkAppM ``Nat.repr #[natural]) do
        throwError "closed string uses a nonstandard natural conversion"
      let some value ← getNatValue? (← withTransparency .all (whnf natural))
        | throwError "closed string contains an unresolved natural"
      return toString value
    -- Stop only at the selected field's formatting operation. Internal
    -- reductions still compare computed lookup keys before selecting a field.
    -- A global unfolding ban would also block those comparisons; unrestricted
    -- root reduction would instead expose String's byte-array implementation.
    let reduced ← withTransparency .all <| whnfHeadPred expression fun term =>
      pure (!(term.isAppOf ``HAppend.hAppend || term.isAppOf ``String.append ||
        term.isAppOf ``toString || term.isAppOf ``Nat.repr))
    if reduced == expression then
      throwError "claim data contains an unresolved string: {expression}"
    read fuel reduced

end Zkc.Claims.ClosedString
