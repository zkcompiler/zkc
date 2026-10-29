import Tests.Companions
import ZkcTools.Companions.Assembly

set_option autoImplicit false
open Lean Elab Command Term Meta ZkcTools.Companions

run_elab do
  let expected := Lean.mkConst ``True
  let good : DefaultMethod := ⟨"truth", ← `(term| True.intro)⟩
  let bad : DefaultMethod := ⟨"wrong-type", ← `(term| (0 : Nat))⟩
  let result ← assemble #[] expected #[bad, good]
  match result with
  | .discharged value method attempts =>
      unless method == "truth" && attempts.size == 1 do
        throwError "default methods did not retain their ordered refusals"
      unless ← isDefEq (← inferType value) expected do throwError "default changed the meaning"
  | _ => throwError "a valid default was not selected"
  let unresolved ← assemble #[] expected #[bad]
  unless (match unresolved with | .openObligation _ attempts => attempts.size == 1 | _ => false) do
    throwError "an unavailable default was not left open"
  let target ← elabTerm (← `(term| 3 + 0 = (3 : Nat))) none
  let pending ← assemble #[⟨"Counter.pending", #[← `(term| 3)]⟩] target #[⟨"rfl", ← `(term| rfl)⟩]
  unless (match pending with | .openObligation _ _ => true | _ => false) do
    throwError "a default silently replaced an explicit unfinished companion"
  let overridden ← assemble #[⟨"Counter.base", #[← `(term| 3)]⟩] target #[bad]
  unless (match overridden with
    | .discharged _ method attempts => method == "companion:Counter.base" && attempts.isEmpty
    | _ => false) do
    throwError "an imported companion did not override defaults"
  let wrong ← assemble #[⟨"Counter.base", #[← `(term| 3)]⟩] expected #[good]
  unless (match wrong with | .refused _ _ => true | _ => false) do
    throwError "a default hid an ill-typed explicit companion"
