import ZkcTools.Companions
import Batteries.Util.ProofWanted

set_option autoImplicit false
namespace Tests.Companions

@[zkc "Counter.base"] theorem base (n : Nat) : n + 0 = n := Nat.add_zero n
@[zkc "Counter<7>.base"] theorem seven : 7 + 0 = 7 := rfl

-- A generic theorem serves different static instances without new proofs.
example : 3 + 0 = 3 := zkc_companion ["Counter.base"[3]]
example : 11 + 0 = 11 := zkc_companion ["Counter.base"[11]]
-- A closed instance has a different telescope from its generic fallback.
example : 7 + 0 = 7 := zkc_companion ["Counter<7>.base"[], "Counter.base"[7]]
example : 13 + 0 = 13 := zkc_companion ["Counter<13>.base"[], "Counter.base"[13]]

structure LoopContract (initial : Nat) where
  invariant : Nat → Prop
  entry : invariant initial

@[zkc "Counter/round"] def counting (initial : Nat) : LoopContract initial :=
  ⟨fun value => value = initial, rfl⟩

example : LoopContract 9 := zkc_companion ["Counter/round"[9]]

-- The pinned Batteries stub records a placeholder, never a proof of its payload.
proof_wanted pending (n : Nat) : n + 0 = n
attribute [zkc "Counter.pending"] pending

open Lean Elab Command Term Meta in
run_elab do
  let placeholderGoal ← elabTerm (← `(term| 3 + 0 = (3 : Nat))) none
  let placeholder ← ZkcTools.Companions.resolve #[⟨"Counter.pending", #[← `(term| 3)]⟩] placeholderGoal
  unless (match placeholder with | .incomplete _ _ _ => true | _ => false) do
    throwError "an open companion stub supplied its unproved payload"
  let expected := Lean.mkConst ``True
  let absentResult ← ZkcTools.Companions.resolve #[⟨"unknown", #[]⟩] expected
  unless (match absentResult with | .missing => true | _ => false) do
    throwError "an unknown companion was not left open"
  let changed ← ZkcTools.Companions.resolve #[⟨"Counter.base", #[← `(term| 3)]⟩] expected
  unless (match changed with | .refused _ _ => true | _ => false) do
    throwError "a same-name companion changed the requested meaning"
  let fixed ← mkFreshExprMVar (mkSort .zero)
  let unresolved ← ZkcTools.Companions.resolve #[] fixed
  unless (match unresolved with | .refused _ _ => true | _ => false) do
    throwError "a companion was allowed to choose an unresolved meaning"
  let orphans := ZkcTools.Companions.orphaned (← getEnv) #["Counter.base", "Counter<7>.base"]
  unless orphans.any (·.identity == "Counter/round") do
    throwError "orphaned companions were not reported"

@[zkc "Counter<5>.base"] theorem wrongInstance : True := True.intro

open Lean Elab Command Term Meta in
run_elab do
  let target ← elabTerm (← `(term| 5 + 0 = (5 : Nat))) none
  let found ← ZkcTools.Companions.resolve
    #[⟨"Counter<5>.base", #[]⟩, ⟨"Counter.base", #[← `(term| 5)]⟩] target
  unless (match found with | .refused _ _ => true | _ => false) do
    throwError "a mismatched instance silently fell back to the template"

@[zkc "Collision"] theorem left : True := True.intro
@[zkc "Collision"] theorem right : True := True.intro

/-- The companion resolver must not evaluate the property it is proving. -/
def nestedProperty : Nat → Prop
  | 0 => True
  | n + 1 => nestedProperty n

theorem nestedProperty_holds (n : Nat) : nestedProperty n := by
  induction n with
  | zero => exact True.intro
  | succ _ ih => exact ih

-- Test stub inspection itself: ordinary theorem/application elaboration has
-- its own reduction policy, independently of companion discovery.
open Lean Elab Command Term Meta in
set_option maxRecDepth 128 in
run_elab do
  let proposition := mkApp (mkConst ``nestedProperty) (mkNatLit 100000)
  unless (← ZkcTools.Companions.placeholderWrapper? proposition).isNone do
    throwError "a genuine recursive proposition was classified as a stub"

open Lean Elab Command Term Meta in
run_elab do
  let found ← ZkcTools.Companions.resolve #[⟨"Collision", #[]⟩] (Lean.mkConst ``True)
  unless (match found with | .refused _ _ => true | _ => false) do
    throwError "ambiguous companion lookup depended on registration order"

end Tests.Companions
