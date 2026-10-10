import Zkc.Source.LocalArithmetic

set_option autoImplicit false

namespace Tests.LocalArithmetic
open Zkc.Source.LocalArithmetic

-- Concrete controls use the actual finite-additive Schnorr Plan formula.
-- keys: x=0, nonce=1, delivered challenge=2, verifier secret branch=3.
def commit : Program := .save (.input 1) (.emit (.mem 0) .done)
def respond : Program := .emit (.mod (.add (.mem 0) (.mul (.input 2) (.input 0))) 3) .done
def forbiddenBranch : Program := .branch (.input 3) (.emit (.lit 0) .done) (.emit (.lit 1) .done)
def events (c b : Nat) : List Event :=
  [⟨0, 0, 0, 2, none⟩, ⟨0, 0, 1, 1, some 1⟩, ⟨0, 2, 2, c, none⟩, ⟨1, 0, 3, b, none⟩]

example : checkedRun commit (observe 0 1 (events 2 0)) [] = some ⟨[1], [1]⟩ := rfl
example : checkedRun respond (observe 0 3 (events 2 0)) [1] = some ⟨[2], [1]⟩ := rfl
example : checkedRun respond (observe 0 1 (events 2 0)) [1] = none := rfl
example : checkedRun forbiddenBranch (observe 0 3 (events 2 0)) [1] = none := rfl
example : checkedRun forbiddenBranch (observe 0 4 (events 2 1 ++ [⟨0, 3, 3, 1, none⟩])) [1] = some ⟨[1], [1]⟩ := rfl

-- For arbitrary natural representatives, the handwritten fragment computes
-- exactly the source formula. Relating the source AST to this fragment remains
-- a separately identified interpretation boundary.
theorem respond_formula (x c r : Nat) :
    respond.eval (fun k => if k = 0 then x else if k = 2 then c else 0) [r] =
      ⟨[(r + c*x) % 3], [r]⟩ := by rfl

example : checkedRun (.emit (.input 1) .done) (observe 0 3 (events 2 0)) [1] = none := rfl

end Tests.LocalArithmetic
