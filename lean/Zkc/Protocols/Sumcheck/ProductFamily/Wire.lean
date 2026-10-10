import Zkc.Protocols.Sumcheck.ProductFamily.Typed
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck.ProductFamily
open Zkc.Protocols.AlgebraicRounds.Scalar
-- Source event numbers include checks, which are absent from the wire schedule.
-- Check positions have no scalar interpretation and map to zero.
def sourceEnv {F : Type} [Zero F] (s : F) (w : Nat → F) (j : Nat) : F :=
  if j = 0 then s else
  let i := (j - 1) / 5
  match (j - 1) % 5 with
  | 0 => w (4 * i)
  | 1 => w (4 * i + 1)
  | 2 => w (4 * i + 2)
  | 4 => w (4 * i + 3)
  | _ => 0

@[simp] theorem source_claim {F : Type} [Zero F] (s : F) (w : Nat → F) :
    sourceEnv s w 0 = s := by simp [sourceEnv]

theorem source_coefficient {F : Type} [Zero F] (s : F) (w : Nat → F)
    (i j : Nat) (hj : j < 3) : sourceEnv s w (1 + 5 * i + j) = w (4 * i + j) := by
  have hp : 1 + 5 * i + j ≠ 0 := by omega
  have hq : (1 + 5 * i + j - 1) / 5 = i := by omega
  have hr : (1 + 5 * i + j - 1) % 5 = j := by omega
  simp only [sourceEnv, if_neg hp, hq, hr]
  interval_cases j <;> rfl

theorem source_challenge {F : Type} [Zero F] (s : F) (w : Nat → F)
    (i : Nat) : sourceEnv s w (5 + 5 * i) = w (4 * i + 3) := by
  have hp : 5 + 5 * i ≠ 0 := by omega
  have hq : (5 + 5 * i - 1) / 5 = i := by omega
  have hr : (5 + 5 * i - 1) % 5 = 4 := by omega
  simp only [sourceEnv, if_neg hp, hq, hr]

def runWith {F : Type} [CommRing F] [DecidableEq F]
    (evaluate : Round F → F) (env : Nat → F) (i : Nat) : Nat → F → Option F
  | 0, s => some s
  | k+1, s => if boundary (loadRound env i) = s then
      runWith evaluate env (i+1) k (evaluate (loadRound env i)) else none

theorem runWith_indexed {F : Type} [CommRing F] [DecidableEq F]
    (evaluate : Round F → F) (heval : ∀ g, evaluate g = value g)
    (env : Nat → F) (i k : Nat) (s : F) :
    runWith evaluate env i k s = Zkc.Protocols.Sumcheck.ProductFamily.runIndexed env i k s := by
  induction k generalizing i s with
  | zero => rfl
  | succ k ih => simp only [runWith, Zkc.Protocols.Sumcheck.ProductFamily.runIndexed, heval, ih]


end Zkc.Protocols.Sumcheck.ProductFamily
