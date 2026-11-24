module

public import ZkcFormal.Interactive.Sumcheck

@[expose] public section

namespace ZkcFormal.Interactive.Sumcheck
open Zkc.Core

/-- Public residual claims indexed by the number of unfixed coordinates. -/
structure Claims (F : Type) where
  State : Nat → Type
  value : (n : Nat) → State n → F
  restrict : (n : Nat) → State (n+1) → F → State n

/-- Evaluate the residual claim only at a point of the required length. -/
def Claims.evaluate {F : Type} (q : Claims F) : (n : Nat) → q.State n → List F → Option F
  | 0, x, [] => some (q.value 0 x)
  | n+1, x, r::rs => q.evaluate n (q.restrict n x r) rs
  | _, _, _ => none

/-- The verifier's public call interface. Both the received message and the subsequent
draw can depend on the complete public history and current claim. -/
structure Verifier {S : Sig} (H F M : Type) where
  receive : List F → F → Process S H M
  draw : List F → F → M → Process S H F
  reject : H
  boundary : M → F
  evaluate : M → F → F

namespace Verifier
variable {S : Sig} {H F M σ : Type} [DecidableEq F]

def reduce (v : Verifier (S := S) H F M) : Nat → List F → F → Process S H (List F × F)
  | 0, _, claim => .done ([], claim)
  | n+1, history, claim =>
    (verifierRound (v.receive history claim) (v.draw history claim) v.reject v.boundary v.evaluate claim).bind
      fun (r, nextClaim) => (v.reduce n (history ++ [r]) nextClaim).map fun (rs, value) => (r::rs, value)

def publicCoins (v : Verifier (S := S) H F M) (K : Experiment S σ) (points : List F)
    (positive : 0 < points.length) : Prop :=
  ∀ history claim s m t, K.Reaches (v.receive history claim) s m t → v.boundary m = claim →
    Fresh K points positive (v.draw history claim m) t

/-- An instance supplies a root count for its public residual claims. The theorem
charges that count at each draw reached after a passing message. -/
theorem reduce_sound (v : Verifier (S := S) H F M) (q : Claims F)
    (K : Experiment S σ) (points : List F) (positive : 0 < points.length) (degree : Nat)
    (roots : ∀ n (x : q.State (n+1)) claim m, claim ≠ q.value (n+1) x → v.boundary m = claim →
      points.countP (fun r => decide (v.evaluate m r = q.value n (q.restrict n x r))) ≤ degree)
    (fresh : v.publicCoins K points positive) (n : Nat) (x : q.State n)
    (history : List F) (claim : F) (s : σ) (wrong : claim ≠ q.value n x) :
    K.probability (v.reduce n history claim) s (fun (rs,value) _ => decide (q.evaluate n x rs = some value)) ≤
      (n : Mass) * roundCost degree points := by
  induction n generalizing history claim s with
  | zero =>
    change (if decide (some (q.value 0 x) = some claim) then (1 : Mass) else 0) ≤ 0 * roundCost degree points
    have bad : q.value 0 x ≠ claim := Ne.symm wrong
    simp [bad]
  | succ n ih =>
    have first := verifierRound_le K s points positive (v.receive history claim) (v.draw history claim) v.reject
      v.boundary v.evaluate (fun r => q.value n (q.restrict n x r)) claim degree
      (fresh history claim s) (fun m => roots n x claim m wrong)
    rw [reduce, Mass.natCast_add, Mass.natCast_one, Mass.add_mul, Mass.one_mul, Mass.add_comm]
    apply K.reduction_bind _ _ _ _ _ first (Mass.zero_le _)
    intro (r, nextClaim) t _ h
    have bad : nextClaim ≠ q.value n (q.restrict n x r) := of_decide_eq_false h
    apply Mass.le_trans _ (ih (q.restrict n x r) (history ++ [r]) nextClaim t bad)
    simp only [Experiment.probability, Process.map_eq_bind, Experiment.expect_bind, Experiment.expect_done]
    apply K.expect_mono
    intro (rs,value) _ _
    by_cases agrees : q.evaluate n (q.restrict n x r) rs = some value <;> simp [Claims.evaluate, agrees]

end Verifier
end ZkcFormal.Interactive.Sumcheck
