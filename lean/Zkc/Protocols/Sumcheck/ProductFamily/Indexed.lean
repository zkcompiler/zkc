import Zkc.Protocols.Sumcheck.ProductFamily.Expressions

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck.ProductFamily
open Zkc.Protocols.AlgebraicRounds.Scalar

open Zkc.Protocols.AlgebraicRounds.Scalar Zkc.Protocols.Sumcheck.ProductFamily

/- Scope is a semantic predicate on the real expression language. It is not
   supplied as an assumption for the generated family: scoped_checks proves it. -/
def Before (p : Nat) : E → Prop
  | .var i => i < p
  | .add a b => Before p a ∧ Before p b
  | .mul a b => Before p a ∧ Before p b
theorem before_mono {p q : Nat} (hpq : p ≤ q) (e : E) :
    Before p e → Before q e := by
  induction e <;> simp_all [Before]
  omega
theorem before_cf (i j p : Nat) (hj : j < 3) (hp : 4+5*i ≤ p) :
    Before p (cf i j) := by simp [Before, cf]; omega
theorem before_round (i : Nat) :
    Before (roundCheck i).1 (roundCheck i).2.1 ∧
    Before (roundCheck i).1 (roundCheck i).2.2 := by
  by_cases h : i=0
  · subst i; simp [roundCheck, bound, cf, Before]
  · simp [roundCheck, h, bound, atRound, poly, cf, dr, Before]
    omega
theorem before_product (p : Nat) (acc : E) (is : List Nat)
    (ha : Before p acc) (hi : ∀ i ∈ is, 5+5*i < p) :
    Before p (productExpr acc is) := by
  induction is generalizing acc with
  | nil => exact ha
  | cons i is ih =>
    apply ih
    · exact ⟨ha, hi i (by simp)⟩
    · intro j hj; exact hi j (by simp [hj])
theorem before_final (m : Nat) :
    Before (finalCheck m).1 (finalCheck m).2.1 ∧
    Before (finalCheck m).1 (finalCheck m).2.2 := by
  constructor
  · simp [finalCheck, atRound, poly, cf, dr, Before]; omega
  · change Before (1+5*(m+1)) (productExpr (dr 0) ((List.range m).map (·+1))) ∧ _
    constructor
    · apply before_product
      · simp [Before, dr]; omega
      · intro i hi
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
        have hj' := List.mem_range.mp hj
        omega
    · simp [Before, dr, finalCheck]; omega
theorem scoped_checks (m : Nat) (c : Nat × E × E) (h : c ∈ checks m) :
    Before c.1 c.2.1 ∧ Before c.1 c.2.2 := by
  simp only [checks, List.mem_append, List.mem_map, List.mem_singleton] at h
  rcases h with ⟨i, _, rfl⟩ | rfl
  · exact before_round i
  · exact before_final m

-- A source check cannot distinguish environments agreeing on its prior values.
theorem eval_before {F : Type} [Semiring F] (p : Nat) (e : E)
    (h : Before p e) (a b : Nat → F) (hab : ∀ i < p, a i=b i) :
    e.eval a = e.eval b := by
  induction e <;> simp_all [Before, Expr.eval]
theorem checks_prefix_local {F : Type} [Semiring F]
    (m : Nat) (c : Nat × E × E) (hc : c ∈ checks m)
    (a b : Nat → F) (hab : ∀ i < c.1, a i=b i) :
    (c.2.1.eval a=c.2.2.eval a) ↔ (c.2.1.eval b=c.2.2.eval b) := by
  obtain ⟨hl,hr⟩ := scoped_checks m c hc
  rw [eval_before c.1 c.2.1 hl a b hab, eval_before c.1 c.2.2 hr a b hab]

variable {F : Type} [CommRing F] [DecidableEq F]
def prior (env : Nat → F) (i : Nat) : F :=
  if i=0 then env 0 else value (loadRound env (i-1))
omit [DecidableEq F] in
@[simp] theorem prior_succ (env : Nat → F) (i : Nat) :
    prior env (i+1) = value (loadRound env i) := by simp [prior]

-- This endpoint is sequential: the next equality is checked only after every
-- preceding equality succeeded. Values are the represented completed trace.
def runIndexed (env : Nat → F) (i : Nat) : Nat → F → Option F
  | 0, s => some s
  | k+1, s => if boundary (loadRound env i)=s then
      runIndexed env (i+1) k (value (loadRound env i)) else none

theorem run_indexed_iff (env : Nat → F) (i k : Nat) (z : F) :
    runIndexed env i k (prior env i)=some z ↔
    (∀ j, i ≤ j → j < i+k → boundary (loadRound env j)=prior env j) ∧
      prior env (i+k)=z := by
  induction k generalizing i with
  | zero =>
    simp [runIndexed]
    intro _ j hj hk; omega
  | succ k ih =>
    by_cases hb : boundary (loadRound env i)=prior env i
    · simp only [runIndexed, hb, ↓reduceIte]
      rw [← prior_succ, ih]
      constructor
      · rintro ⟨h, hz⟩
        constructor
        · intro j hlow hhigh
          by_cases heq : j=i
          · subst j; exact hb
          · exact h j (by omega) (by omega)
        · convert hz using 1
          congr 1
          omega
      · rintro ⟨h,hz⟩
        constructor
        · intro j hlow hhigh; exact h j (by omega) (by omega)
        · convert hz using 1
          congr 1
          omega
    · simp only [runIndexed, hb, ↓reduceIte, reduceCtorEq, false_iff, not_and]
      intro h
      exact False.elim (hb (h i (by omega) (by omega)))

def sourceSatisfied (env : Nat → F) (m : Nat) : Prop :=
  ∀ c ∈ checks m, c.2.1.eval env=c.2.2.eval env
def finalTarget (env : Nat → F) (m : Nat) : F :=
  (env 5 :: ((List.range m).map (fun i => env (5+5*(i+1))))).prod + env 5

theorem source_iff_endpoint (env : Nat → F) (m : Nat) :
    sourceSatisfied env m ↔
      runIndexed env 0 (m+1) (env 0)=some (finalTarget env m) := by
  have hprior : prior env 0=env 0 := by simp [prior]
  rw [← hprior, run_indexed_iff]
  simp only [Nat.zero_add, prior_succ]
  constructor
  · intro hs
    constructor
    · intro j _ hj
      have hmem : roundCheck j ∈ checks m := by
        apply List.mem_append_left
        exact List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩
      exact (round_equation env j).mp (hs _ hmem)
    · have hmem : finalCheck m ∈ checks m := by simp [checks]
      have h := hs _ hmem
      change (atRound m).eval env=(finalCheck m).2.2.eval env at h
      rw [eval_atRound, eval_final_rhs] at h
      exact h
  · rintro ⟨hr,hf⟩ c hc
    simp only [checks, List.mem_append, List.mem_map, List.mem_singleton] at hc
    rcases hc with ⟨j,hj,rfl⟩ | rfl
    · exact (round_equation env j).mpr (hr j (by omega) (List.mem_range.mp hj))
    · change (atRound m).eval env=(finalCheck m).2.2.eval env
      rw [eval_atRound, eval_final_rhs]
      exact hf

-- Connect the indexed endpoint with the preceding actual round-list semantics.
theorem run_indexed_list (env : Nat → F) (i k : Nat) (s : F) :
    runIndexed env i k s =
      run s ((List.range' i k).map (loadRound env)) := by
  induction k generalizing i s with
  | zero => simp [runIndexed, run]
  | succ k ih => simp [runIndexed, List.range'_succ, run, ih]


end Zkc.Protocols.Sumcheck.ProductFamily
