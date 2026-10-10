import Zkc.Protocols.Sumcheck.ProductFamily.Indexed

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck.ProductFamily
open Zkc.Protocols.AlgebraicRounds.Scalar

open Zkc.Protocols.AlgebraicRounds.Scalar Zkc.Protocols.Sumcheck.ProductFamily

def OnlyValues (n : Nat) : E → Prop
  | .var i => ∃ r : Ref n, origin r=i
  | .add a b => OnlyValues n a ∧ OnlyValues n b
  | .mul a b => OnlyValues n a ∧ OnlyValues n b
theorem typed_cf (n i j : Nat) (hi : i<n) (hj : j<3) : OnlyValues n (cf i j) :=
  ⟨.coeff ⟨i,hi⟩ ⟨j,hj⟩, rfl⟩
theorem typed_dr (n i : Nat) (hi : i<n) : OnlyValues n (dr i) :=
  ⟨.draw ⟨i,hi⟩, rfl⟩
theorem typed_bound (n i : Nat) (hi : i<n) : OnlyValues n (bound i) := by
  exact ⟨⟨⟨typed_cf n i 0 hi (by omega),typed_cf n i 0 hi (by omega)⟩,
    typed_cf n i 1 hi (by omega)⟩,typed_cf n i 2 hi (by omega)⟩
theorem typed_atRound (n i : Nat) (hi : i<n) : OnlyValues n (atRound i) := by
  exact ⟨typed_cf n i 0 hi (by omega),⟨⟨typed_cf n i 1 hi (by omega),typed_dr n i hi⟩,
    ⟨typed_cf n i 2 hi (by omega),⟨typed_dr n i hi,typed_dr n i hi⟩⟩⟩⟩
theorem typed_product (n : Nat) (acc : E) (is : List Nat)
    (ha : OnlyValues n acc) (hi : ∀ i ∈ is, i<n) :
    OnlyValues n (productExpr acc is) := by
  induction is generalizing acc with
  | nil => exact ha
  | cons i is ih =>
    apply ih
    · exact ⟨ha,typed_dr n i (hi i (by simp))⟩
    · intro j hj; exact hi j (by simp [hj])
theorem typed_checks (m : Nat) (c : Nat × E × E) (h : c ∈ checks m) :
    OnlyValues (m+1) c.2.1 ∧ OnlyValues (m+1) c.2.2 := by
  simp only [checks, List.mem_append, List.mem_map, List.mem_singleton] at h
  rcases h with ⟨i,hi,rfl⟩ | rfl
  · have hi' := List.mem_range.mp hi
    constructor
    · exact typed_bound (m+1) i hi'
    · by_cases hz : i=0
      · simp only [roundCheck, hz, ↓reduceIte]; exact ⟨.claim,rfl⟩
      · simp only [roundCheck, hz, ↓reduceIte]; exact typed_atRound (m+1) (i-1) (by omega)
  · constructor
    · exact typed_atRound (m+1) m (by omega)
    · constructor
      · apply typed_product
        · exact typed_dr (m+1) 0 (by omega)
        · intro i hi
          obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
          have hj' := List.mem_range.mp hj; omega
      · exact typed_dr (m+1) 0 (by omega)

theorem eval_only_values {F : Type} [Semiring F] (n : Nat) (e : E)
    (h : OnlyValues n e) (a b : Nat → F)
    (hab : ∀ r : Ref n, a (origin r)=b (origin r)) : e.eval a=e.eval b := by
  induction e with
  | var i => obtain ⟨r,hr⟩ := h; simpa [Expr.eval,hr] using hab r
  | add a b ia ib => exact congrArg₂ (·+·) (ia h.1) (ib h.2)
  | mul a b ia ib => exact congrArg₂ (·*·) (ia h.1) (ib h.2)

-- Combined well-scoped source: no future reads, no check-position pseudo-values.
theorem source_value_independent {F : Type} [CommRing F] [DecidableEq F]
    (m : Nat) (a b : Nat → F)
    (hab : ∀ r : Ref (m+1), a (origin r)=b (origin r)) :
    sourceSatisfied a m ↔ sourceSatisfied b m := by
  unfold sourceSatisfied
  constructor <;> intro h c hc
  · obtain ⟨hl,hr⟩ := typed_checks m c hc
    rw [← eval_only_values (m+1) c.2.1 hl a b hab,
        ← eval_only_values (m+1) c.2.2 hr a b hab]
    exact h c hc
  · obtain ⟨hl,hr⟩ := typed_checks m c hc
    rw [eval_only_values (m+1) c.2.1 hl a b hab,
        eval_only_values (m+1) c.2.2 hr a b hab]
    exact h c hc

variable {F : Type} [CommRing F] [DecidableEq F]
abbrev Message (F : Type) := F × F × F
abbrev ChallengePolicy (F : Type) := List (Round F) → Message F → F
def onlineTail (draw : ChallengePolicy F) (first prefixProduct : F)
    (seen : List (Round F)) : Nat → List (Round F)
  | 0 => []
  | k+1 =>
    let a := first*2^k
    let r := draw seen (a,prefixProduct,0)
    let g : Round F := ⟨a,prefixProduct,0,r⟩
    g :: onlineTail draw first (prefixProduct*r) (seen++[g]) k
omit [DecidableEq F] in
theorem online_tail_length (draw : ChallengePolicy F) (x p : F)
    (seen : List (Round F)) (k : Nat) : (onlineTail draw x p seen k).length=k := by
  induction k generalizing p seen with
  | zero => rfl
  | succ k ih => simp [onlineTail, ih]
omit [DecidableEq F] in
theorem online_tail_honest (draw : ChallengePolicy F) (x p : F)
    (seen : List (Round F)) (k : Nat) :
    onlineTail draw x p seen k =
      honestTail x p ((onlineTail draw x p seen k).map Round.r) := by
  induction k generalizing p seen with
  | zero => rfl
  | succ k ih =>
    simp only [onlineTail, List.map_cons, honestTail, List.length_map, online_tail_length]
    congr 1
    exact ih _ _

def online (draw : ChallengePolicy F) (m : Nat) : List (Round F) :=
  let b : F := 1+2^m
  let r := draw [] (0,b,0)
  let g : Round F := ⟨0,b,0,r⟩
  g :: onlineTail draw r r [g] m
theorem online_complete (draw : ChallengePolicy F) (m : Nat) :
    run (1+2^m) (online draw m) =
      some (((online draw m).map Round.r).prod + (draw [] (0,1+2^m,0))) := by
  let r := draw [] (0,1+2^m,0)
  let tail := onlineTail draw r r [⟨0,1+2^m,0,r⟩] m
  have ht : tail=honestTail r r (tail.map Round.r) := online_tail_honest _ _ _ _ _
  have hl : (tail.map Round.r).length=m := by simp [tail,online_tail_length]
  have he : online draw m=honest r (tail.map Round.r) := by
    simp only [online, honest, hl]
    exact congrArg (List.cons (⟨0,1+2^m,0,r⟩ : Round F)) ht
  rw [he, ← hl, honest_complete]
  congr 1
  simp [honest, ← ht, r, tail, online_tail_length]


end Zkc.Protocols.Sumcheck.ProductFamily
