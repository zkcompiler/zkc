module

public import ZkcSecurity.Families.Gkr.Combination
public import ZkcSecurity.Algebra.Polynomial

public section

/-! Detection of a false output table at a fresh multilinear point. This is
the initial claim reduction; it does not assume that evaluation at every point
detects a false table. Each actual coordinate draw has error at most 1 / |F|.
-/

namespace ZkcSecurity.Families.Gkr.Output
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open OracleComp OracleSpec

variable {F : Type} [Field F] {width : Nat}

@[expose] def Differ (difference : Table F width) (remaining : Nat) (point : List F) : Prop :=
  point.length + remaining = width ∧ ∃ suffix : Fin remaining → Bool,
    extension width difference (coordinates width (point ++ List.ofFn (booleanPoint suffix))) ≠ 0

theorem initial (difference : Table F width) (nonzero : ∃ bits, difference bits ≠ 0) :
    Differ difference width [] := by
  obtain ⟨bits, nonzero⟩ := nonzero
  exact ⟨by simp, bits, by simpa only [List.nil_append, coordinates_ofFn, extension_boolean] using nonzero⟩

theorem terminal (difference : Table F width) (point : List F) (wrong : Differ difference 0 point) :
    point.length = width ∧ extension width difference (coordinates width point) ≠ 0 := by
  obtain ⟨length, suffix, wrong⟩ := wrong
  exact ⟨by omega, by simpa only [List.ofFn_zero, List.append_nil] using wrong⟩

theorem ofFn_booleanPoint_succ {n : Nat} (suffix : Fin (n + 1) → Bool) :
    List.ofFn (booleanPoint (F := F) suffix) =
      (if suffix 0 then 1 else 0) :: List.ofFn (booleanPoint (suffix ∘ Fin.succ)) := by
  rw [List.ofFn_succ]; rfl

variable [Fintype F] [DecidableEq F] [SampleableType F]

theorem successor (difference : Table F width) (remaining : Nat) (point : List F)
    (differ : Differ difference (remaining + 1) point) :
    Pr{let r ← $ᵗ F}[¬ Differ difference remaining (point ++ [r])] ≤
      1 / (Fintype.card F : ENNReal) := by
  classical
  obtain ⟨sized, suffix, nonzero⟩ := differ
  let tail := List.ofFn (booleanPoint (F := F) (suffix ∘ Fin.succ))
  have short : point.length < width := by omega
  let low := extension width difference (coordinates width (point ++ 0 :: tail))
  let high := extension width difference (coordinates width (point ++ 1 :: tail))
  have pair : ¬ (low = 0 ∧ high = 0) := by
    rintro ⟨lowZero, highZero⟩
    apply nonzero
    rw [ofFn_booleanPoint_succ, extension_insert difference point tail _ short]
    change (1 - _) * low + _ * high = 0
    rw [lowZero, highZero]; ring
  have count := affine_zeros_card_le low high pair
  have bound : Pr{let r ← $ᵗ F}[(1 - r) * low + r * high = 0] ≤
      1 / (Fintype.card F : ENNReal) := by
    rw [SampleableType.prEvent_uniformSample]
    exact ENNReal.div_le_div_right (by exact_mod_cast count) _
  refine (prEvent_mono _ _ (fun r => (1 - r) * low + r * high = 0)
    (fun r escaped => ?_)).trans bound
  by_contra notZero
  apply escaped
  refine ⟨by simp; omega, suffix ∘ Fin.succ, ?_⟩
  rw [List.append_assoc, List.singleton_append, extension_insert difference point tail _ short]
  exact notZero

end ZkcSecurity.Families.Gkr.Output
