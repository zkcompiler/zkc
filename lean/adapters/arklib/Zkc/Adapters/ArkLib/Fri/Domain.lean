module

public import ArkLib.ProofSystem.Fri.QuerySoundness
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

@[expose] public section

/-! # The FRI library's cosets as ArkLib domains

`TwoAdicField(F)` supplies a compatible family of two-power roots
(`docs/spec/domains/polynomials.md`): `roots m` is a primitive `2^m`-th root of unity, and
squaring `roots (m + 1)` gives `roots m`. The logical order of the size-`2^m` coset with nonzero
shift `s` is `x_i = s * roots m ^ i`, and `coset::point(s, 2^m, i)` returns `x_i`.

ArkLib's `SmoothCosetFftDomain` enumerates a coset in the same natural order. `cosetDomain`
builds that domain from a shift and a primitive root, and `subdomain_one_apply` shows that
ArkLib's first subdomain is the coset with the squared shift and the squared root, which is the
domain `fri::LowDegree` moves to after each fold. `pair_sq` states that the positions `i` and
`i + 2^m` of a size-`2^(m + 1)` coset square to the same point, which is the pairing the library's
fold uses.
-/

namespace ZkcSecurity.ArkLib.Fri

open Domain

variable {F : Type} [Field F]

/-- `coset::point(shift, 2^m, position)`: the point at `position` of the size-`2^m` coset with
the given shift, in logical order. `roots m` is the installed root of log order `m`. -/
def point (roots : ℕ → F) (shift : F) (m position : ℕ) : F :=
  shift * roots m ^ position

/-- The size-`2^m` coset `i ↦ shift * root ^ i` as an ArkLib domain. -/
def cosetDomain {m : ℕ} (shift root : F) (hshift : shift ≠ 0)
    (hroot : IsPrimitiveRoot root (2 ^ m)) : SmoothCosetFftDomain m F :=
  let unit := Units.mk0 root (hroot.ne_zero (by positivity))
  have hone : unit ^ (2 ^ m) = 1 := Units.ext (by simpa [unit] using hroot.pow_eq_one)
  { subgroupDomain :=
      { toFun := fun i => unit ^ (Multiplicative.toAdd i).val
        map_one' := by simp
        map_mul' := by
          intro a b
          simp only [toAdd_mul, Fin.val_add]
          rw [← pow_add, ← pow_eq_pow_mod _ hone] }
    subgroupDomain_inj := by
      intro a b h
      have h' := congrArg Units.val h
      simp only [MonoidHom.coe_mk, OneHom.coe_mk, Units.val_pow_eq_pow_val, unit,
        Units.val_mk0] at h'
      exact Multiplicative.toAdd.injective
        (Fin.ext (hroot.pow_inj (Multiplicative.toAdd a).isLt (Multiplicative.toAdd b).isLt h'))
    cosetGenerator := Units.mk0 shift hshift }

@[simp]
theorem cosetDomain_apply {m : ℕ} (shift root : F) (hshift : shift ≠ 0)
    (hroot : IsPrimitiveRoot root (2 ^ m)) (i : Fin (2 ^ m)) :
    cosetDomain shift root hshift hroot i = shift * root ^ i.val := by
  rw [CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain]
  simp [cosetDomain, CosetFftDomain.subgroupUnit]

/-- The initial domain of `fri::LowDegree`: the size-`2^n` coset of the verifier's shift. -/
theorem cosetDomain_point {n : ℕ} (roots : ℕ → F) (shift : F) (hshift : shift ≠ 0)
    (hroot : IsPrimitiveRoot (roots n) (2 ^ n)) (i : Fin (2 ^ n)) :
    cosetDomain shift (roots n) hshift hroot i = point roots shift n i := by
  simp [point]

/-- Index `j` of the first subdomain is the image of index `j` of the larger domain. -/
theorem sqFoldMapGen_low {m : ℕ} (j : Fin (2 ^ m)) :
    CosetFftDomainClass.sqFoldMapGen (n := m + 1) (i := 1)
      (⟨j.val, by have := j.isLt; rw [pow_succ]; omega⟩ : Fin (2 ^ (m + 1))) = j :=
  Fin.ext (Nat.mod_eq_of_lt j.isLt)

/-- Index `j + 2^m` of a size-`2^(m + 1)` domain also maps to index `j` of the first subdomain. -/
theorem sqFoldMapGen_high {m : ℕ} (j : Fin (2 ^ m)) :
    CosetFftDomainClass.sqFoldMapGen (n := m + 1) (i := 1)
      (⟨j.val + 2 ^ m, by have := j.isLt; rw [pow_succ]; omega⟩ : Fin (2 ^ (m + 1))) = j := by
  apply Fin.ext
  change (j.val + 2 ^ m) % 2 ^ (m + 1 - 1) = j.val
  rw [Nat.add_sub_cancel, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]

/-- Both positions `j` and `j + 2^m` of a size-`2^(m + 1)` domain square to point `j` of
ArkLib's first subdomain. -/
theorem pair_sq {m : ℕ} (D : SmoothCosetFftDomain (m + 1) F) (j : Fin (2 ^ m)) :
    D ⟨j.val, by have := j.isLt; rw [pow_succ]; omega⟩ ^ 2 = D.subdomain 1 j ∧
      D ⟨j.val + 2 ^ m, by have := j.isLt; rw [pow_succ]; omega⟩ ^ 2 = D.subdomain 1 j := by
  constructor
  · have h := CosetFftDomainClass.pow_eq_subdomain_sqFoldMapGen (ω := D) (i := 1)
      (⟨j.val, by have := j.isLt; rw [pow_succ]; omega⟩ : Fin (2 ^ (m + 1)))
    rw [sqFoldMapGen_low] at h
    simpa using h.symm
  · have h := CosetFftDomainClass.pow_eq_subdomain_sqFoldMapGen (ω := D) (i := 1)
      (⟨j.val + 2 ^ m, by have := j.isLt; rw [pow_succ]; omega⟩ : Fin (2 ^ (m + 1)))
    rw [sqFoldMapGen_high] at h
    simpa using h.symm

/-- ArkLib's first subdomain of the coset `shift * root ^ i` is the coset
`shift^2 * (root^2) ^ j`: after a fold, `fri::LowDegree` squares its shift and moves to the
compatible root of half the size. -/
theorem subdomain_one_apply {m : ℕ} (D : SmoothCosetFftDomain (m + 1) F) (shift root : F)
    (hD : ∀ i : Fin (2 ^ (m + 1)), D i = shift * root ^ i.val) (j : Fin (2 ^ m)) :
    D.subdomain 1 j = (shift * shift) * (root ^ 2) ^ j.val := by
  rw [← (pair_sq D j).1, hD]
  ring

end ZkcSecurity.ArkLib.Fri
