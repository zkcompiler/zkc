module

public import CompPoly.Fields.Extension.Binomial
public import CompPoly.Fields.Extension.Field
public import CompPoly.Fields.KoalaBear.Basic
import Mathlib.Tactic.ReduceModChar

/-!
# KoalaBear and its octic binomial extension

The base is CompPoly's prime field of order `2130706433`. The octic uses
CompPoly's coefficient arithmetic, with a proved ring equivalence to
`Fq[X] / (X^8 - 3)`. Its field laws reuse that quotient bridge and the
kernel-checked binomial irreducibility certificate below. No new algebra
instances replace the operations provided by CompPoly.

Coordinates are coefficients in increasing powers of the adjoined root.
This mathematical representation theorem does not identify native arithmetic,
storage, byte codecs, providers or sampling with these operations. Catalogue
admission, interpreted embedding operations and the mixed-domain endpoint
remain separate obligations.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

namespace ZkcSecurity.Domains.KoalaBear

open CompPoly.Extension Polynomial

/-- The actual KoalaBear prime, written as a numeral for modular computation. -/
abbrev q : ℕ := 2130706433

/-- Reuse the pinned library's prime-field carrier and its existing instances. -/
abbrev Base : Type := _root_.KoalaBear.Field

theorem q_eq_fieldSize : q = _root_.KoalaBear.fieldSize := by
  norm_num [_root_.KoalaBear.fieldSize]

theorem q_prime : Nat.Prime q := _root_.KoalaBear.is_prime

@[simp] theorem card_base : Fintype.card Base = q := ZMod.card _

theorem nat_card_base : Nat.card Base = q := by
  rw [Nat.card_eq_fintype_card, card_base]

/-- The two integer divisibility conditions in the collapsed Rabin test. -/
theorem eight_dvd_top : 8 ∣ q ^ 8 - 1 := by norm_num

theorem eight_dvd_mid : 8 ∣ q ^ 4 - 1 := by norm_num

theorem primeFactors_eight : (8 : ℕ).primeFactors = {2} := by
  rw [show (8 : ℕ) = 2 ^ 3 from by norm_num,
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two]

/-- Modular repeated squaring produces a proof term checked by the kernel. -/
theorem rabin_top : (3 : Base) ^ ((q ^ 8 - 1) / 8) = 1 := by
  show (3 : ZMod q) ^ ((q ^ 8 - 1) / 8) = 1
  reduce_mod_char

/-- The unique proper-subdegree test gives `-1`, rather than `1`. -/
theorem rabin_mid : (3 : Base) ^ ((q ^ 4 - 1) / 8) = -1 := by
  show (3 : ZMod q) ^ ((q ^ 4 - 1) / 8) = -1
  reduce_mod_char

theorem rabin_mid_ne_one : (3 : Base) ^ ((q ^ 4 - 1) / 8) ≠ 1 := by
  rw [rabin_mid]
  decide

/-- The same modular-power certificate stated in natural-number arithmetic. -/
theorem rabin_top_mod : 3 ^ ((q ^ 8 - 1) / 8) % q = 1 := by
  have hp : ((3 ^ ((q ^ 8 - 1) / 8) : ℕ) : ZMod q) = 1 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using rabin_top
  have h := congrArg (ZMod.val : ZMod q → ℕ) hp
  simpa only [ZMod.val_natCast, ZMod.val_one] using h

theorem rabin_mid_mod : 3 ^ ((q ^ 4 - 1) / 8) % q = q - 1 := by
  have hp : ((3 ^ ((q ^ 4 - 1) / 8) : ℕ) : ZMod q) = -1 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using rabin_mid
  have h := congrArg (ZMod.val : ZMod q → ℕ) hp
  calc
    _ = 2130706432 := by simpa only [ZMod.val_natCast, ZMod.val_neg_one] using h
    _ = q - 1 := by norm_num

/-- The specified degree-eight binomial, with the certified base cardinality. -/
def octicParams : BinomialParams Base where
  d := 8
  W := 3
  two_le := by norm_num
  q := q

instance baseCardinality : Fact (Nat.card Base = octicParams.q) := ⟨nat_card_base⟩

/-- The general monic presentation is exactly `X^8 - 3`. -/
noncomputable abbrev octicPolynomial : Base[X] := octicParams.toExtensionParams.poly

@[simp] theorem octicPolynomial_eq : octicPolynomial = (X : Base[X]) ^ 8 - C 3 :=
  octicParams.toExtensionParams_poly

theorem octicPolynomial_irreducible : Irreducible octicPolynomial := by
  rw [octicPolynomial_eq]
  refine irreducible_X_pow_sub_C card_base (by norm_num) (by decide)
    eight_dvd_top ?_ rabin_top ?_
  · simp only [primeFactors_eight, Finset.mem_singleton]
    rintro ℓ rfl
    exact eight_dvd_mid
  · simp only [primeFactors_eight, Finset.mem_singleton]
    rintro ℓ rfl
    exact rabin_mid_ne_one

instance octicIrreducible : Fact (Irreducible octicParams.toExtensionParams.poly) :=
  ⟨octicPolynomial_irreducible⟩

/-- CompPoly's computable realization of the specified polynomial quotient. -/
abbrev Octic : Type := Ext octicParams.toExtensionParams

/-- The mathematical quotient, whose defining polynomial is `X^8 - 3`. -/
abbrev Quotient : Type := AdjoinRoot octicPolynomial

/-- The existing field instance extends the existing coefficient ring instance. -/
theorem octic_field_extends_ring :
    (inferInstance : Field Octic).toCommRing = (inferInstance : CommRing Octic) := rfl

theorem octic_field_inverse :
    (inferInstance : Field Octic).inv = (inferInstance : Inv Octic).inv := rfl

@[simp] theorem card_octic : Fintype.card Octic = q ^ 8 := Ext.card_ext

theorem nat_card_octic : Nat.card Octic = q ^ 8 := Ext.nat_card_ext

theorem card_quotient : Fintype.card Quotient = q ^ 8 := Ext.card_quot

/-- A bijective ring map to the actual quotient, not just a cardinality match. -/
noncomputable def quotientEquiv : Octic ≃+* Quotient :=
  Ext.ringEquivQuot octicParams.toExtensionParams

@[simp] theorem quotientEquiv_apply (x : Octic) : quotientEquiv x = Ext.toQuot x := rfl

/-- The base embedding uses the same operations as the octic field instance. -/
def embed : Base →+* Octic := Ext.ofBaseRingHom octicParams.toExtensionParams

theorem embed_injective : Function.Injective embed := embed.injective

@[simp] theorem embed_eq_ofBase (a : Base) : embed a = Ext.ofBase a := rfl

theorem embed_eq_algebraMap : embed = algebraMap Base Octic := rfl

@[simp] theorem quotientEquiv_embed (a : Base) :
    quotientEquiv (embed a) = algebraMap Base Quotient a := Ext.toQuot_ofBase a

/-- The image of `X`, with CompPoly's coefficient representation. -/
def generator : Octic := Ext.gen

@[simp] theorem quotientEquiv_generator :
    quotientEquiv generator = AdjoinRoot.root octicPolynomial := Ext.toQuot_gen

@[simp] theorem generator_pow_eight : generator ^ 8 = embed 3 :=
  Ext.gen_pow_d_binomial octicParams

theorem aeval_generator : aeval generator octicPolynomial = 0 := Ext.aeval_gen_poly

/-- The quotient map evaluates the eight stored coefficients at the quotient root. -/
theorem quotientEquiv_coefficients (x : Octic) :
    quotientEquiv x = ∑ i : Fin 8,
      algebraMap Base Quotient (Ext.coeff x i) *
        AdjoinRoot.root octicPolynomial ^ (i : ℕ) := rfl

/-- Evaluating any base polynomial agrees with its class in the quotient. -/
theorem quotientEquiv_eval (p : Base[X]) :
    quotientEquiv (p.eval₂ embed generator) = AdjoinRoot.mk octicPolynomial p := by
  change quotientEquiv.toRingHom (p.eval₂ embed generator) = _
  rw [Polynomial.hom_eval₂]
  have hmap : quotientEquiv.toRingHom.comp embed = algebraMap Base Quotient := by
    ext a
    exact quotientEquiv_embed a
  rw [hmap]
  change p.eval₂ (algebraMap Base Quotient) (quotientEquiv generator) = _
  rw [quotientEquiv_generator, ← aeval_def, AdjoinRoot.aeval_eq]

/-- Inversion is the pinned arithmetic operation certified by the field laws. -/
theorem inverse_eq_pow (x : Octic) : x⁻¹ = x ^ (q ^ 8 - 2) := Ext.inv_def x

end ZkcSecurity.Domains.KoalaBear
