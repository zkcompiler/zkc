module

public import ZkcSecurity.Domains.KoalaBear

/-!
Independent mathematical clients of the octic domain adapter. These controls
do not construct a catalogue admission or an endpoint receipt. In particular,
a constant-zero function cannot stand in for a lawful base embedding.
-/

public section

set_option autoImplicit false
set_option warningAsError true

namespace TestsSecurity.KoalaBearDomain

open ZkcSecurity.Domains.KoalaBear Polynomial CompPoly.Extension

example : q = 2130706433 := rfl
example : Nat.Prime q := q_prime
example : Field Base := inferInstance
example : Field Octic := inferInstance
example : Nonempty (Field Quotient) := ⟨inferInstance⟩
example : Finite Octic := inferInstance
example : Fintype Octic := inferInstance
example : CharP Base q := inferInstance

example : Fintype.card Base = q := card_base
example : Fintype.card Octic = q ^ 8 := card_octic
example : Nat.card Octic = q ^ 8 := nat_card_octic
example : Fintype.card Quotient = q ^ 8 := card_quotient
example : (inferInstance : Field Octic).toCommRing =
    (inferInstance : CommRing Octic) := octic_field_extends_ring
example : (inferInstance : Field Octic).inv =
    (inferInstance : Inv Octic).inv := octic_field_inverse

example : octicPolynomial = (X : Base[X]) ^ 8 - C 3 := octicPolynomial_eq
example : Irreducible octicPolynomial := octicPolynomial_irreducible
example : 8 ∣ q ^ 8 - 1 := eight_dvd_top
example : 8 ∣ q ^ 4 - 1 := eight_dvd_mid
example : 3 ^ ((q ^ 8 - 1) / 8) % q = 1 := rabin_top_mod
example : 3 ^ ((q ^ 4 - 1) / 8) % q = q - 1 := rabin_mid_mod

example : Function.Injective embed := embed_injective
example (a b : Base) : embed (a + b) = embed a + embed b := embed.map_add a b
example (a b : Base) : embed (a * b) = embed a * embed b := embed.map_mul a b
example : embed 1 = 1 := embed.map_one
example (a : Base) : embed a = algebraMap Base Octic a := rfl
example (a : Base) : quotientEquiv (embed a) = algebraMap Base Quotient a :=
  quotientEquiv_embed a
example : generator ^ 8 = embed 3 := generator_pow_eight
example (p : Base[X]) :
    quotientEquiv (p.eval₂ embed generator) = AdjoinRoot.mk octicPolynomial p :=
  quotientEquiv_eval p
example (x : Octic) : quotientEquiv.symm (quotientEquiv x) = x :=
  quotientEquiv.symm_apply_apply x
example (x : Octic) (hx : x ≠ 0) : x * x⁻¹ = 1 := mul_inv_cancel₀ (G₀ := Octic) hx
example (x : Octic) : x⁻¹ = x ^ (q ^ 8 - 2) := inverse_eq_pow x

/-- Cancellation and injectivity suffice for the independent algebraic implication. -/
theorem equality_of_checks (a b : Base) (u c : Octic)
    (ha : u + c = embed a + c) (hb : u + c = embed b + c) : a = b :=
  embed_injective (add_right_cancel (ha.symm.trans hb))

/-- A deliberately unlawful candidate embedding. -/
def zeroEmbedding : Base → Octic := fun _ => 0

theorem zeroEmbedding_not_injective : ¬ Function.Injective zeroEmbedding := by
  intro h
  exact zero_ne_one (h (show zeroEmbedding 0 = zeroEmbedding 1 from rfl))

theorem zeroEmbedding_not_ringHom :
    ¬ ∃ f : Base →+* Octic, (f : Base → Octic) = zeroEmbedding := by
  rintro ⟨f, hf⟩
  have h : f 1 = 0 := congrFun hf 1
  rw [map_one] at h
  exact one_ne_zero h

theorem zeroEmbedding_not_quotientAgreement :
    ¬ ∀ a : Base, quotientEquiv (zeroEmbedding a) = algebraMap Base Quotient a := by
  intro h
  have hOne := h 1
  have hZero : quotientEquiv (zeroEmbedding 1) = 0 := quotientEquiv.map_zero
  rw [hZero, map_one] at hOne
  exact zero_ne_one hOne

end TestsSecurity.KoalaBearDomain
