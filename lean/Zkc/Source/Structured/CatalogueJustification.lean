module

public import Zkc.Source.Structured.Catalogue
public import Mathlib.NumberTheory.LucasPrimality
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

/-! Justified catalogue rows.

A catalogue row asserts data facts that the Lean meaning of its identity relies
on. The modulus of a field row is its characteristic, so it is prime, whatever
the field's degree; a `CharacteristicNotTwo` row's modulus is not two. A
catalogue is justified when every row's facts hold, and the environment
catalogue of the structured importer is proved justified here: the BLS12-381
scalar modulus is prime by a Lucas certificate evaluated in the kernel.
Presentations of extension fields (defining polynomials, bases) are not yet
catalogue data, so their irreducibility is not part of this predicate. -/

set_option autoImplicit false
namespace Zkc.Source.Structured

/-- The data facts of one row. -/
def Nominal.Justified (row : Nominal) : Prop :=
  (∀ modulus, row.modulus = some modulus → row.sort = .field → modulus.Prime) ∧
    ("CharacteristicNotTwo" ∈ row.capabilities → row.modulus ≠ some 2)

def Catalogue.Justified (catalogue : Catalogue) : Prop :=
  ∀ row ∈ catalogue.nominals, row.Justified

/-! Primality certificates. -/

/-- A prime dividing a product of prime powers is one of the primes. -/
theorem prime_mem_of_dvd_prod {q : ℕ} (prime : q.Prime) :
    ∀ (factors : List (ℕ × ℕ)), (∀ factor ∈ factors, factor.1.Prime) →
      q ∣ (factors.map fun factor => factor.1 ^ factor.2).prod → ∃ factor ∈ factors, q = factor.1
  | [], _, divides => by
    simp only [List.map_nil, List.prod_nil, Nat.dvd_one] at divides
    exact absurd divides prime.one_lt.ne'
  | factor :: rest, primes, divides => by
    simp only [List.map_cons, List.prod_cons] at divides
    rcases (Nat.Prime.dvd_mul prime).mp divides with head | tail
    · exact ⟨factor, List.mem_cons_self .., (Nat.prime_dvd_prime_iff_eq prime
        (primes factor List.mem_cons_self)).mp (prime.dvd_of_dvd_pow head)⟩
    · obtain ⟨found, member, same⟩ := prime_mem_of_dvd_prod prime rest
        (fun other member => primes other (List.mem_cons_of_mem _ member)) tail
      exact ⟨found, List.mem_cons_of_mem _ member, same⟩

/-- Lucas primality from a factorization of `p - 1` and a witness checked by
kernel-evaluated modular exponentiation. -/
theorem prime_of_certificate (p witness : ℕ) (factors : List (ℕ × ℕ)) (large : 1 < p)
    (factorization : p - 1 = (factors.map fun factor => factor.1 ^ factor.2).prod)
    (primes : ∀ factor ∈ factors, factor.1.Prime)
    (fermat : Nat.powMod witness (p - 1) p = 1)
    (order : ∀ factor ∈ factors, Nat.powMod witness ((p - 1) / factor.1) p ≠ 1) :
    p.Prime := by
  have one : 1 % p = 1 := Nat.mod_eq_of_lt large
  have cast : ∀ exponent,
      ((witness : ZMod p) ^ exponent = 1 ↔ Nat.powMod witness exponent p = 1) := by
    intro exponent
    rw [Nat.powMod_def, ← Nat.cast_pow, ← Nat.cast_one,
      ZMod.natCast_eq_natCast_iff', one]
  refine lucas_primality p witness ((cast (p - 1)).mpr fermat) ?_
  intro q prime divides
  rw [factorization] at divides
  obtain ⟨factor, member, rfl⟩ := prime_mem_of_dvd_prod prime factors primes divides
  rw [Ne, cast _]
  exact order factor member

/-- The BLS12-381 scalar modulus is prime. -/
theorem blsModulus_prime : blsModulus.Prime := by
  refine prime_of_certificate blsModulus 7
    [(2, 32), (3, 1), (11, 1), (19, 1), (10177, 1), (125527, 1), (859267, 1), (906349, 2),
      (2508409, 1), (2529403, 1), (52437899, 1), (254760293, 2)]
    (by decide +kernel) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro factor (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> norm_num

/-- The environment catalogue of the structured importer is justified. -/
theorem blsCatalogue_justified : blsCatalogue.Justified := by
  intro row member
  simp only [blsCatalogue, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · refine ⟨fun modulus same _ => ?_, fun _ same => ?_⟩
    · cases same
      exact blsModulus_prime
    · cases same
  all_goals exact ⟨fun _ same => (by cases same), fun _ => (by simp)⟩

end Zkc.Source.Structured
