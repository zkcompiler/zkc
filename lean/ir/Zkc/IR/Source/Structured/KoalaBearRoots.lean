module

public import Zkc.IR.Source.Structured.NumericalCapabilities
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Arithmetic certificates for the pinned KoalaBear base-field ordering.
These concern the declared prime-field constants, not a native FFT, the octic
extension construction, its codec, or any operational resource bound. -/
namespace Zkc.Source.Structured

abbrev KoalaBearResidue := ZMod 2130706433

theorem koalaBearRootLiterals_bound :
    koalaBearRootLiterals.all (· < 2130706433) = true := by decide

theorem koalaBearRootLiterals_square :
    ((koalaBearRootLiterals.drop 1).zip koalaBearRootLiterals).all
      (fun pair ↦ decide ((pair.1 : KoalaBearResidue) ^ 2 = pair.2)) = true := by decide

/-- Every selected constant has its exact two-power order. In particular,
coordinate five is 0x0a28f031, rather than an arbitrary primitive 32nd root. -/
theorem koalaBearRootLiterals_order (k : Fin 25) :
    IsPrimitiveRoot (koalaBearRootLiterals[k.val]! : KoalaBearResidue) (2 ^ k.val) := by
  fin_cases k
  · exact IsPrimitiveRoot.one
  · change IsPrimitiveRoot (0x7f000000 : KoalaBearResidue) (2 ^ 1)
    exact IsPrimitiveRoot.iff_orderOf.mpr
      (orderOf_eq_prime_pow
        (x := (0x7f000000 : KoalaBearResidue)) (p := 2) (n := 0) (by decide) (by decide))
  · change IsPrimitiveRoot (0x7e010002 : KoalaBearResidue) (2 ^ 2)
    exact IsPrimitiveRoot.iff_orderOf.mpr
      (orderOf_eq_prime_pow
        (x := (0x7e010002 : KoalaBearResidue)) (p := 2) (n := 1) (by decide) (by decide))
  · change IsPrimitiveRoot (0x6832fe4a : KoalaBearResidue) (2 ^ 3)
    exact IsPrimitiveRoot.iff_orderOf.mpr
      (orderOf_eq_prime_pow
        (x := (0x6832fe4a : KoalaBearResidue)) (p := 2) (n := 2) (by decide) (by decide))
  · change IsPrimitiveRoot (0x8dbd69c : KoalaBearResidue) (2 ^ 4)
    exact IsPrimitiveRoot.iff_orderOf.mpr
      (orderOf_eq_prime_pow
        (x := (0x8dbd69c : KoalaBearResidue)) (p := 2) (n := 3) (by decide) (by decide))
  · change IsPrimitiveRoot (0xa28f031 : KoalaBearResidue) (2 ^ 5)
    exact IsPrimitiveRoot.iff_orderOf.mpr
      (orderOf_eq_prime_pow
        (x := (0xa28f031 : KoalaBearResidue)) (p := 2) (n := 4) (by decide) (by decide))
  · change IsPrimitiveRoot (0x5c4a5b99 : KoalaBearResidue) (2 ^ 6)
    exact IsPrimitiveRoot.iff_orderOf.mpr
      (orderOf_eq_prime_pow
        (x := (0x5c4a5b99 : KoalaBearResidue)) (p := 2) (n := 5) (by decide) (by decide))
  · change IsPrimitiveRoot (0x29b75a80 : KoalaBearResidue) (2 ^ 7)
    exact IsPrimitiveRoot.iff_orderOf.mpr
      (orderOf_eq_prime_pow
        (x := (0x29b75a80 : KoalaBearResidue)) (p := 2) (n := 6) (by decide) (by decide))
  · change IsPrimitiveRoot (0x17668b8a : KoalaBearResidue) (2 ^ 8)
    exact IsPrimitiveRoot.iff_orderOf.mpr
      (orderOf_eq_prime_pow
        (x := (0x17668b8a : KoalaBearResidue)) (p := 2) (n := 7) (by decide) (by decide))
  · change IsPrimitiveRoot (0x27ad539b : KoalaBearResidue) (2 ^ 9)
    exact IsPrimitiveRoot.iff_orderOf.mpr
      (orderOf_eq_prime_pow
        (x := (0x27ad539b : KoalaBearResidue)) (p := 2) (n := 8) (by decide) (by decide))
  · change IsPrimitiveRoot (0x334d48c7 : KoalaBearResidue) (2 ^ 10)
    exact IsPrimitiveRoot.iff_orderOf.mpr
      (orderOf_eq_prime_pow
        (x := (0x334d48c7 : KoalaBearResidue)) (p := 2) (n := 9) (by decide) (by decide))
  · change IsPrimitiveRoot (0x7744959c : KoalaBearResidue) (2 ^ 11)
    exact IsPrimitiveRoot.iff_orderOf.mpr
      (orderOf_eq_prime_pow
        (x := (0x7744959c : KoalaBearResidue)) (p := 2) (n := 10) (by decide) (by decide))
  · change IsPrimitiveRoot (0x768fc6fa : KoalaBearResidue) (2 ^ 12)
    exact IsPrimitiveRoot.iff_orderOf.mpr
      (orderOf_eq_prime_pow
        (x := (0x768fc6fa : KoalaBearResidue)) (p := 2) (n := 11) (by decide) (by decide))
  · change IsPrimitiveRoot (0x303964b2 : KoalaBearResidue) (2 ^ 13)
    exact IsPrimitiveRoot.iff_orderOf.mpr
      (orderOf_eq_prime_pow
        (x := (0x303964b2 : KoalaBearResidue)) (p := 2) (n := 12) (by decide) (by decide))
  · change IsPrimitiveRoot (0x3e687d4d : KoalaBearResidue) (2 ^ 14)
    exact IsPrimitiveRoot.iff_orderOf.mpr
      (orderOf_eq_prime_pow
        (x := (0x3e687d4d : KoalaBearResidue)) (p := 2) (n := 13) (by decide) (by decide))
  · change IsPrimitiveRoot (0x45a60e61 : KoalaBearResidue) (2 ^ 15)
    exact IsPrimitiveRoot.iff_orderOf.mpr
      (orderOf_eq_prime_pow
        (x := (0x45a60e61 : KoalaBearResidue)) (p := 2) (n := 14) (by decide) (by decide))
  · change IsPrimitiveRoot (0x6e2f4d7a : KoalaBearResidue) (2 ^ 16)
    exact IsPrimitiveRoot.iff_orderOf.mpr
      (orderOf_eq_prime_pow
        (x := (0x6e2f4d7a : KoalaBearResidue)) (p := 2) (n := 15) (by decide) (by decide))
  · change IsPrimitiveRoot (0x163bd499 : KoalaBearResidue) (2 ^ 17)
    exact IsPrimitiveRoot.iff_orderOf.mpr
      (orderOf_eq_prime_pow
        (x := (0x163bd499 : KoalaBearResidue)) (p := 2) (n := 16) (by decide) (by decide))
  · change IsPrimitiveRoot (0x6c4a8a45 : KoalaBearResidue) (2 ^ 18)
    exact IsPrimitiveRoot.iff_orderOf.mpr
      (orderOf_eq_prime_pow
        (x := (0x6c4a8a45 : KoalaBearResidue)) (p := 2) (n := 17) (by decide) (by decide))
  · change IsPrimitiveRoot (0x143ef899 : KoalaBearResidue) (2 ^ 19)
    exact IsPrimitiveRoot.iff_orderOf.mpr
      (orderOf_eq_prime_pow
        (x := (0x143ef899 : KoalaBearResidue)) (p := 2) (n := 18) (by decide) (by decide))
  · change IsPrimitiveRoot (0x514ddcad : KoalaBearResidue) (2 ^ 20)
    exact IsPrimitiveRoot.iff_orderOf.mpr
      (orderOf_eq_prime_pow
        (x := (0x514ddcad : KoalaBearResidue)) (p := 2) (n := 19) (by decide) (by decide))
  · change IsPrimitiveRoot (0x484ef19b : KoalaBearResidue) (2 ^ 21)
    exact IsPrimitiveRoot.iff_orderOf.mpr
      (orderOf_eq_prime_pow
        (x := (0x484ef19b : KoalaBearResidue)) (p := 2) (n := 20) (by decide) (by decide))
  · change IsPrimitiveRoot (0x205d63c3 : KoalaBearResidue) (2 ^ 22)
    exact IsPrimitiveRoot.iff_orderOf.mpr
      (orderOf_eq_prime_pow
        (x := (0x205d63c3 : KoalaBearResidue)) (p := 2) (n := 21) (by decide) (by decide))
  · change IsPrimitiveRoot (0x68e7dd49 : KoalaBearResidue) (2 ^ 23)
    exact IsPrimitiveRoot.iff_orderOf.mpr
      (orderOf_eq_prime_pow
        (x := (0x68e7dd49 : KoalaBearResidue)) (p := 2) (n := 22) (by decide) (by decide))
  · change IsPrimitiveRoot (0x6ac49f88 : KoalaBearResidue) (2 ^ 24)
    exact IsPrimitiveRoot.iff_orderOf.mpr
      (orderOf_eq_prime_pow
        (x := (0x6ac49f88 : KoalaBearResidue)) (p := 2) (n := 23) (by decide) (by decide))

end Zkc.Source.Structured
