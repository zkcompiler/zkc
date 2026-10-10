import ZkcClean.Native
import TestsClean.KoalaBear

/-! A prime field size does not determine the native presentation.

`Twisted` is `F 5` with Clean's canonical naturals of 2 and 3 exchanged. It is a
lawful Clean `FiniteField` of prime size and its artifacts pass import
admission, but its naturals are not residues: `fromNat 2` is the residue 3. A
native reader of residues would silently change its constants, so no
`PrimePresentation` exists and nothing can be emitted for it.
-/

set_option autoImplicit false

namespace TestsClean.Presentation

open ZkcClean

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

def Twisted : Type := F 5

instance : DecidableEq Twisted := inferInstanceAs (DecidableEq (F 5))

def swap (x : F 5) : F 5 := if x = 2 then 3 else if x = 3 then 2 else x

theorem swap_injective : ∀ x y : F 5, swap x = swap y → x = y := by decide +kernel

instance field : Field Twisted := inferInstanceAs (Field (F 5))

instance : FiniteField Twisted where
  toField := field
  val x := ZMod.val (swap x)
  fromNat n := swap (n : F 5)
  size := 5
  val_lt x := ZMod.val_lt (swap x)
  val_injective x y h := swap_injective x y (ZMod.val_injective 5 h)
  val_fromNat := by decide +kernel
  val_zero := by decide +kernel
  val_one := by decide +kernel

theorem twisted_size_prime : (FiniteField.size Twisted).Prime := by
  change Nat.Prime 5
  exact Fact.out

theorem twisted_not_residue : (FiniteField.fromNat 2 : Twisted) ≠ (2 : Twisted) := by
  decide +kernel

theorem twisted_no_presentation : PrimePresentation Twisted → False :=
  fun presentation => twisted_not_residue (presentation.residue 2)

/-- Import admission accepts the artifact: the field size matches and every
constant is canonical. Admission is not the presentation contract. -/
theorem twisted_decodes :
    (({ fieldSize := 5, width := 1, assertions := [.add (.column 0) (.constant 2)] } : Artifact).decode
      Twisted).isSome := by
  decide +kernel

end TestsClean.Presentation
