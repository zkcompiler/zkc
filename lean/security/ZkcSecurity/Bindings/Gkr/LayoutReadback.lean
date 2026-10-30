module

public import ZkcSecurity.Bindings.Gkr.RoundsLayout
public import Zkc.Polynomial.Multilinear.ListRestriction

@[expose] public section

namespace ZkcSecurity.Realizations.Gkr.HonestHelpers
open Zkc.Polynomial.Multilinear
open ZkcSecurity.Examples.Components
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The flat encoding is determined by the decoded mathematical table. -/
theorem encode_of_decodes {n : Nat} (xs : List F) (table : Table F n)
    (decoded : ofList? n xs = some table) : GkrRoundsLayout.encode table = xs := by
  apply List.ext_getElem
  · simp only [GkrRoundsLayout.encode, List.length_ofFn, ofList?_length xs table decoded]
  · intro i hi hj
    have bound : i < 2 ^ n := by simpa [GkrRoundsLayout.encode] using hi
    have entry := ofList?_entry xs table decoded ⟨i, bound⟩
    simp only [List.getElem?_eq_getElem hj] at entry
    simpa only [GkrRoundsLayout.encode, List.getElem_ofFn] using (Option.some.inj entry).symm

end ZkcSecurity.Realizations.Gkr.HonestHelpers
