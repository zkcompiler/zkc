module

public import Zkc.Source.Structured.CollectLaws

@[expose] public section

/-! Indexed reference equations for ordered finite collections. The reference
enumeration preserves the complete typed tuple and strict zip admission. -/

set_option autoImplicit false
namespace Zkc.Source.Structured

theorem list_map_range {A B : Type} (xs : List A) (fallback : A) (f : A → B) :
    xs.map f = (List.range xs.length).map (fun i => f (xs[i]?.getD fallback)) := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range]
  · intro i left right
    have bound : i < xs.length := by simpa only [List.length_map] using left
    simp only [List.getElem_map, List.getElem_range, List.getElem?_eq_getElem bound,
      Option.getD_some]

theorem zipDomainRows_ranges {carriers : Carriers} {left right : List Ty}
    (n m : Nat) (lhs : Nat → Values carriers.Value left)
    (rhs : Nat → Values carriers.Value right) :
    zipDomainRows (.cons ((List.range n).map lhs) (.cons ((List.range m).map rhs) .nil)) =
      if n = m then
        .returned ((List.range n).map fun i => (lhs i).append ((rhs i).append .nil))
      else .stopped .refused := by
  simp only [zipDomainRows, Finite.continueWith, List.length_map, List.length_range]
  split
  · next same =>
      subst m
      simp only [List.map_map, List.zip_map, Function.comp_def,
        List.map_zip_eq_zipWith, List.zipWith_self]
      rfl
  · rfl

end Zkc.Source.Structured
