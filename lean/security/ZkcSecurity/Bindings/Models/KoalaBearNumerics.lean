module

public import ZkcSecurity.Bindings.Models.KoalaBearModel
public import Zkc.Source.Structured.KoalaBearRoots

@[expose] public section

/-! Ordered numerical roots for the octic verifier. The stored generators
are in the prime subfield and are embedded by the installed ring homomorphism. -/
set_option autoImplicit false
namespace ZkcSecurity.Domains.KoalaBearModel
open Zkc.Source.Structured
open ZkcSecurity.Domains.KoalaBear (Base)

def octicRoots : TwoAdicData model.Field :=
  ⟨baseIdentity, koalaBearRootLiterals.map (fun (n : Nat) ↦ (n : Base))⟩

theorem octicRoots_installed : model.twoAdic octicIdentity = some octicRoots := by rfl

theorem root_at (k : Nat) (h : k < octicRoots.roots.length) :
    octicRoots.roots[k] = (koalaBearRootLiterals[k]'h : Base) :=
  List.getElem_map (fun (n : Nat) ↦ (n : Base)) (l := koalaBearRootLiterals) (i := k) (h := h)

theorem octicRoots_ordered : OrderedRootLaw catalogue model.toFieldModel octicIdentity octicRoots where
  capability := by decide
  installed := ⟨koalaBearRootLiterals, rfl, rfl⟩
  embedding := embedding_law
  order k root atIndex := by
    obtain ⟨bound, rfl⟩ := List.getElem?_eq_some_iff.mp atIndex
    have limit : k < koalaBearRootLiterals.length := bound
    have order := koalaBearRootLiterals_order ⟨k, limit⟩
    change IsPrimitiveRoot (koalaBearRootLiterals[k]! : KoalaBearResidue) (2 ^ k) at order
    rw [getElem!_pos koalaBearRootLiterals k limit] at order
    rw [root_at]
    exact order
  square k a b left right := by
    obtain ⟨bound, rfl⟩ := List.getElem?_eq_some_iff.mp left
    obtain ⟨next, rfl⟩ := List.getElem?_eq_some_iff.mp right
    have limit : k + 1 < 25 := next
    let pairs := (koalaBearRootLiterals.drop 1).zip koalaBearRootLiterals
    have pairBound : k < pairs.length := (show k < 24 by omega)
    have pair := of_decide_eq_true (List.all_eq_true.mp koalaBearRootLiterals_square
      pairs[k] (List.getElem_mem pairBound))
    rw [root_at, root_at]
    change (koalaBearRootLiterals[k + 1]'next : KoalaBearResidue) ^ 2 =
      (koalaBearRootLiterals[k]'bound : KoalaBearResidue)
    simp only [pairs, List.getElem_zip, List.getElem_drop, Nat.add_comm 1 k] at pair
    exact pair

/-- Root data is available only for the selected octic operations. Inverses
exist at both installed field rows. -/
theorem numericalLaws : NumericalDomainLaws catalogue model
    {inverse := [baseIdentity, octicIdentity], roots := [octicIdentity]} where
  algebra := laws
  characteristic := characteristic_laws
  inverse_complete d member := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨by decide, _, inverse_base⟩
    · exact ⟨by decide, _, inverse_octic⟩
  roots_complete d member := by
    obtain rfl := List.mem_singleton.mp member
    exact ⟨_, octicRoots_installed⟩
  binary_complete _ member := False.elim (List.not_mem_nil member)
  roots d data installed := by
    by_cases selected : d = octicIdentity
    · subst d
      rw [octicRoots_installed] at installed
      cases installed
      exact octicRoots_ordered
    · simp [model, selected] at installed
  binary _ _ installed := by cases installed

end ZkcSecurity.Domains.KoalaBearModel
