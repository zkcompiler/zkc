module

public import ZkcArkLibExamples.Fri.HolderFold
public import ZkcArkLibExamples.Fri.HolderPadding

@[expose] public section

/-! The holder's linked numerical helpers produce one chronological sequence
of words and the exact terminal vector for every admissible codeword and
challenge schedule. The scalar checker uses these same words at every index. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.HonestMessages
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured FriSourceBodies
open ZkcSecurity.Domains.KoalaBearModel (model)
open ZkcSecurity.Domains.KoalaBear (Octic)
open Domain (SmoothCosetFftDomain)
open _root_.ProximityGap (foldWord)

abbrev Words (n : Nat) := Fin (2 ^ n) → Octic

/-- Every fold and the final vector come from the checked helper table.
The list on the left is the supplied draw schedule, in source order. -/
def Computes (I : PIR.Signature) : {n R : Nat} → Octic → Words n → List Octic → Layers Octic n R → Prop
  | _, _, shift, word, draws, .final coefficients =>
    draws = [] ∧ (do
      let polynomial ← invoke (RetainedFold.helpers (I := I)).closed helper17Helper
        (.cons (List.ofFn word) (.cons shift .nil))
      let cs ← invoke (RetainedFold.helpers (I := I)).closed helper18Helper polynomial
      invoke (RetainedFold.helpers (I := I)).closed helper21Helper (.cons (cs.get .here) (.cons 1 .nil))) =
        .done (.cons coefficients .nil)
  | _, _, shift, word, draws, .fold sent beta rest =>
    sent = word ∧ ∃ next tail, draws = beta :: tail ∧
      invoke (RetainedFold.helpers (I := I)).closed helper16Helper
        (.cons (List.ofFn word) (.cons shift (.cons beta .nil))) =
        .done (.cons (List.ofFn next) (.cons (shift * shift) .nil)) ∧
      Computes I (shift * shift) next tail rest

private theorem messages (I : PIR.Signature) : ∀ (draws : List Octic) (_small : draws.length ≤ 3)
    (shift : Octic) (_nonzero : shift ≠ 0) (D : SmoothCosetFftDomain (2 + draws.length) Octic)
    (_geometry : ∀ j, D j = point RetainedDomain.root shift (2 + draws.length) j)
    (word : Words (2 + draws.length)),
    word ∈ ReedSolomon.code (D : Fin (2 ^ (2 + draws.length)) ↪ Octic) (degreeBound draws.length 1) →
    ∃ layers : Layers Octic (2 + draws.length) draws.length,
      Computes I shift word draws layers ∧ (toTrace 0 D layers).initial = word ∧
      Honest 0 D layers ∧ layers.coefficients.length = 1
  | [], _, shift, nz, D, geometry, word, code => by
    obtain ⟨c, constant, runs⟩ := HolderPadding.terminal_message (I := I) (by decide : 2 ≤ 5)
      shift nz D geometry word code
    refine ⟨.final [c], ⟨rfl, runs⟩, ?_, trivial, rfl⟩
    funext j
    change evaluate [c] (D j) = word j
    simp [evaluate, constant j]
  | beta :: tail, small, shift, nz, D, geometry, word, code => by
    have size : (2 + tail.length) + 1 ≤ 5 := by simp only [List.length_cons] at small; omega
    let next := foldWord D word 1 beta
    have step := HolderFold.installed (I := I) size D shift beta nz geometry word
    have codeNext := fold_mem_code 0 (m := 2 + tail.length) (R := tail.length) (by omega) D word code beta
    have geometryNext := subdomain_point RetainedDomain.root D shift geometry
      (RetainedDomain.square (2 + tail.length) (lt_of_le_of_lt size (by decide : 5 < 25)))
    obtain ⟨rest, produces, initial, correct, width⟩ := messages I tail (by simp only [List.length_cons] at small; omega)
      (shift * shift) (mul_ne_zero nz nz) (D.subdomain 1) geometryNext next codeNext
    exact ⟨.fold word beta rest, ⟨rfl, next, tail, rfl, step, produces⟩, rfl, ⟨initial, correct⟩, width⟩

/-- On the retained coset all eight scalar positions work for the same
three messages, including schedules with repeated positions or challenges. -/
theorem retained (I : PIR.Signature) (shift : Octic) (nonzero : shift ≠ 0)
    (word : Words 5) (code : word ∈ ReedSolomon.code (RetainedDomain.domain shift nonzero : Fin 32 ↪ Octic) 8)
    (first second third : Octic) :
    ∃ layers : Layers Octic 5 3, Computes I shift word [first, second, third] layers ∧
      (toTrace 0 (RetainedDomain.domain shift nonzero) layers).initial = word ∧
      ∀ positions : Fin 8 → Fin 32, Phases.accepts RetainedDomain.root 0 layers shift positions = true := by
  obtain ⟨layers, runs, original, honest, width⟩ := messages I [first, second, third] (by simp)
    shift nonzero _ (RetainedDomain.geometry shift nonzero) word code
  refine ⟨layers, runs, original, fun positions ↦ ?_⟩
  have result := verify_of_honest RetainedDomain.root 0 (RetainedDomain.domain shift nonzero) shift
    (RetainedDomain.geometry shift nonzero) RetainedDomain.compatible layers honest
    (by simp [bounded, width]) positions
  simp only [verify, Bool.and_eq_true] at result
  have walks := result.2
  simp only [Phases.accepts, Phases.firstPath_eq_walk, Phases.exactCoefficients, width, pow_zero,
    decide_true, Bool.true_and]
  exact walks

end ZkcSecurity.ArkLib.Fri.HonestMessages
