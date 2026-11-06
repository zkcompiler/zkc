module

public import ZkcArkLib.Fri.RetainedFold
public import ZkcArkLib.Fri.Completeness
public import Zkc.Source.Structured.NumericalFold

@[expose] public section

/-! The holder evaluates an entire folded word. The virtual oracle evaluates
one cell when the verifier requests it. Both are tied to the same ArkLib fold. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.HolderFold
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open ZkcSecurity.Domains.KoalaBearModel (model inverse_octic octicIdentity)
open ZkcSecurity.Domains.KoalaBear (Octic Base embed embed_injective)
open FriSourceViews FriSourceBodies

theorem two_nonzero : (2 : Octic) ≠ 0 := by
  intro zero
  have base : (2 : Base) ≠ 0 := by decide
  apply base
  apply embed_injective
  simpa only [map_ofNat, map_zero] using zero

theorem orderedCells {F : Type} [Field F] [DecidableEq F] [Inhabited F] {m : Nat}
    (roots : Nat → F) (domain : Domain.SmoothCosetFftDomain (m + 1) F) (shift beta : F)
    (geometry : ∀ i : Fin (2 ^ (m + 1)), domain i = point roots shift (m + 1) i)
    (word : Fin (2 ^ (m + 1)) → F) :
    let xs := List.ofFn word
    (List.range (xs.length / 2)).map (fun i ↦
      (xs[i]! + xs[i + xs.length / 2]!) * (2 : F)⁻¹ +
        beta * (xs[i]! - xs[i + xs.length / 2]!) * (2 : F)⁻¹ * (shift * roots (m + 1) ^ i)⁻¹) =
      List.ofFn (ProximityGap.foldWord domain word 1 beta) := by
  dsimp only
  have half : (List.ofFn word).length / 2 = 2 ^ m := by
    rw [List.length_ofFn, pow_succ, Nat.mul_div_cancel]; decide
  rw [half]
  apply List.ext_getElem (by simp)
  intro i _ right
  let pos : Fin (2 ^ m) := ⟨i, by simpa using right⟩
  have atCell (j : Fin (2 ^ (m + 1))) : (List.ofFn word)[j.val]! = word j := by
    rw [getElem!_pos _ _ (List.length_ofFn.symm ▸ j.isLt), List.getElem_ofFn]
  have low : (List.ofFn word)[i]! = word (lowIndex pos) := atCell (lowIndex pos)
  have high : (List.ofFn word)[i + 2 ^ m]! = word (highIndex pos) := atCell (highIndex pos)
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, low, high]
  simpa only [foldedValue, foldValue, point, one_add_one_eq_two] using
    foldedValue_eq roots domain shift geometry word beta pos

theorem word_fold {m : Nat} (size : m + 1 ≤ 5)
    (domain : Domain.SmoothCosetFftDomain (m + 1) Octic) (shift beta : Octic)
    (nonzero : shift ≠ 0)
    (geometry : ∀ i : Fin (2 ^ (m + 1)), domain i = point RetainedDomain.root shift (m + 1) i)
    (word : Fin (2 ^ (m + 1)) → Octic) :
    Numerical.checkedEvaluateOn model.toFieldModel octicIdentity "" .polyFold
      (.cons (List.ofFn word) (.cons shift (.cons beta .nil))) =
      .returned (.cons (List.ofFn (ProximityGap.foldWord domain word 1 beta)) .nil) := by
  have length : (List.ofFn word).length = 2 ^ (m + 1) := List.length_ofFn
  have bound : (List.ofFn word).length < indexLimit := by
    rw [length]; exact Nat.pow_lt_pow_right (by decide) (show m + 1 < 64 by omega)
  refine (Numerical.checked_fold model.toFieldModel octicIdentity "" (List.ofFn word) shift beta bound).trans ?_
  have enough : 2 ≤ (List.ofFn word).length := by
    rw [length]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ m + 1 by omega)
  have generators (i : Nat) : shift * RetainedDomain.root (m + 1) ^ i ≠ 0 :=
    mul_ne_zero nonzero (pow_ne_zero _ ((RetainedDomain.order (m + 1) (by omega)).ne_zero (by positivity)))
  refine (Numerical.fold_cells model.toFieldModel octicIdentity "" (List.ofFn word)
    shift beta (RetainedDomain.root (m + 1)) (fun x : Octic ↦ (x⁻¹ : Octic))
    ((congrArg (Numerical.domainRoot model.toFieldModel octicIdentity) length).trans
      (RetainedDomain.domainRoot (m + 1) size)) nonzero
    enough inverse_octic two_nonzero (fun i _ ↦ generators i)).trans ?_
  apply congrArg (fun ys ↦ PIR.Outcome.returned
    (Values.cons (Value := model.Value) (ty := .vector octicIdentity) ys .nil))
  exact orderedCells RetainedDomain.root domain shift beta geometry word

abbrev foldPrimitive : Primitive := .numerical .polyFold octicIdentity ""

def advance (model : DomainModel) (shift : model.Field octicIdentity) :
    PIR.Outcome (Values model.Value foldPrimitive.results) →
    PIR.Outcome (Values model.Value helper16Helper.outputs)
  | .stopped reason => .stopped reason
  | .returned (.cons folded .nil) => .returned (.cons folded (.cons (shift * shift) .nil))

theorem primitiveStep (model : DomainModel) (table : Evaluation.MeaningsOn model.toCarriers closedInterface)
    (args : Values model.Value foldPrimitive.arguments)
    {result : PIR.Outcome (Values model.Value foldPrimitive.results)}
    (equation : foldPrimitive.evaluateOn model.toFieldModel args = result) :
    (Evaluation.meaningOn model SiteObservations.closed table).OperationLaw
      (fun op ↦ .call op .done) (.exec foldPrimitive) args .nil (primitiveOutcome result) := by
  apply RegionMeaning.OperationLaw.identity
  exact congrArg primitiveOutcome equation

theorem helper_body (model : DomainModel) (table : Evaluation.MeaningsOn model.toCarriers closedInterface)
    (xs : List (model.Field octicIdentity)) (shift beta : model.Field octicIdentity) :
    let args : Values model.Value foldPrimitive.arguments := .cons xs (.cons shift (.cons beta .nil))
    helper16Body.denote (Evaluation.meaningOn model SiteObservations.closed table) args.get =
      primitiveOutcome (advance model shift (foldPrimitive.evaluateOn model.toFieldModel args)) := by
  intro args
  cases outcome : foldPrimitive.evaluateOn model.toFieldModel args with
  | stopped reason =>
    derive_process using (exact primitiveStep model table args outcome)
  | returned values =>
    cases values with | cons folded rest =>
    cases rest
    derive_process using (exact primitiveStep model table args outcome)

def law (model : DomainModel) : ReferenceLaw model helper16Helper.inputs helper16Helper.outputs where
  body := helper16Body
  Requires _ _ := True
  reference
    | .cons xs (.cons shift (.cons beta .nil)) => advance model shift
        (foldPrimitive.evaluateOn model.toFieldModel (.cons xs (.cons shift (.cons beta .nil))))
  valid table
    | .cons xs (.cons shift (.cons beta .nil)), _ => helper_body model table xs shift beta

/-- The admitted holder helper returns every honest folded cell, in order,
and the squared shift supplied to the next round. -/
theorem installed {I : PIR.Signature} {m : Nat} (size : m + 1 ≤ 5)
    (domain : Domain.SmoothCosetFftDomain (m + 1) Octic) (shift beta : Octic)
    (nonzero : shift ≠ 0)
    (geometry : ∀ i : Fin (2 ^ (m + 1)), domain i = point RetainedDomain.root shift (m + 1) i)
    (word : Fin (2 ^ (m + 1)) → Octic) :
    invoke (RetainedFold.helpers (I := I)).closed helper16Helper
      (.cons (List.ofFn word) (.cons shift (.cons beta .nil))) =
      .done (.cons (List.ofFn (ProximityGap.foldWord domain word 1 beta)) (.cons (shift * shift) .nil)) := by
  refine ((law model).invokeOn (I := I) unit.definitions unit.linked
    (helper := helper16Helper) (by exact_body helper16Definition)
    (.cons (List.ofFn word) (.cons shift (.cons beta .nil))) trivial).trans ?_
  change primitiveOutcome (advance model shift (Numerical.checkedEvaluateOn model.toFieldModel octicIdentity ""
    .polyFold (.cons (List.ofFn word) (.cons shift (.cons beta .nil))))) = _
  rw [word_fold size domain shift beta nonzero geometry word]
  rfl

/-- The installed holder step preserves the degree invariant for every
admissible polynomial and every challenge, including zero. -/
theorem installed_codeword {I : PIR.Signature} {m t R : Nat} (size : m + 1 ≤ 5)
    (rate : t + R ≤ m) (domain : Domain.SmoothCosetFftDomain (m + 1) Octic)
    (shift beta : Octic) (nonzero : shift ≠ 0)
    (geometry : ∀ i : Fin (2 ^ (m + 1)), domain i = point RetainedDomain.root shift (m + 1) i)
    (word : Fin (2 ^ (m + 1)) → Octic)
    (codeword : word ∈ ReedSolomon.code (domain : Fin (2 ^ (m + 1)) ↪ Octic) (degreeBound (R + 1) (2 ^ t))) :
    ∃ next : Fin (2 ^ (m + 1 - 1)) → Octic,
      invoke (RetainedFold.helpers (I := I)).closed helper16Helper
          (.cons (List.ofFn word) (.cons shift (.cons beta .nil))) =
        .done (.cons (List.ofFn next) (.cons (shift * shift) .nil)) ∧
      next ∈ ReedSolomon.code (domain.subdomain 1 : Fin (2 ^ (m + 1 - 1)) ↪ Octic) (degreeBound R (2 ^ t)) :=
  ⟨_, installed size domain shift beta nonzero geometry word, fold_mem_code t rate domain word codeword beta⟩

end ZkcSecurity.ArkLib.Fri.HolderFold
