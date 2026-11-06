module

public import ZkcArkLibExamples.Fri.VirtualReads
public import ZkcArkLib.Fri.SourcePublication

@[expose] public section

/-! Read the installed virtual Fold against one immutable published word.
The actual two child addresses select the ArkLib low and high cells. -/
set_option autoImplicit false
set_option maxRecDepth 6000
namespace ZkcSecurity.ArkLib.Fri.VirtualWord
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open ZkcSecurity.Domains.KoalaBearModel (model)
open ZkcSecurity.Domains.KoalaBear (Octic)
open VirtualReads (kind low)

theorem addresses {m : Nat} (size : m + 1 ≤ 63) (index : Fin (2 ^ m)) :
    low index.val (2 ^ (m + 1)) = (lowIndex index).val ∧
    wrappingAdd (low index.val (2 ^ (m + 1))) (logicalShiftRight (2 ^ (m + 1)) 1) =
      (highIndex index).val := by
  have rows : 2 ^ (m + 1) < wordModulus :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  have bounded := (lowIndex index).isLt.trans rows
  have first := machine_pair_low index.val m size bounded
  have half : logicalShiftRight (2 ^ (m + 1)) 1 = 2 ^ m := by
    rw [logicalShiftRight_of_lt _ (by decide), Nat.mod_eq_of_lt rows]
    simp [Nat.pow_succ]
  have high := machine_high_index index.val m size
  simp only [Nat.mod_eq_of_lt index.isLt] at first high
  change low index.val (2 ^ (m + 1)) = index.val at first
  exact ⟨first, by rw [first, half]; exact high⟩

variable {Aux E : Type}

theorem runFold {S E : Type} {m : Nat} (size : m + 1 ≤ 63)
    (domain : Domain.SmoothCosetFftDomain (m + 1) Octic) (shift : Octic)
    (geometry : ∀ i : Fin (2 ^ (m + 1)), domain i = point RetainedDomain.root shift (m + 1) i)
    (word : Fin (2 ^ (m + 1)) → Octic) (beta : Octic) (index : Fin (2 ^ m))
    (source : OracleAnchor) (handler : PIR.Handler (VirtualReads.readInterface model) S E)
    {initial middle final : S} {leftTrace rightTrace : List E}
    (leftRead : handler (VirtualReads.leftRequest source (lowIndex index).val) initial =
      ⟨.returned (word (lowIndex index)), middle, leftTrace⟩)
    (rightRead : handler (VirtualReads.rightRequest source (highIndex index).val) middle =
      ⟨.returned (word (highIndex index)), final, rightTrace⟩) :
    (FriVirtualBody.installed.denote model (VirtualReads.arguments model source beta (2 ^ (m + 1)) (2 ^ m)
        shift (RetainedDomain.root (m + 1)) (shift⁻¹ : Octic) ((RetainedDomain.root (m + 1))⁻¹ : Octic)
        ((2 : Octic)⁻¹ : Octic) index.val).present).run handler initial =
      ⟨.returned (.cons (some (ProximityGap.foldWord domain word 1 beta index)) .nil),
        final, leftTrace ++ rightTrace⟩ := by
  obtain ⟨first, second⟩ := addresses size index
  have run := congrArg (fun p ↦ p.run handler initial) (VirtualReads.twoReads model
    source beta (2 ^ (m + 1)) (2 ^ m) shift (RetainedDomain.root (m + 1)) (shift⁻¹ : Octic)
    ((RetainedDomain.root (m + 1))⁻¹ : Octic) ((2 : Octic)⁻¹ : Octic) index.val)
  refine run.trans ((VirtualReads.runChildren model handler source beta _ _ _ _ index.val
    first second leftRead rightRead).trans ?_)
  exact congrArg (fun x : Octic ↦ PIR.Execution.mk (.returned (Values.cons (Value := Component model.Value)
    (ty := .field FriSource.extension) (some x) .nil)) final (leftTrace ++ rightTrace))
    (prepared_inverse_fold RetainedDomain.root domain shift geometry word beta index)

theorem foldWord {m : Nat} (size : m + 1 ≤ 63)
    (domain : Domain.SmoothCosetFftDomain (m + 1) Octic) (shift : Octic)
    (geometry : ∀ i : Fin (2 ^ (m + 1)), domain i = point RetainedDomain.root shift (m + 1) i)
    (word : Fin (2 ^ (m + 1)) → Octic) (beta : Octic) (index : Fin (2 ^ m))
    (source : OracleAnchor) (state : PublishedWords.State model Aux)
    (stored : PublishedWords.Word model kind.answer)
    (found : PublishedWords.find state.words kind.answer source = some stored)
    (answer : stored.kind.answer = kind.answer) (shape : OracleStore.validRows stored.kind stored.rows = true)
    (rows : stored.rows = 2 ^ (m + 1)) (cells : stored.cells = List.ofFn word) :
    (FriVirtualBody.installed.denote model (VirtualReads.arguments model source beta (2 ^ (m + 1)) (2 ^ m)
        shift (RetainedDomain.root (m + 1)) (shift⁻¹ : Octic) ((RetainedDomain.root (m + 1))⁻¹ : Octic) ((2 : Octic)⁻¹ : Octic) index.val).present).run
      (PublishedWords.read (E := E)) state =
      ⟨.returned (.cons (some (ProximityGap.foldWord domain word 1 beta index)) .nil), state, []⟩ := by
  have child (position : Fin (2 ^ (m + 1))) (location : OracleLocation) :=
    SourcePublication.read_fixed_word (model := model) (E := E) source word stored answer shape rows cells
      position location [] state found
  exact runFold size domain shift geometry word beta index source _ (child (lowIndex index) _)
    (child (highIndex index) _)

end ZkcSecurity.ArkLib.Fri.VirtualWord
