module

public import ZkcArkLibExamples.Fri.HolderFold
public import ZkcExamples.Structured.FriPower
public import Zkc.Source.Structured.OracleQueryDerivation

@[expose] public section

/-! The checked binary-domain predicate on the retained folding cosets. Its
two power calls are discharged in the protocol's actual declaration table. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.BinaryDomain
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open FriSourceBodies FriSourceViews
open ZkcSecurity.Domains.KoalaBear (Octic)
open ZkcSecurity.Domains.KoalaBearModel (model)

def arguments (n : Nat) (shift : Octic) : Values model.Value helper12Helper.inputs :=
  let root := RetainedDomain.root (n + 1)
  .cons (2 ^ (n + 1)) (.cons shift (.cons root (.cons (shift⁻¹ : Octic)
    (.cons (root⁻¹ : Octic) (.cons ((2 : Octic)⁻¹ : Octic) .nil)))))

private def power (table : Evaluation.MeaningsOn model.toCarriers closedInterface) (g : Octic)
    (e : Nat) (x : Octic) : Prop :=
  invoke table helper11Helper (.cons g (.cons e .nil)) = .done (.cons x .nil)

theorem halfSize (n : Nat) (bound : n + 1 ≤ 5) :
    logicalShiftRight (2 ^ (n + 1)) 1 = 2 ^ n := by
  have fits : 2 ^ (n + 1) < wordModulus := Nat.pow_lt_pow_right (by decide) (by omega)
  rw [logicalShiftRight_of_lt _ (by decide), Nat.mod_eq_of_lt fits]
  simp [pow_succ]

private def inputs (m : DomainModel) (rows : Nat) (shift root si gi ti : m.Field FriSource.extension) :
    Values m.Value helper12Helper.inputs := .cons rows (.cons shift (.cons root (.cons si (.cons gi (.cons ti .nil)))))

private theorem equalTrue (m : DomainModel) {p : Prop} [Decidable p] (holds : p) :
    PIR.Process.done (I := closedInterface) (Values.cons (Value := m.Value) (ty := .boolean) (decide p) .nil) =
      .done (.cons true .nil) := by rw [decide_eq_true holds]

private theorem equalFalse (m : DomainModel) {p : Prop} [Decidable p] (fails : ¬p) :
    PIR.Process.done (I := closedInterface) (Values.cons (Value := m.Value) (ty := .boolean) (decide p) .nil) =
      .done (.cons false .nil) := by rw [decide_eq_false fails]

local macro "guard_step " value:term : tactic =>
  `(tactic|
    refine Region.ReturnsValues.letOp $value ?_ ?_)

private theorem branchTaken (m : DomainModel) (table : Evaluation.MeaningsOn m.toCarriers closedInterface)
    {ins out : List Ty} (yes no : Region dialect ins out) (captured : Values m.Value ins) (result : Values m.Value out)
    (checked : yes.ReturnsValues (Evaluation.meaningOn m SiteObservations.closed table) captured result) :
    (Evaluation.meaningOn m SiteObservations.closed table).operation (.branch ins out)
      (.cons true captured) ((Regions.cons yes (.cons no .nil)).denote (Evaluation.meaningOn m SiteObservations.closed table)) =
        .done result := checked

/-- The short-circuit branch checking the 64-bit power-of-two mask. Its
tree is matched against the actual callback by the enclosing source law. -/
private def maskCheck : Region dialect [.index] [.boolean] :=
  .letOp (.indexConstant 1) .nil .nil <|
  .letOp .indexWrappingSubtract (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp .indexBitAnd (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .letOp (.indexConstant 0) .nil .nil <|
  .letOp .indexEqual (.cons (.there .here) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

private theorem retainedMask (m : DomainModel) (table : Evaluation.MeaningsOn m.toCarriers closedInterface)
    (n : Nat) (bound : n + 1 ≤ 5) :
    maskCheck.ReturnsValues (Evaluation.meaningOn m SiteObservations.closed table) (.cons (2 ^ (n+1)) .nil) (.cons true .nil) := by
  have small : n ≤ 4 := by omega
  unfold Region.ReturnsValues
  interval_cases n <;> kernel_rfl

private theorem guardBody (m : DomainModel) (table : Evaluation.MeaningsOn m.toCarriers closedInterface)
    (rows : Nat) (shift g si gi ti : m.Field FriSource.extension)
    (nonzero : rows ≠ 0) (nonunit : rows ≠ 1) (masked : maskCheck.ReturnsValues (Evaluation.meaningOn m SiteObservations.closed table) (.cons rows .nil) (.cons true .nil))
    (shiftUnit : shift * si = 1) (gUnit : g * gi = 1) (two : (1 + 1) * ti = 1)
    (half : invoke table helper11Helper (.cons g (.cons (logicalShiftRight rows 1) .nil)) =
      .done (.cons (0 - 1 : m.Field FriSource.extension) .nil))
    (full : invoke table helper11Helper (.cons g (.cons rows .nil)) = .done (.cons 1 .nil)) :
    helper12Body.ReturnsValues (Evaluation.meaningOn m SiteObservations.closed table)
      (inputs m rows shift g si gi ti) (.cons true .nil) := by
  let one : m.Field FriSource.extension := Nat.cast 1
  let zero : m.Field FriSource.extension := Nat.cast 0
  have one_eq : one = 1 := Nat.cast_one
  have zero_eq : zero = 0 := Nat.cast_zero
  have sourceShift : shift * si = one := shiftUnit.trans one_eq.symm
  have sourceGenerator : g * gi = one := gUnit.trans one_eq.symm
  have sourceTwo : (one + one) * ti = one := by rw [one_eq]; exact two
  have sourceMid : (0 - 1 : m.Field FriSource.extension) = zero - one := by rw [zero_eq, one_eq]
  guard_step (.cons 0 .nil)
  · as_aux_lemma => rfl
  guard_step (.cons false .nil)
  · as_aux_lemma => exact equalFalse m nonzero
  guard_step (.cons false .nil)
  · as_aux_lemma => rfl
  guard_step (.cons true .nil)
  · as_aux_lemma => rfl
  guard_step (.cons true .nil)
  · change PIR.Process.done (I := closedInterface) (Values.cons (Value := m.Value) (ty := .boolean)
      (decide (rows = 1) == false) .nil) = _
    rw [decide_eq_false nonunit]; rfl
  as_aux_lemma =>
    guard_step (.cons true .nil)
    · exact branchTaken m table maskCheck _ (.cons rows .nil) (.cons true .nil) masked
    guard_step (.cons true .nil)
    · as_aux_lemma => exact equalTrue m sourceShift
    guard_step (.cons true .nil)
    · as_aux_lemma => exact equalTrue m sourceGenerator
    guard_step (.cons true .nil)
    · as_aux_lemma => exact equalTrue m sourceTwo
    guard_step (.cons true .nil)
    · change (invoke table helper11Helper (.cons g (.cons (logicalShiftRight rows 1) .nil))).bind _ = _
      rw [half]
      exact equalTrue m sourceMid
    guard_step (.cons true .nil)
    · change (invoke table helper11Helper (.cons g (.cons rows .nil))).bind _ = _
      rw [full]
      exact equalTrue m one_eq.symm
    apply Region.ReturnsValues.ret

set_option maxRecDepth 5000 in
private def law (n : Nat) (bound : n + 1 ≤ 5) (shift : Octic) (nonzero : shift ≠ 0) :
    ReferenceLaw model helper12Helper.inputs helper12Helper.outputs where
  body := helper12Body
  reference _ := .returned (.cons true .nil)
  Requires table args := args = arguments n shift ∧
    power table (RetainedDomain.root (n + 1)) (2 ^ n) (-1) ∧
    power table (RetainedDomain.root (n + 1)) (2 ^ (n + 1)) 1
  valid table args h := by
    obtain ⟨rfl, half, full⟩ := h
    have notOne : 2 ^ (n + 1) ≠ 1 := by
      have := Nat.two_pow_pos n
      rw [pow_succ]; omega
    have rootNonzero := (RetainedDomain.order (n + 1) (by omega)).ne_zero (by positivity)
    apply guardBody model table _ _ _ _ _ _ (by positivity) notOne (retainedMask model table n bound)
      (mul_inv_cancel₀ nonzero) (mul_inv_cancel₀ rootNonzero)
    · change ((1 : Octic) + 1) * (2 : Octic)⁻¹ = 1
      rw [one_add_one_eq_two]; exact mul_inv_cancel₀ HolderFold.two_nonzero
    · unfold power at half
      rw [halfSize n bound]
      change invoke table helper11Helper _ = .done (Values.cons (Value := model.Value) (ty := .field FriSource.extension) (0 - 1 : Octic) .nil)
      rw [zero_sub]
      exact half
    · exact full

private theorem installedPower (g : Octic) (e : Nat) (bounded : e < wordModulus) :
    power (closedMeaningsOn model unit.definitions) g e (g ^ e) := by
  refine ((FriPower.powerLaw model).invoke unit.definitions unit.linked (helper := helper11Helper)
    (by exact_body helper11Definition) (.cons g (.cons e .nil))
    (FriPower.dependencies model unit.definitions unit.linked (by exact_body helper7Definition)
      (by exact_body helper8Definition) (by exact_body helper9Definition) (by exact_body helper10Definition) g e)).trans ?_
  change primitiveOutcome (WordPower.outcome model FriSource.extension g e) = _
  rw [WordPower.outcome_power model FriSource.extension g e bounded]
  rfl

/-- The verifier accepts these exact six captures at the linked geometry
predicate for every retained binary folding round. -/
theorem installed (n : Nat) (bound : n + 1 ≤ 5) (shift : Octic) (nonzero : shift ≠ 0) :
    invoke (unit.oracleCalculations model 1) helper12Helper
      (ProtocolValue.embedComponents (arguments n shift).present) =
      .done (.cons (OracleProtocol.concrete model .boolean true) .nil) := by
  have order := RetainedDomain.order (n + 1) (by omega)
  have half := (IsPrimitiveRoot.pow (by positivity) order (pow_succ 2 n)).eq_neg_one_of_two_right
  have bounded : 2 ^ (n + 1) < wordModulus := Nat.pow_lt_pow_right (by decide) (by omega)
  apply (law n bound shift nonzero).invokeOracleConcrete unit 1 rfl FriPairIndex.mathFragment unit.linked
    (by exact_body helper12Definition) (arguments n shift)
  exact ⟨rfl, half ▸ installedPower _ _ (lt_trans (Nat.pow_lt_pow_right (by decide) (by omega)) bounded),
    order.pow_eq_one ▸ installedPower _ _ bounded⟩

end ZkcSecurity.ArkLib.Fri.BinaryDomain
