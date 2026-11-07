module

public import ZkcArkLibExamples.Fri.HolderInterpolation
public import Zkc.Source.Structured.OracleReferenceLaws

@[expose] public section

/-! The terminal message has an exact public width. The admitted helper
first rejects an overlong coefficient list, then appends exactly the missing
zeros. Both called helpers are checked against their linked declarations. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.HolderPadding
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open FriSourceBodies FriSourceViews
open ZkcSecurity.Domains.KoalaBearModel (model octicIdentity)
open ZkcSecurity.Domains.KoalaBear (Octic)

abbrev d := FriSource.extension
private abbrev Table (M : DomainModel) := Evaluation.MeaningsOn M.toCarriers closedInterface
private abbrev meaning (M : DomainModel) (table : Table M) := Evaluation.meaningOn M SiteObservations.closed table

private def comparison (M : DomainModel) := ReferenceLibrary.marked M "s0"
  (ReferenceLibrary.execute M (inputs := helper19Helper.inputs) .indexLess (.cons .here (.cons (.there .here) .nil)))
private def concatenation (M : DomainModel) := ReferenceLibrary.marked M "s0"
  (ReferenceLibrary.execute M (inputs := helper20Helper.inputs) (.numerical .vectorConcat d "")
    (.cons .here (.cons (.there .here) .nil)))

private theorem execStep (M : DomainModel) (table : Table M) (op : Primitive)
    {args : Values M.Value op.arguments} {output : Values M.Value op.results}
    (ok : op.evaluateOn M.toFieldModel args = .returned output) :
    (meaning M table).OperationLaw (fun op ↦ .call op .done) (.exec op) args .nil (.done output) :=
  RegionMeaning.OperationLaw.identity _ _ _ (congrArg primitiveOutcome ok)

private theorem callStep (M : DomainModel) (table : Table M) (h : Helper)
    {args : Values M.Value h.inputs} {output : Values M.Value h.outputs}
    (ok : invoke table h args = .done output) :
    (meaning M table).OperationLaw (fun op ↦ .call op .done) (.invoke h) args .nil (.done output) :=
  RegionMeaning.OperationLaw.identity _ _ _ ok

private theorem zeroStep (M : DomainModel) (table : Table M) :
    (meaning M table).OperationLaw (fun op ↦ .call op .done) (.fieldConstant d 0) .nil .nil
      (.done (.cons 0 .nil)) := by
  apply RegionMeaning.OperationLaw.identity
  change PIR.Process.done (I := closedInterface) (Values.cons (ty := .field d) (Value := M.Value)
    ((0 : Nat) : M.Field d) .nil) = _
  rw [Nat.cast_zero]
  rfl

private theorem length_ok (M : DomainModel) (xs : List (M.Field d)) (small : xs.length < indexLimit) :
    (Primitive.vectorLength d).evaluateOn M.toFieldModel (.cons xs .nil) = .returned (.cons xs.length .nil) := by
  simp [Primitive.evaluateOn, small]

private theorem sub_ok (M : DomainModel) (n l : Nat) (small : n < indexLimit) (within : l ≤ n) :
    Primitive.indexSub.evaluateOn M.toFieldModel (.cons n (.cons l .nil)) = .returned (.cons (n-l) .nil) := by
  simp [Primitive.evaluateOn, checkedIndices, small, lt_of_le_of_lt within small, within]

private theorem fill_ok (M : DomainModel) (n : Nat) (small : n < indexLimit) :
    (Primitive.numerical .vectorFill d "").evaluateOn M.toFieldModel (.cons 0 (.cons n .nil)) =
      .returned (.cons (List.replicate n 0) .nil) := by
  change (match (do Except.ok (); Numerical.require (n < indexLimit); Except.ok () : Numerical.Result Unit) with
    | .ok () => PIR.Outcome.returned (Values.cons (ty := Ty.vector d) (Value := M.Value) (List.replicate n 0) .nil)
    | .error why => .stopped why) = _
  simp [Numerical.require, small, bind, Except.bind]
  rfl

private theorem concat_ok (M : DomainModel) (xs ys : List (M.Field d))
    (small : xs.length + ys.length < indexLimit) :
    (Primitive.numerical .vectorConcat d "").evaluateOn M.toFieldModel (.cons xs (.cons ys .nil)) =
      .returned (.cons (xs ++ ys) .nil) := by
  have x : xs.length < indexLimit := by omega
  have y : ys.length < indexLimit := by omega
  change (match (do Numerical.size xs.length; Numerical.size ys.length; Except.ok () : Numerical.Result Unit) with
    | .ok () => Numerical.finish (do Numerical.size (xs.length + ys.length)
                                     return Values.cons (ty := Ty.vector d) (Value := M.Value) (xs ++ ys) .nil)
    | .error why => .stopped why) = _
  simp [Numerical.size, x, y, small, bind, Except.bind, pure, Except.pure, Numerical.finish]
  rfl

def padded (M : DomainModel) (xs : List (M.Field d)) (n : Nat) : PIR.Outcome (Values M.Value [.vector d]) :=
  if xs.length ≤ n then .returned (.cons (xs ++ List.replicate (n - xs.length) 0) .nil) else .stopped .reject

private structure Calls (M : DomainModel) (table : Table M) (xs : List (M.Field d)) (n : Nat) : Prop where
  inputs : xs.length < indexLimit ∧ n < indexLimit
  compare : invoke table helper19Helper (.cons n (.cons xs.length .nil)) = .done (.cons (decide (n < xs.length)) .nil)
  append : xs.length ≤ n → invoke table helper20Helper (.cons xs (.cons (List.replicate (n - xs.length) 0) .nil)) =
    .done (.cons (xs ++ List.replicate (n - xs.length) 0) .nil)

private theorem body (M : DomainModel) (table : Table M) (xs : List (M.Field d)) (n : Nat)
    (calls : Calls M table xs n) :
    helper21Body.denote (meaning M table) (Values.cons (Value := M.Value) (ty := .vector d) xs (.cons n .nil)).get =
      primitiveOutcome (padded M xs n) := by
  have length := execStep M table _ (length_ok M xs calls.inputs.1)
  by_cases within : xs.length ≤ n
  · have compare := callStep M table _ (output := .cons false .nil) (calls.compare.trans (by simp [Nat.not_lt.mpr within]))
    have sub := execStep M table _ (sub_ok M n xs.length calls.inputs.2 within)
    have fill := execStep M table _ (fill_ok M (n - xs.length) (by have := calls.inputs.2; omega))
    have append := callStep M table _ (calls.append within)
    rw [padded, ite_eq_left within]
    derive_process using (first | exact length | exact compare | exact zeroStep M table | exact sub | exact fill | exact append)
  · have compare := callStep M table _ (output := .cons true .nil) (calls.compare.trans (by simp [Nat.lt_of_not_ge within]))
    rw [padded, ite_eq_right within]
    derive_process using (first | exact length | exact compare)

private def law (M : DomainModel) : ReferenceLaw M helper21Helper.inputs helper21Helper.outputs where
  body := helper21Body
  Requires table
    | .cons xs (.cons n .nil) => Calls M table xs n
  reference
    | .cons xs (.cons n .nil) => padded M xs n
  valid table
    | .cons xs (.cons n .nil), calls => body M table xs n calls

theorem installed {I : PIR.Signature} (xs : List Octic) (n : Nat)
    (vectorBound : xs.length < indexLimit) (countBound : n < indexLimit) :
    invoke (RetainedFold.helpers (I := I)).closed helper21Helper (.cons xs (.cons n .nil)) =
      primitiveOutcome (padded model xs n) := by
  apply (law model).invokeOn (I := I) unit.definitions unit.linked
    (helper := helper21Helper) (by exact_body helper21Definition)
  refine ⟨⟨vectorBound, countBound⟩, ?_, ?_⟩
  · refine ((comparison model).invoke unit.definitions unit.linked
      (helper := helper19Helper) (by exact_body helper19Definition) _ trivial).trans ?_
    change primitiveOutcome (checkedIndices n xs.length (.returned (Values.cons (ty := .boolean) (Value := model.Value) (decide (n < xs.length)) .nil))) = _
    simp [checkedIndices, countBound, vectorBound, primitiveOutcome]
    rfl
  · intro within
    refine ((concatenation model).invoke unit.definitions unit.linked
      (helper := helper20Helper) (by exact_body helper20Definition) _ trivial).trans ?_
    have bound : xs.length + (List.replicate (n - xs.length) (0 : Octic)).length < indexLimit := by
      rw [List.length_replicate]
      omega
    exact congrArg (@primitiveOutcome closedInterface _)
      (concat_ok model xs (List.replicate (n - xs.length) 0) bound)

private theorem padded_singleton {F : Type} [Zero F] [DecidableEq F] (c : F) :
    let cs := normalizeCoefficients 0 [c]
    cs ++ List.replicate (1 - cs.length) 0 = [c] := by
  by_cases zero : c = 0 <;> simp [normalizeCoefficients, zero]

private theorem padded_constant (M : DomainModel) (c : M.Field d) :
    padded M (normalizeCoefficients 0 [c]) 1 = .returned (.cons [c] .nil) := by
  have width : (normalizeCoefficients 0 [c]).length ≤ 1 := normalizeCoefficients_length_le _ _
  unfold padded
  rw [ite_eq_left width]
  exact congrArg (fun cells ↦ PIR.Outcome.returned
    (Values.cons (Value := M.Value) (ty := .vector d) cells .nil)) (padded_singleton c)

theorem installed_singleton {I : PIR.Signature} (c : Octic) :
    invoke (RetainedFold.helpers (I := I)).closed helper21Helper
      (.cons (normalizeCoefficients 0 [c]) (.cons 1 .nil)) = .done (.cons [c] .nil) := by
  have width := normalizeCoefficients_length_le (0 : Octic) [c]
  have count : 1 < indexLimit := by decide
  exact (installed (I := I) _ _ (lt_of_le_of_lt width count) count).trans
    (congrArg (@primitiveOutcome I _) (padded_constant model c))

/-- The holder's entire terminal coefficient pipeline, including exact-length
padding, for any codeword below degree one on its installed coset. -/
theorem terminal_message {I : PIR.Signature} {k : Nat} (bound : k ≤ 5)
    (shift : Octic) (nonzero : shift ≠ 0) (domain : Domain.SmoothCosetFftDomain k Octic)
    (geometry : ∀ j, domain j = point RetainedDomain.root shift k j)
    (word : Fin (2 ^ k) → Octic)
    (codeword : word ∈ ReedSolomon.code (domain : Fin (2 ^ k) ↪ Octic) 1) :
    ∃ c : Octic, (∀ i, word i = c) ∧
      (do
        let interpolant ← invoke (RetainedFold.helpers (I := I)).closed helper17Helper
          (.cons (List.ofFn word) (.cons shift .nil))
        let cs ← invoke (RetainedFold.helpers (I := I)).closed helper18Helper interpolant
        invoke (RetainedFold.helpers (I := I)).closed helper21Helper (.cons (cs.get .here) (.cons 1 .nil))) =
          .done (.cons [c] .nil) := by
  obtain ⟨c, constant, interpolated, coefficients⟩ :=
    HolderInterpolation.installed_codeword (I := I) bound shift nonzero domain geometry word codeword
  refine ⟨c, constant, ?_⟩
  rw [interpolated]
  change (invoke (RetainedFold.helpers (I := I)).closed helper18Helper
    (.cons (PolynomialValue.ofCoefficients 0 [c]) .nil)).bind _ = _
  rw [coefficients]
  exact installed_singleton c

/-- At the holder role of the actual oracle algebra, all three helpers see
the returned value of the preceding helper. This includes the empty
coefficient representation and preserves the role-local result ABI. -/
theorem holder_message {k : Nat} (bound : k ≤ 5)
    (shift : Octic) (nonzero : shift ≠ 0) (domain : Domain.SmoothCosetFftDomain k Octic)
    (geometry : ∀ j, domain j = point RetainedDomain.root shift k j)
    (word : Fin (2 ^ k) → Octic)
    (codeword : word ∈ ReedSolomon.code (domain : Fin (2 ^ k) ↪ Octic) 1) :
    let tables := RetainedFold.helpers (I := OracleProtocol.Interface model)
    ∃ c : Octic, (∀ i, word i = c) ∧
      (do
        let poly ← OracleProtocol.owned model 0 0 tables helper17Helper
          (ProtocolValue.embedComponents (Values.present (Values.cons (Value := model.Value)
            (ty := .vector d) (List.ofFn word) (.cons shift .nil))))
        let cs ← OracleProtocol.owned model 0 0 tables helper18Helper poly
        OracleProtocol.owned model 0 0 tables helper21Helper
          (.cons (cs.get .here) (.cons (some (ProtocolValue.ofConcrete .index 1)) .nil))) =
          .done (ProtocolValue.embedComponents (Values.present (Values.cons (Value := model.Value)
            (ty := .vector d) [c] .nil))) := by
  intro tables
  obtain ⟨c, constant, interpolated, coefficients⟩ := HolderInterpolation.installed_codeword
    (I := OracleProtocol.Interface model) bound shift nonzero domain geometry word codeword
  refine ⟨c, constant, ?_⟩
  rw [OracleProtocol.owned_present, interpolated]
  dsimp only [bind, PIR.Process.bind]
  rw [OracleProtocol.owned_present, coefficients]
  dsimp only [PIR.Process.bind]
  change OracleProtocol.owned model 0 0 tables helper21Helper
    (ProtocolValue.embedComponents (Values.present (Values.cons (Value := model.Value) (ty := .vector d)
      (normalizeCoefficients 0 [c]) (.cons 1 .nil)))) = _
  rw [OracleProtocol.owned_present, installed_singleton]
  rfl

end ZkcSecurity.ArkLib.Fri.HolderPadding
