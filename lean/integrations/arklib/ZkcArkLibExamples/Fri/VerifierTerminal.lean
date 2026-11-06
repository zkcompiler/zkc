module

public import ZkcArkLibExamples.Fri.RetainedFold
public import Zkc.Source.Structured.ReferenceLibrary

@[expose] public section

/-! The last guard compares against the value returned by the source's
terminal helper. Its polynomial is constructed from the delivered coefficient
list, and its point uses the actual shifted domain and sampled position. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.VerifierTerminal
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open ZkcSecurity.Domains.KoalaBearModel (model)
open ZkcSecurity.Domains.KoalaBear (Octic)
open FriSource (extension)
open FriSourceBodies FriSourceViews

variable (M : DomainModel) (d : String)

private def fromCoefficients := ReferenceLibrary.marked M "s0"
  (ReferenceLibrary.execute M (inputs := [.vector d]) (.numerical .polyFromCoefficients d "") (.cons .here .nil))

private def evaluate := ReferenceLibrary.marked M "s0"
  (ReferenceLibrary.execute M (inputs := [.polynomial d, .field d]) (.numerical .polyEvaluate d "")
    (.cons .here (.cons (.there .here) .nil)))

private theorem makePolynomial (cs : List (M.Field d)) (size : cs.length < indexLimit) :
    Numerical.checkedEvaluateOn M.toFieldModel d "" .polyFromCoefficients (.cons cs .nil) =
      .returned (.cons (PolynomialValue.ofCoefficients 0 cs) .nil) := by
  have admitted : @Numerical.checkValues M.toFieldModel (Numerical.polyFromCoefficients.arguments d "")
      (.cons cs .nil) = .ok () := by
    change (do Numerical.size cs.length; Except.ok ()) = _
    simp [Numerical.size, size, bind, Except.bind]
  unfold Numerical.checkedEvaluateOn
  rw [admitted]
  rfl

private theorem evaluatePolynomial (cs : List (M.Field d)) (size : cs.length < indexLimit) (x : M.Field d) :
    Numerical.checkedEvaluateOn M.toFieldModel d "" .polyEvaluate
      (.cons (PolynomialValue.ofCoefficients 0 cs) (.cons x .nil)) =
      .returned (.cons (Numerical.evaluate (PolynomialValue.ofCoefficients 0 cs).coefficients x) .nil) := by
  have trimmed : (normalizeCoefficients (0 : M.Field d) cs).length < indexLimit :=
    lt_of_le_of_lt (normalizeCoefficients_length_le _ _) size
  have admitted : @Numerical.checkValues M.toFieldModel (Numerical.polyEvaluate.arguments d "")
      (.cons (PolynomialValue.ofCoefficients 0 cs) (.cons x .nil)) = .ok () := by
    change (do (do Numerical.size (normalizeCoefficients 0 cs).length; Numerical.require ((0 : M.Field d) = 0))
               Except.ok (); Except.ok ()) = _
    simp [Numerical.size, Numerical.require, trimmed, bind, Except.bind]
  unfold Numerical.checkedEvaluateOn
  rw [admitted]
  rfl

private theorem pointValue (shift generator : M.Field d) (nonzero : shift ≠ 0) (n i : Nat)
    (size : n < indexLimit) (inside : i < n) (root : Numerical.domainRoot M.toFieldModel d n = .ok generator) :
    (Primitive.numerical .polyPoint d "").evaluateOn M.toFieldModel (.cons shift (.cons n (.cons i .nil))) =
      .returned (.cons (shift * generator ^ i) .nil) := by
  let field := {M.toFieldModel with inverse := fun _ ↦ none}
  change Numerical.checkedEvaluateOn field d "" .polyPoint (.cons shift (.cons n (.cons i .nil))) = _
  have selected : Numerical.domainRoot field d n = .ok generator := by
    refine Eq.trans ?_ root
    unfold Numerical.domainRoot
    cases family : M.toFieldModel.twoAdic d with
    | none => simp [field]
    | some f => cases cell : f.roots[n.log2]? <;> simp [field, cell]
  have admitted : @Numerical.checkValues field (Numerical.polyPoint.arguments d "")
      (.cons shift (.cons n (.cons i .nil))) = .ok () := by
    change (do Except.ok (); Numerical.require (n < indexLimit); Numerical.require (i < indexLimit); Except.ok ()) = _
    simp [Numerical.require, size, inside.trans size, bind, Except.bind]
  unfold Numerical.checkedEvaluateOn
  rw [admitted]
  simp [Numerical.evaluateOn, selected, Numerical.require, nonzero, inside, Numerical.finish,
    bind, Except.bind, pure, Except.pure]
  rfl

private theorem body (M : DomainModel) (table : Evaluation.MeaningsOn M.toCarriers closedInterface)
    (cs : List (M.Field extension)) (shift x value : M.Field extension) (n i : Nat)
    (construct : invoke table helper34Helper (.cons cs .nil) =
      .done (.cons (PolynomialValue.ofCoefficients 0 cs) .nil))
    (point : (Primitive.numerical .polyPoint extension "").evaluateOn M.toFieldModel
      (.cons shift (.cons n (.cons i .nil))) = .returned (.cons x .nil))
    (evalAt : invoke table helper35Helper (.cons (PolynomialValue.ofCoefficients 0 cs) (.cons x .nil)) =
      .done (.cons value .nil)) :
    helper36Body.denote (meaningOn M table) (Values.cons (ty := Ty.vector extension) (Value := M.Value)
      cs (.cons shift (.cons n (.cons i .nil)))).get = .done (.cons value .nil) := by
  have makeStep : (meaningOn M table).OperationLaw (fun op ↦ .call op .done) (.invoke helper34Helper)
      (.cons cs .nil) .nil (.done (.cons (PolynomialValue.ofCoefficients 0 cs) .nil)) :=
    RegionMeaning.OperationLaw.identity _ _ _ construct
  have pointStep : (meaningOn M table).OperationLaw (fun op ↦ .call op .done)
      (.exec (.numerical .polyPoint extension "")) (.cons shift (.cons n (.cons i .nil))) .nil
      (.done (.cons x .nil)) :=
    RegionMeaning.OperationLaw.identity _ _ _ (congrArg (@primitiveOutcome closedInterface _) point)
  have evalStep : (meaningOn M table).OperationLaw (fun op ↦ .call op .done) (.invoke helper35Helper)
      (.cons (PolynomialValue.ofCoefficients 0 cs) (.cons x .nil)) .nil (.done (.cons value .nil)) :=
    RegionMeaning.OperationLaw.identity _ _ _ evalAt
  derive_process using (first | exact makeStep | exact pointStep | exact evalStep)

theorem installed {I : PIR.Signature} {k : Nat} (bound : k ≤ 5)
    (cs : List Octic) (length : cs.length < indexLimit) (shift : Octic)
    (nonzero : shift ≠ 0) (index : Fin (2 ^ k)) :
    invoke (RetainedFold.helpers (I := I)).closed helper36Helper
      (.cons cs (.cons shift (.cons (2 ^ k) (.cons index.val .nil)))) =
      .done (.cons (terminal (F := Octic) RetainedDomain.root cs shift k index.val) .nil) := by
  let table := closedMeaningsOn model unit.definitions
  let x := point RetainedDomain.root shift k index.val
  have size : 2 ^ k < indexLimit := lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) bound)
    (by decide : 2 ^ 5 < indexLimit)
  have construct := (fromCoefficients model extension).invoke (helper := helper34Helper)
    unit.definitions unit.linked (by exact_body helper34Definition) (.cons cs .nil) trivial
  have evalAt := (evaluate model extension).invoke (helper := helper35Helper)
    unit.definitions unit.linked (by exact_body helper35Definition)
    (.cons (PolynomialValue.ofCoefficients 0 cs) (.cons x .nil)) trivial
  have coefficients := construct.trans (congrArg (@primitiveOutcome closedInterface _)
    (makePolynomial model extension cs length))
  have result := evalAt.trans (congrArg (@primitiveOutcome closedInterface _)
    (evaluatePolynomial model extension cs length x))
  have association : BodyIn unit.definitions helper36Helper helper36Body := by exact_body helper36Definition
  obtain ⟨definition, member, signature, raw⟩ := association
  rw [Evaluation.closed_invoke_componentTablesOn, Evaluation.definitions_invoke_body_view_asOn model
    SiteObservations.closed unit.definitions unit.linked definition member helper36Helper signature helper36Body raw]
  rw [body model table cs shift x _ _ _ coefficients
    (pointValue model extension shift _ nonzero _ _ size index.isLt (RetainedDomain.domainRoot k bound)) result]
  exact congrArg (fun value : Octic ↦ PIR.Process.done (I := I)
    (Values.cons (ty := Ty.field extension) (Value := model.Value) value .nil))
    (Phases.terminal_source_evaluate RetainedDomain.root cs shift k index.val)

end ZkcSecurity.ArkLib.Fri.VerifierTerminal
