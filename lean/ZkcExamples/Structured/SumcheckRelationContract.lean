module

public import Zkc.Source.Structured.Linking
public import Zkc.Source.RegionDerivation

@[expose] public section

/-! Total-sum source formulas used by the maintained Sumcheck library.
The bodies are checked against actual retained definitions by `BodyIn` clients.
Finite-domain capacity remains an explicit premise of Boolean adequacy. -/
namespace ZkcExamples.Structured.SumcheckRelationContract
open Zkc.Source Zkc.Source.Structured

set_option backward.isDefEq.respectTransparency false

abbrev scalar : Ty := .field "bls12-381.fr"
abbrev vector : Ty := .vector "bls12-381.fr"

abbrev addHelper : Helper :=
  ⟨"zkl_3fc17a64a5bb6e75192d0a1362e9954f0d434a10d0f93e319db6b516835a1005",
    .math, [scalar, scalar], [scalar]⟩
abbrev totalHelper : Helper :=
  ⟨"zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e",
    .math, [vector], [scalar]⟩
abbrev sumHelper : Helper :=
  ⟨"zkf_116f3285742dd1275b8149c69b78a6713cd6256a8af715be7c346da1c793a766",
    .math, [vector, scalar], [.boolean]⟩
abbrev tableSumHelper : Helper :=
  ⟨"zkf_654a0e58b11e83f398996b9e830df00890bec0f8dc08a65c5750d6d9c759b643",
    .math, [vector, .index, .index, scalar], [.boolean]⟩
abbrev valuesHelper : Helper :=
  ⟨"zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33",
    .math, [vector, .index, .index], [vector]⟩

abbrev foldSpec : FoldSpec :=
  ⟨⟨"finite_" ++ totalHelper.name ++ "_s1_domain", [vector], "bls12-381.fr", .here, false⟩,
    [scalar], [], "finite_" ++ totalHelper.name ++ "_s1_body", "", .math⟩

def addBody : Region dialect addHelper.inputs addHelper.outputs :=
  .letOp (.fieldAdd "bls12-381.fr") (.cons .here (.cons (.there .here) .nil)) .nil
    (.ret (.cons .here .nil))

def stepBody : Region dialect foldSpec.stepHelper.inputs foldSpec.stepHelper.outputs :=
  .letOp (.invoke addHelper) (.cons .here (.cons (.there .here) .nil)) .nil
    (.ret (.cons .here .nil))

def totalBody : Region dialect totalHelper.inputs totalHelper.outputs :=
  .letOp (.fieldConstant "bls12-381.fr" 0) .nil .nil <|
  .letOp (.fold foldSpec) (.cons (.there .here) (.cons .here .nil)) .nil
    (.ret (.cons .here .nil))

def sumBody : Region dialect sumHelper.inputs sumHelper.outputs :=
  .letOp (.invoke totalHelper) (.cons .here .nil) .nil <|
  .letOp (.fieldEqual "bls12-381.fr")
    (.cons (.there (.there .here)) (.cons .here .nil)) .nil
    (.ret (.cons .here .nil))

def tableSumBody : Region dialect tableSumHelper.inputs tableSumHelper.outputs :=
  .letOp (.invoke valuesHelper)
    (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.invoke totalHelper) (.cons .here .nil) .nil <|
  .letOp (.fieldEqual "bls12-381.fr")
    (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil)) .nil
    (.ret (.cons .here .nil))

def valuesBody : Region dialect valuesHelper.inputs valuesHelper.outputs :=
  .ret (.cons .here .nil)

/-- All dependencies must belong to the same actual linked helper inventory. -/
structure Bodies (definitions : List CheckedDefinition) : Prop where
  add : BodyIn definitions addHelper addBody
  step : BodyIn definitions foldSpec.stepHelper stepBody
  total : BodyIn definitions totalHelper totalBody

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

private abbrev identityEffect : PIR.OperationInterpretation closedInterface closedInterface :=
  fun op => .call op .done

theorem add_equation (table : Meanings F G) (a b : F) :
    addBody.denote (meaning F G table) (Values.cons a (.cons b .nil)).get =
      .done (.cons (a + b) .nil) := by
  let env : Environment (assignment F G) [scalar, scalar] := (Values.cons a (.cons b (Values.nil : Values (assignment F G) []))).get
  have derivation : Region.Derivation (meaning F G table) identityEffect addBody env
      ((PIR.Proc.done (.cons (a + b) .nil)).bind fun values =>
        .done (Operands.eval (env.prepend values) (.cons .here .nil))) := by
    unfold addBody
    apply Region.Derivation.letOp _ _ Regions.Derivation.nil ?_ (fun _ => .ret _ _)
    intro callbacks _
    cases callbacks
    rfl
  exact derivation.sound_identity

variable {definitions : List CheckedDefinition}
    (linked : DeclarationsLinked [] definitions) (bodies : Bodies definitions)

include linked bodies

theorem step_equation (xs : List F) (a x : F) :
    invoke (closedMeanings (F := F) (G := G) definitions) foldSpec.stepHelper (.cons a (.cons x (.cons xs .nil))) =
      .done (.cons (a + x) .nil) := by
  rw [bodies.step.invoke linked]
  simp only [stepBody, Region.denote, meaning, Evaluation.meaning, Evaluation.operation,
    Operands.eval, Values.get, Regions.denote]
  rw [bodies.add.invoke linked, add_equation]
  rfl

omit linked bodies [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
private theorem sum_fold (xs : List F) (initial : F) :
    xs.foldl (fun (state : Values (assignment F G) [scalar]) x =>
      Values.cons (state.get .here + x) .nil) (.cons initial .nil) =
      .cons (initial + xs.sum) .nil := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih => simpa [List.foldl_cons, Values.get, List.sum_cons, add_assoc] using ih (initial + x)

theorem total_equation (xs : List F) (bounded : xs.length < indexLimit) :
    invoke (closedMeanings (F := F) (G := G) definitions) totalHelper (.cons xs .nil) =
      .done (.cons xs.sum .nil) := by
  rw [bodies.total.invoke linked]
  simp only [totalBody, Region.denote, meaning, Evaluation.meaning, Evaluation.operation,
    Operands.eval, Values.get, Regions.denote,
    PIR.Proc.bind, Environment.prepend, Environment.push, Nat.cast_zero]
  have admitted : (foldSpec.domain.denote (Values.cons xs
      (Values.nil : Values (assignment F G) []))).admit = .returned xs := by
    simp [foldSpec, DomainSpec.denote, Finite.Domain.admit, Values.get, bounded]
  have folded := Evaluation.denoteFold_reference (closedMeanings (F := F) (G := G) definitions) foldSpec
    (.cons xs .nil) (.cons (0 : F) .nil) .nil xs admitted
    (fun (state : Values (assignment F G) [scalar]) (x : F) => Values.cons (state.get .here + x) .nil) (fun _ => True) trivial (by
      intro state x _ _
      cases state with | cons a rest => ?_
      cases rest
      constructor
      · exact (Evaluation.foldTransition_unfiltered _ foldSpec rfl _ _ _ _).trans
          (step_equation linked bodies xs a x)
      · trivial)
  change (Evaluation.denoteFold _ foldSpec
    ((Values.cons xs Values.nil).append ((Values.cons (0 : F) Values.nil).append Values.nil))).bind _ = _
  rw [folded]
  simp only [sum_fold (G := G) xs (0 : F), zero_add, PIR.Proc.bind, Environment.prepend, Environment.push]

/-- The formula's helper call, comparison and return are composed by the shared
structural derivation. The local call law is the independently proved fold law. -/
theorem sum_equation (association : BodyIn definitions sumHelper sumBody) (xs : List F)
    (claim : F) (bounded : xs.length < indexLimit) :
    invoke (closedMeanings (F := F) (G := G) definitions) sumHelper (.cons xs (.cons claim .nil)) =
      .done (.cons (decide (claim = xs.sum)) .nil) := by
  rw [association.invoke linked]
  let table := closedMeanings (F := F) (G := G) definitions
  let env : Environment (assignment F G) [vector, scalar] := (Values.cons xs (.cons claim (Values.nil : Values (assignment F G) []))).get
  have derivation : Region.Derivation (meaning F G table) identityEffect sumBody env
      ((PIR.Proc.done (Values.cons (ty := scalar) xs.sum (Values.nil : Values (assignment F G) []))).bind fun totals =>
        (PIR.Proc.done (Values.cons (ty := Ty.boolean) (decide (claim = totals.get .here)) (Values.nil : Values (assignment F G) []))).bind fun result =>
          .done (.cons (result.get .here) .nil)) := by
    unfold sumBody
    apply Region.Derivation.letOp _ _ Regions.Derivation.nil
    · intro callbacks _
      cases callbacks
      simpa only [PIR.Proc.interpret_identity, Evaluation.operation, Operands.eval,
        env, table, Values.get] using total_equation linked bodies xs bounded
    · intro totals
      cases totals with | cons total rest => ?_
      cases rest
      apply Region.Derivation.letOp _ _ Regions.Derivation.nil
      · intro callbacks _
        cases callbacks
        rfl
      · intro result
        cases result with | cons decision rest => ?_
        cases rest
        exact .ret _ _
  exact derivation.sound_identity

theorem tableSum_equation
    (association : BodyIn definitions tableSumHelper tableSumBody)
    (values : BodyIn definitions valuesHelper valuesBody) (xs : List F) (dimension width : Nat) (claim : F)
    (bounded : xs.length < indexLimit) :
    invoke (closedMeanings (F := F) (G := G) definitions) tableSumHelper
      (.cons xs (.cons dimension (.cons width (.cons claim .nil)))) =
      .done (.cons (decide (claim = xs.sum)) .nil) := by
  rw [association.invoke linked]
  simp only [tableSumBody, Region.denote, meaning, Evaluation.meaning, Evaluation.operation,
    Operands.eval, Values.get, Regions.denote]
  rw [values.invoke linked]
  simp only [valuesBody, Region.denote, Operands.eval, Values.get, PIR.Proc.bind, Environment.prepend, Environment.push]
  rw [total_equation linked bodies xs bounded]
  rfl

end ZkcExamples.Structured.SumcheckRelationContract
