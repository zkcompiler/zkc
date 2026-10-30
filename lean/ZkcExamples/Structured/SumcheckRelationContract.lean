module

public import Zkc.Source.Structured.Linking
public import Zkc.Source.RegionDerivation
public import Zkc.Protocols.Multilinear.Source.MapFirstBodies

@[expose] public section

/-! Pure input-shape and total-sum source formulas used by the maintained Sumcheck library.
The bodies are checked against actual retained definitions by `BodyIn` clients.
Finite-domain capacity remains an explicit premise of Boolean adequacy. -/
namespace ZkcExamples.Structured.SumcheckRelationContract
open Zkc.Source Zkc.Source.Structured


abbrev scalar : Ty := .field "bls12-381.fr"
abbrev vector : Ty := .vector "bls12-381.fr"

/-- The exact bounded shape formula retained for the public Sumcheck input clause.
Its total Math operations carry no execution or security correspondence claim. -/
abbrev shapeHelper : Helper :=
  ⟨"zkf_9ca6c98faa0d00ed80eb608a89db1544ad71443a8944af6ac99e6fd78cb3660b",
    .math, [vector, .index], [.boolean]⟩

def shapeBody : Region dialect shapeHelper.inputs shapeHelper.outputs :=
  .letOp (.vectorLength "bls12-381.fr") (.cons .here .nil) .nil <|
  .letOp .indexPowerOfTwo (.cons .here (.cons (.there (.there .here)) .nil)) .nil <|
  .letOp (.indexConstant 2) .nil .nil <|
  .letOp .indexLess (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.booleanConstant false) .nil .nil <|
  .letOp .booleanEqual (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp .booleanAnd (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil
    (.ret (.cons .here .nil))

abbrev addHelper : Helper :=
  ⟨"zkl_3fc17a64a5bb6e75192d0a1362e9954f0d434a10d0f93e319db6b516835a1005",
    .math, [scalar, scalar], [scalar]⟩
abbrev totalHelper : Helper :=
  ⟨"zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e",
    .math, [vector], [scalar]⟩
abbrev sumHelper : Helper :=
  ⟨"zkf_116f3285742dd1275b8149c69b78a6713cd6256a8af715be7c346da1c793a766",
    .math, [vector, scalar], [.boolean]⟩
abbrev valuesHelper : Helper :=
  ⟨"zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33",
    .math, [vector, .index, .index], [vector]⟩

abbrev foldSpec : FoldSpec :=
  ⟨DomainSpec.elements ("finite_" ++ totalHelper.name ++ "_s1_domain") [vector] (.vector "bls12-381.fr") .here,
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

/-- The current continuation formula reads the full Pending prefix and scalar. -/
abbrev pendingHelper : Helper :=
  ⟨"zkf_c51d11bf318ad26bc2fce7b89eec63f85b98f57e91e0e9e6256f84a573b5b6e6",
    .math, [vector, .index, .index, vector, scalar], [.boolean]⟩

def pendingBody : Region dialect pendingHelper.inputs pendingHelper.outputs :=
  .letOp (.invoke valuesHelper)
    (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.multilinearRestrictPrefix "bls12-381.fr")
    (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.invoke totalHelper) (.cons .here .nil) .nil <|
  .letOp (.fieldEqual "bls12-381.fr")
    (.cons (.there (.there (.there (.there (.there (.there (.there .here)))))))
      (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

def valuesBody : Region dialect valuesHelper.inputs valuesHelper.outputs :=
  .ret (.cons .here .nil)

abbrev tableShapeHelper : Helper :=
  ⟨"zkf_326ab2331715c62ba21cb6a967c927ba6ad7f7f2da5e84eb0e5de0fc610f26ca", .math, [(.vector "bls12-381.fr"), .index, .index], [.boolean]⟩

def tableShapeBody : Region dialect tableShapeHelper.inputs tableShapeHelper.outputs :=
  .letOp (.invoke (⟨ "zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275", .math, [(.vector "bls12-381.fr"), .index, .index], [.index] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.indexConstant 1) .nil .nil <|
  .letOp .indexEqual (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.invoke (⟨ "zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", .math, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil))) .nil <|
  .letOp (.vectorLength "bls12-381.fr") (.cons .here .nil) .nil <|
  .letOp (.invoke (⟨ "zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94", .math, [(.vector "bls12-381.fr"), .index, .index], [.index] ⟩ : Helper)) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil))) .nil <|
  .letOp .indexPowerOfTwo (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp .booleanAnd (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)


/-- All dependencies must belong to the same actual linked helper inventory. -/
structure Bodies (definitions : List CheckedDefinition) : Prop where
  add : BodyIn definitions addHelper addBody
  step : BodyIn definitions foldSpec.stepHelper stepBody
  total : BodyIn definitions totalHelper totalBody

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The exact pure input-shape formula, with no execution or capacity premise. -/
theorem shape_equation (table : Meanings F G) (raw : List F) (rounds : Nat) :
    shapeBody.denote (meaning F G table) (Values.cons raw (.cons rounds .nil)).get =
      .done (.cons (decide (raw.length = 2 ^ rounds ∧ rounds ≤ 2)) .nil) := by
  change (PIR.Process.done (Values.cons
    (naturalPowerOfTwo raw.length rounds && (decide (2 < rounds) == false)) .nil) :
      Closed (Values (assignment F G) [.boolean])) = _
  rw [naturalPowerOfTwo_eq_decide]
  by_cases bound : rounds ≤ 2
  · have upper : ¬ 2 < rounds := by omega
    simp [bound, upper]
  · have upper : 2 < rounds := by omega
    simp [bound, upper]

private abbrev identityEffect : PIR.OperationInterpretation closedInterface closedInterface :=
  fun op => .call op .done

theorem add_equation (table : Meanings F G) (a b : F) :
    addBody.denote (meaning F G table) (Values.cons a (.cons b .nil)).get =
      .done (.cons (a + b) .nil) := by
  let env : Environment (assignment F G) [scalar, scalar] := (Values.cons a (.cons b (Values.nil : Values (assignment F G) []))).get
  have derivation : Region.Derivation (meaning F G table) identityEffect addBody env
      ((PIR.Process.done (.cons (a + b) .nil)).bind fun values =>
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

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
theorem total_equation (xs : List F) (bounded : xs.length < indexLimit) :
    invoke (closedMeanings (F := F) (G := G) definitions) totalHelper (.cons xs .nil) =
      .done (.cons xs.sum .nil) := by
  rw [bodies.total.invoke linked]
  simp only [totalBody, Region.denote, meaning, Evaluation.meaning, Evaluation.operation,
    Operands.eval, Values.get, Regions.denote,
    PIR.Process.bind, Environment.prepend, Environment.push, Nat.cast_zero]
  have admitted : foldSpec.domain.admit (Values.cons xs
      (Values.nil : Values (assignment F G) [])) =
      .returned (xs.map fun item => .cons item .nil) := by
    simp [foldSpec, DomainSpec.admit_elements, Collection.values, Values.get, bounded]
  have folded := Evaluation.denoteFold_reference_map (closedMeanings (F := F) (G := G) definitions) foldSpec
    (.cons xs .nil) (.cons (0 : F) .nil) .nil xs (fun item => .cons item .nil) admitted
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
  simp only [sum_fold (G := G) xs (0 : F), zero_add, PIR.Process.bind, Environment.prepend, Environment.push]

set_option backward.isDefEq.respectTransparency false in
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
      ((PIR.Process.done (Values.cons (ty := scalar) xs.sum (Values.nil : Values (assignment F G) []))).bind fun totals =>
        (PIR.Process.done (Values.cons (ty := Ty.boolean) (decide (claim = totals.get .here)) (Values.nil : Values (assignment F G) []))).bind fun result =>
          .done (.cons (result.get .here) .nil)) := by
    unfold sumBody
    apply Region.Derivation.letOp _ _ Regions.Derivation.nil
    · intro callbacks _
      cases callbacks
      simpa only [PIR.Process.interpret_identity, Evaluation.operation, Operands.eval,
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

/-- One mathematical law for the exact retained continuation body in any unit. -/
theorem pending_equation
    (association : BodyIn definitions pendingHelper pendingBody)
    (values : BodyIn definitions valuesHelper valuesBody) (xs : List F) (dimension width : Nat)
    (point : List F) (claim : F)
    (bounded : (Zkc.Polynomial.Multilinear.restrictPrefixValues xs point).length < indexLimit) :
    invoke (closedMeanings (F := F) (G := G) definitions) pendingHelper
      (.cons xs (.cons dimension (.cons width (.cons point (.cons claim .nil))))) =
      .done (.cons (decide (claim =
        (Zkc.Polynomial.Multilinear.restrictPrefixValues xs point).sum)) .nil) := by
  rw [association.invoke linked]
  change (invoke (closedMeanings (F := F) (G := G) definitions) valuesHelper
    (.cons xs (.cons dimension (.cons width .nil)))).bind _ = _
  rw [values.invoke linked]
  change (invoke (closedMeanings (F := F) (G := G) definitions) totalHelper
    (.cons (Zkc.Polynomial.Multilinear.restrictPrefixValues xs point) .nil)).bind _ = _
  rw [total_equation linked bodies _ bounded]
  rfl

omit bodies in
/-- The independent mathematical Table shape clause is total. -/
theorem tableShape_equation
    (association : BodyIn definitions tableShapeHelper tableShapeBody)
    (widthBody : BodyIn definitions MapFirstBodies.widthHelper MapFirstBodies.widthBody)
    (values : BodyIn definitions valuesHelper valuesBody)
    (variablesBody : BodyIn definitions MapFirstBodies.variablesHelper MapFirstBodies.variablesBody)
    (xs : List F) (dimension width : Nat) :
    invoke (closedMeanings (F := F) (G := G) definitions) tableShapeHelper
      (.cons xs (.cons dimension (.cons width .nil))) =
      .done (.cons (decide (width = 1 ∧ xs.length = 2 ^ dimension)) .nil) := by
  rw [association.invoke linked]
  change (invoke (closedMeanings (F := F) (G := G) definitions) MapFirstBodies.widthHelper
    (.cons xs (.cons dimension (.cons width .nil)))).bind _ = _
  rw [widthBody.invoke linked]
  change (invoke (closedMeanings (F := F) (G := G) definitions) valuesHelper
    (.cons xs (.cons dimension (.cons width .nil)))).bind _ = _
  rw [values.invoke linked]
  change (invoke (closedMeanings (F := F) (G := G) definitions) MapFirstBodies.variablesHelper
    (.cons xs (.cons dimension (.cons width .nil)))).bind _ = _
  rw [variablesBody.invoke linked]
  change (PIR.Process.done (Values.cons
    (decide (width = 1) && naturalPowerOfTwo xs.length dimension) .nil) :
    Closed (Values (assignment F G) [.boolean])) = _
  rw [naturalPowerOfTwo_eq_decide]
  by_cases width = 1 <;> by_cases xs.length = 2 ^ dimension <;> simp_all

end ZkcExamples.Structured.SumcheckRelationContract
