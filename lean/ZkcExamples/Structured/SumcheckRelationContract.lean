module

public import Zkc.Source.Structured.Linking
public import ZkcExamples.Structured.SumcheckSourceSelections
public import Zkc.Protocols.Multilinear.Source.Bindings
public import ZkcExamples.Structured.SumcheckSourceBodies
public import ZkcExamples.Structured.SumcheckReduceBodies
public import Zkc.Protocols.Multilinear.Source.MapFirstBodies

@[expose] public section

/-! Pure input-shape and total-sum source formulas used by the maintained Sumcheck library.
The bodies are checked against actual retained definitions by `BodyIn` clients.
Finite-domain capacity remains an explicit premise of Boolean adequacy. -/
namespace ZkcExamples.Structured.SumcheckRelationContract
open Zkc.Source Zkc.Source.Structured


abbrev scalar : Ty := .field "bls12-381.fr"
abbrev vector : Ty := .vector "bls12-381.fr"

open ReferenceLibrary

abbrev shapeBody := SumcheckSourceBodies.inputShapeBody
abbrev valuesHelper := SumcheckSourceBodies.valuesHelper
abbrev valuesBody := SumcheckSourceBodies.valuesBody
abbrev pendingHelper := SumcheckSourceBodies.pendingFormulaHelper
abbrev pendingBody := SumcheckSourceBodies.pendingFormulaBody
abbrev tableShapeHelper := SumcheckReduceBodies.tableShapeFormulaHelper
abbrev tableShapeBody := SumcheckReduceBodies.tableShapeFormulaBody

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The exact pure input-shape formula, with no execution or capacity premise. -/
theorem shape_equation (table : Meanings F G) (raw : List F) (rounds : Nat) :
    shapeBody.denote (meaning F G table) (Values.cons raw (.cons rounds .nil)).get =
      .done (.cons (decide (raw.length = 2 ^ rounds ∧ rounds ≤ 2)) .nil) := by
  exact (Evaluation.denote_meaning_eq_meaningOn SiteObservations.closed table shapeBody _).trans
    ((ReferenceLibrary.Sum.inputShape (ringModel F G) "bls12-381.fr" 2).valid
      table (.cons raw (.cons rounds .nil)) trivial)

variable {definitions : List CheckedDefinition}
    (linked : DeclarationsLinked [] definitions)
    (bodies : Sum.Bodies (ringModel F G) definitions "bls12-381.fr"
      SumcheckSourceSelections.sumBindings)

include linked bodies

/-- Bounded invocation is a specialization of the library's complete outcome.
Its source binding comes from the admitted scalar relation. -/
theorem total_equation (xs : List F) (bounded : xs.length < indexLimit) :
    invoke (closedMeanings (F := F) (G := G) definitions) SumcheckSourceBodies.sumTotalHelper
      (.cons xs .nil) = .done (.cons xs.sum .nil) := by
  rw [closedMeanings_eq_closedMeaningsOn]
  refine (Sum.total_eq (ringModel F G) linked bodies xs).trans ?_
  simp [Sum.totalOutcome, bounded, primitiveOutcome]
  rfl

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
  let model := ringModel F G
  let law := Sum.pendingRelation model "bls12-381.fr" SumcheckSourceSelections.sumBindings valuesHelper.name
  let arguments : Values (assignment F G) pendingHelper.inputs :=
    .cons xs (.cons dimension (.cons width (.cons point (.cons claim .nil))))
  refine (law.invokeUniform definitions linked association arguments ?_).trans ?_
  · constructor
    · exact (values.invoke linked (.cons xs (.cons dimension (.cons width .nil)))).trans rfl
    · rw [closedMeanings_eq_closedMeaningsOn]
      exact Sum.total_eq model linked bodies _
  · simp [law, arguments, Sum.pendingRelation, bounded, primitiveOutcome]
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
  let table := closedMeanings (F := F) (G := G) definitions
  let args : Values (assignment F G) tableShapeHelper.inputs := .cons xs (.cons dimension (.cons width .nil))
  refine (Evaluation.denote_meaning_eq_meaningOn SiteObservations.closed table tableShapeBody args.get).trans ?_
  apply (ReferenceLibrary.Sum.tableShape (ringModel F G) "bls12-381.fr"
    MultilinearSourceBindings.common).valid table args
  exact ⟨widthBody.invoke linked args, values.invoke linked args, variablesBody.invoke linked args⟩

end ZkcExamples.Structured.SumcheckRelationContract
