module

public import Zkc.Protocols.TableMembership.SourceLaws
public import Zkc.Protocols.TableMembership.BatchSourceLaws

@[expose] public section

/-! The same ordinary reference-call installation serves the membership and
point/value batch formulas. Full finite-admission outcomes are fixed before
association; no lookup chooses a replacement mathematical reference. -/
namespace Zkc.Protocols.TableMembership
open Zkc.Source Zkc.Source.Structured

namespace Source

def membershipOutcome (model : DomainModel) (field : String) (bindings : Names)
    (args : Values model.Value (membershipHelper field bindings).inputs) :
    PIR.Outcome (Values model.Value [.boolean]) :=
  if Admissible (args.get .here) (args.get (.there .here)) then
    .returned (.cons (PIR.Relation.Table.membership (args.get .here)
      ((args.get (.there .here)).map decodeQuery)) .nil)
  else .stopped .exhausted

def formulaLaw (model : DomainModel) (field : String) (bindings : Names) :
    ReferenceLaw model (formulaHelper field bindings).inputs [.boolean] :=
  ReferenceLibrary.forward model (membershipHelper field bindings)
    (Operands.identity _) (membershipOutcome model field bindings)

end Source

namespace BatchSource

def batchOutcome (model : DomainModel) (field : String) (bindings : Names)
    (args : Values model.Value (batchValuesHelper field bindings).inputs) :
    PIR.Outcome (Values model.Value [.boolean]) :=
  if (args.get (.there (.there .here))).length < indexLimit then
    .returned (.cons (decision (args.get .here) (args.get (.there .here))
      (args.get (.there (.there .here)))) .nil)
  else .stopped .exhausted

def formulaLaw (model : DomainModel) (field : String) (bindings : Names) :
    ReferenceLaw model (formulaHelper field bindings).inputs [.boolean] :=
  ReferenceLibrary.forward model (batchValuesHelper field bindings)
    (Operands.identity _) (batchOutcome model field bindings)

end BatchSource

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Relate the established uniform helper fold to the domain-indexed API.
This changes only the evaluator presentation, with the same definitions. -/
theorem closed_ring (definitions : List CheckedDefinition) :
    definitions.foldl (Evaluation.extendMeaningsOn (ringModel F G) SiteObservations.closed) [] =
      closedMeanings (F := F) (G := G) definitions := by
  have extend : Evaluation.extendMeaningsOn (ringModel F G) SiteObservations.closed =
      Evaluation.extendMeanings (F := F) (G := G) SiteObservations.closed :=
    funext fun table => funext fun definition =>
      (Evaluation.extendMeanings_eq_extendMeaningsOn _ table definition).symm
  rw [extend]

namespace Source

/-- Installation into an arbitrary actual linked helper closure. This theorem
uses the ordinary ReferenceLaw API, retaining the complete stopped outcome. -/
theorem formula_installed {definitions : List CheckedDefinition} {field : String} {bindings : Names}
    (linked : DeclarationsLinked [] definitions) (bodies : Bodies definitions field bindings)
    (args : Values (assignment F G) (formulaHelper field bindings).inputs) :
    invoke (closedMeanings (F := F) (G := G) definitions) (formulaHelper field bindings) args =
      primitiveOutcome ((formulaLaw (ringModel F G) field bindings).reference args) := by
  have associated : BodyIn definitions (formulaHelper field bindings)
      (formulaLaw (ringModel F G) field bindings).body := bodies.formula
  have premise : (formulaLaw (ringModel F G) field bindings).Requires
      (definitions.foldl (Evaluation.extendMeaningsOn (ringModel F G) SiteObservations.closed) []) args := by
    rw [closed_ring]
    cases args with | cons table rest => ?_
    cases rest with | cons queries rest => ?_
    cases rest
    change invoke (closedMeanings (F := F) (G := G) definitions) (membershipHelper field bindings)
      (.cons table (.cons queries .nil)) = primitiveOutcome (membershipOutcome (ringModel F G) field bindings
        (.cons table (.cons queries .nil)))
    rw [membership_equation linked bodies]
    unfold membershipOutcome
    simp only [Values.get]
    split <;> rfl
  have installed := (formulaLaw (ringModel F G) field bindings).invoke
    definitions linked associated args premise
  rw [closed_ring] at installed
  exact installed

end Source

namespace BatchSource

theorem formula_installed {definitions : List CheckedDefinition} {field : String} {bindings : Names}
    (linked : DeclarationsLinked [] definitions) (bodies : Bodies definitions field bindings)
    (args : Values (assignment F G) (formulaHelper field bindings).inputs) :
    invoke (closedMeanings (F := F) (G := G) definitions) (formulaHelper field bindings) args =
      primitiveOutcome ((formulaLaw (ringModel F G) field bindings).reference args) := by
  have associated : BodyIn definitions (formulaHelper field bindings)
      (formulaLaw (ringModel F G) field bindings).body := bodies.formula
  have premise : (formulaLaw (ringModel F G) field bindings).Requires
      (definitions.foldl (Evaluation.extendMeaningsOn (ringModel F G) SiteObservations.closed) []) args := by
    rw [closed_ring]
    cases args with | cons point rest => ?_
    cases rest with | cons value rest => ?_
    cases rest with | cons batch rest => ?_
    cases rest
    change invoke (closedMeanings (F := F) (G := G) definitions) (batchValuesHelper field bindings)
      (.cons point (.cons value (.cons batch .nil))) = primitiveOutcome (batchOutcome (ringModel F G) field bindings
        (.cons point (.cons value (.cons batch .nil))))
    unfold batchOutcome
    simp only [Values.get]
    by_cases bounded : batch.length < indexLimit
    · rw [ite_eq_left bounded, batchValues_bounded linked bodies point value batch bounded]
      rfl
    · rw [ite_eq_right bounded, batchValues_exhausted linked bodies point value batch bounded]
      rfl
  have installed := (formulaLaw (ringModel F G) field bindings).invoke
    definitions linked associated args premise
  rw [closed_ring] at installed
  exact installed

end BatchSource
end Zkc.Protocols.TableMembership
