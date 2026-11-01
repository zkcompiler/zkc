module

public import Tests.MathematicalCompanionSigmaGoals
public import Zkc.Protocols.Sigma.Source
public meta import ZkcTools.StructuredSource.Association

@[expose] public section

/-! Reuse the ordinary independent-witness family on the actual retained
relation helper. Sampling and property-specific extraction remain separate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
noncomputable section
namespace Tests.MathematicalCompanionSigma
open Zkc.Source Zkc.Source.Structured
open MathematicalCompanionSigmaGoals
open ZkcExamples.Structured.Generated.Bindings.SchnorrAndRandomizedInputs

def domains : Zkc.Protocols.Sigma.Source.Domains := ⟨"bls12-381.g1", "bls12-381.fr"⟩

def relationReference (model : DomainModel)
    (firstBase firstPoint secondBase secondPoint : model.Group "bls12-381.g1")
    (firstWitness secondWitness : model.Field "bls12-381.fr") :
    PIR.Outcome (Relation.Output model) := .returned ⟨
      decide (firstPoint = model.smul domains.group domains.scalar firstWitness firstBase) &&
      decide (secondPoint = model.smul domains.group domains.scalar secondWitness secondBase)⟩

companion_goal RelationGoal for theorem relation (model : DomainModel) :
  Relation.Goal model (relationReference model) (fun _ _ _ _ _ _ _ => True)

@[zkc "mathematical-companion/randomized-and-relation"]
theorem relation_companion : RelationGoal := by
  intro model
  apply Relation.of_law model _ _ (Zkc.Protocols.Sigma.Source.independentLaw model domains) rfl
  · intro firstBase firstPoint secondBase secondPoint firstWitness secondWitness; rfl
  · intro table firstBase firstPoint secondBase secondPoint firstWitness secondWitness _; trivial

def relationLaw (model : DomainModel) :=
  Relation.law model (relationReference model) (fun _ _ _ _ _ _ _ => True)
    (zkc_companion ["mathematical-companion/randomized-and-relation" [model]])

theorem actual_relation (model : DomainModel) (input : RelationInputs.View model.Value) :
    invoke (program.payload.definitions.foldl
      (Evaluation.extendMeaningsOn model SiteObservations.closed) []) helper0Helper
      (RelationInputs.pack input) = primitiveOutcome (Relation.encodeOutcome model
        (relationReference model input.firstBase input.firstPoint input.secondBase input.secondPoint
          input.firstWitness input.secondWitness)) :=
  ReferenceLaw.invoke (helper := helper0Helper) (relationLaw model)
    program.payload.definitions program.payload.linked (by bind_structured_bodies) _ trivial

theorem related_iff {F G : Type} [CommRing F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [DecidableEq G]
    (input : RelationInputs.View (ringModel F G).Value) :
    invoke (program.payload.definitions.foldl
      (Evaluation.extendMeaningsOn (ringModel F G) SiteObservations.closed) []) helper0Helper
      (RelationInputs.pack input) =
      .done (Relation.encode (ringModel F G) { decision := true }) ↔
      input.firstPoint = input.firstWitness • input.firstBase ∧
      input.secondPoint = input.secondWitness • input.secondBase := by
  rw [actual_relation]
  change ((PIR.Process.done (Relation.encode (ringModel F G)
    { decision := decide (input.firstPoint = input.firstWitness • input.firstBase) &&
      decide (input.secondPoint = input.secondWitness • input.secondBase) }) :
      Closed (Values (ringModel F G).Value [.boolean])) =
      PIR.Process.done (Relation.encode (ringModel F G) { decision := true })) ↔ _
  simp [Relation.encode]

#print axioms actual_relation
#print axioms actual_producer
#print axioms actual_validator
end Tests.MathematicalCompanionSigma
