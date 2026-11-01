module

public import Zkc.Protocols.Sigma.SourceInstallation
public import ZkcSecurity.Families.Sigma.Algebra

@[expose] public section

/-! Mathematical consumers of the exact nominal Sigma helper installation.
The installed relation supplies the algebraic premise for honest acceptance;
no knowledge, zero-knowledge or sampler claim follows from this equation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ZkcSecurity.Bindings.Sigma.SourceExecution
open Zkc.Source Zkc.Source.Structured Zkc.Protocols.Sigma.Source

section Mathematics
variable {F G : Type} [CommRing F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The named verifier helper accepts arbitrary nonce/challenge values under
precisely the retained discrete-log relation. -/
theorem equation_accepts (d : Domains) (base point : G) (witness nonce challenge : F)
    (related : point = witness • base) :
    (equationLaw (ringModel F G) d).reference
      (.cons base (.cons point (.cons (nonce • base)
        (.cons challenge (.cons (nonce + challenge * witness) .nil))))) =
      .returned (.cons true .nil) := by
  have equation := ZkcSecurity.Families.Sigma.honest_equation base point witness nonce challenge related
  change PIR.Outcome.returned (.cons (decide ((nonce + challenge * witness) • base =
    nonce • base + challenge • point)) .nil : Values (ringModel F G).Value [.boolean]) = _
  simp only [equation, decide_true]

omit [DecidableEq F] in
/-- Two independent witnesses are separate premises. A shared challenge does
not identify witnesses or private samples. -/
theorem independent_accepts (firstBase firstPoint secondBase secondPoint : G)
    (firstWitness secondWitness firstNonce secondNonce challenge : F)
    (firstRelated : firstPoint = firstWitness • firstBase)
    (secondRelated : secondPoint = secondWitness • secondBase) :
    decide ((firstNonce + challenge * firstWitness) • firstBase =
      firstNonce • firstBase + challenge • firstPoint) &&
    decide ((secondNonce + challenge * secondWitness) • secondBase =
      secondNonce • secondBase + challenge • secondPoint) = true := by
  obtain ⟨first, second⟩ := ZkcSecurity.Families.Sigma.and_equation
    firstBase firstPoint secondBase secondPoint firstWitness secondWitness firstNonce secondNonce
    challenge firstRelated secondRelated
  simp only [first, second, decide_true, Bool.and_self]

omit [DecidableEq F] in
/-- Sharing a witness requires both retained equations at that one value. -/
theorem shared_accepts (firstBase firstPoint secondBase secondPoint : G)
    (witness nonce challenge : F)
    (firstRelated : firstPoint = witness • firstBase)
    (secondRelated : secondPoint = witness • secondBase) :
    decide ((nonce + challenge * witness) • firstBase = nonce • firstBase + challenge • firstPoint) &&
    decide ((nonce + challenge * witness) • secondBase = nonce • secondBase + challenge • secondPoint) = true :=
  independent_accepts firstBase firstPoint secondBase secondPoint witness witness nonce nonce challenge
    firstRelated secondRelated
end Mathematics

attribute [local implicit_reducible] relationHelper independentHelper sharedHelper equationHelper

section SourceHelpers
variable {F G : Type} [CommRing F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The retained source relation, including its ordered arguments, is the
mathematical premise. A declaration with the same signature is insufficient. -/
theorem relation_accepts_iff (d : Domains) (name : String)
    (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
    (associated : BodyIn definitions (relationHelper d name) (relationBody d))
    (base point : G) (witness : F) :
    invoke (definitions.foldl (Evaluation.extendMeaningsOn (ringModel F G) SiteObservations.closed) [])
      (relationHelper d name) (.cons base (.cons point (.cons witness .nil))) =
      .done (.cons true .nil) ↔ point = witness • base := by
  rw [relation_invoke (ringModel F G) d name definitions linked associated]
  change ((PIR.Process.done (.cons (decide (point = witness • base)) .nil) :
    Closed (Values (ringModel F G).Value [.boolean])) = .done (.cons true .nil)) ↔ _
  simp

/-- Both independent witnesses are read from the exact retained helper. -/
theorem independent_accepts_iff (d : Domains) (name : String)
    (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
    (associated : BodyIn definitions (independentHelper d name) (independentRelationBody d))
    (firstBase firstPoint secondBase secondPoint : G) (firstWitness secondWitness : F) :
    invoke (definitions.foldl (Evaluation.extendMeaningsOn (ringModel F G) SiteObservations.closed) [])
      (independentHelper d name) (.cons firstBase (.cons firstPoint (.cons secondBase
        (.cons secondPoint (.cons firstWitness (.cons secondWitness .nil)))))) =
      .done (.cons true .nil) ↔
      firstPoint = firstWitness • firstBase ∧ secondPoint = secondWitness • secondBase := by
  rw [ReferenceLaw.invoke (helper := independentHelper d name) (independentLaw (ringModel F G) d)
    definitions linked associated _ trivial]
  change ((PIR.Process.done (.cons
    (decide (firstPoint = firstWitness • firstBase) && decide (secondPoint = secondWitness • secondBase)) .nil) :
    Closed (Values (ringModel F G).Value [.boolean])) = .done (.cons true .nil)) ↔ _
  simp

/-- The shared relation reads one witness at both bases. -/
theorem shared_accepts_iff (d : Domains) (name : String)
    (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
    (associated : BodyIn definitions (sharedHelper d name) (sharedRelationBody d))
    (firstBase firstPoint secondBase secondPoint : G) (witness : F) :
    invoke (definitions.foldl (Evaluation.extendMeaningsOn (ringModel F G) SiteObservations.closed) [])
      (sharedHelper d name) (.cons firstBase (.cons firstPoint (.cons secondBase
        (.cons secondPoint (.cons witness .nil))))) = .done (.cons true .nil) ↔
      firstPoint = witness • firstBase ∧ secondPoint = witness • secondBase := by
  rw [ReferenceLaw.invoke (helper := sharedHelper d name) (sharedLaw (ringModel F G) d)
    definitions linked associated _ trivial]
  change ((PIR.Process.done (.cons
    (decide (firstPoint = witness • firstBase) && decide (secondPoint = witness • secondBase)) .nil) :
    Closed (Values (ringModel F G).Value [.boolean])) = .done (.cons true .nil)) ↔ _
  simp

/-- An actual installed relation and equation helper share the same fixed
nominal domains. Honest acceptance holds for every nonce and challenge, with
no source-name dispatch and no reinterpretation of a same-signature helper. -/
theorem installed_equation_accepts (d : Domains) (relationName equationName : String)
    (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
    (relationAssociated : BodyIn definitions (relationHelper d relationName) (relationBody d))
    (equationAssociated : BodyIn definitions (equationHelper d equationName) (equationBody d))
    (base point : G) (witness nonce challenge : F)
    (related : invoke (definitions.foldl
      (Evaluation.extendMeaningsOn (ringModel F G) SiteObservations.closed) [])
      (relationHelper d relationName) (.cons base (.cons point (.cons witness .nil))) =
      .done (.cons true .nil)) :
    invoke (definitions.foldl (Evaluation.extendMeaningsOn (ringModel F G) SiteObservations.closed) [])
      (equationHelper d equationName) (.cons base (.cons point (.cons (nonce • base)
        (.cons challenge (.cons (nonce + challenge * witness) .nil))))) = .done (.cons true .nil) := by
  rw [ReferenceLaw.invoke (helper := equationHelper d equationName) (equationLaw (ringModel F G) d)
    definitions linked equationAssociated _ trivial]
  rw [equation_accepts d base point witness nonce challenge
    ((relation_accepts_iff d relationName definitions linked relationAssociated base point witness).mp related)]
  rfl

end SourceHelpers
end ZkcSecurity.Bindings.Sigma.SourceExecution
