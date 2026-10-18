module

public import ZkcExamples.Structured.SchnorrAnd
public import Zkc.Source.Structured.ContractExecution
public import Zkc.Source.Structured.ContractElaboration
public import Zkc.Source.Structured.ContractObligations
public import Zkc.Protocols.Schnorr

@[expose] public section

/-! The authored `knowledge` target of `sigma::SchnorrAnd`: the retained
`DLogPair` formula with two witness ports. Each witness is keyed by its own
selector, so two extracted witnesses are independent logical values; nothing
identifies them with each other or with the prover's inputs. -/
namespace ZkcExamples.Structured.SchnorrAndBinding
open Zkc.Source Zkc.Source.Structured SchnorrAndViews SchnorrAnd

set_option smartUnfolding false

def owner : ContractBinding imported := by bind_contract

def clauseIndex : Fin owner.contract.clauses.length := owner.namedClause "knowledge"

def clause : ContractClause := owner.clause clauseIndex

theorem owner_is_entry : owner.protocol = program.payload.entry := rfl

def application : ApplicationBinding owner clause.subject := by bind_contract

def firstBaseSelector : BoundarySelector owner.protocol.signature (.group groupDomain) :=
  application.selectors.get .here

def firstKeySelector : BoundarySelector owner.protocol.signature (.group groupDomain) :=
  application.selectors.get (.there .here)

def secondBaseSelector : BoundarySelector owner.protocol.signature (.group groupDomain) :=
  application.selectors.get (.there (.there .here))

def secondKeySelector : BoundarySelector owner.protocol.signature (.group groupDomain) :=
  application.selectors.get (.there (.there (.there .here)))

def firstWitnessSelector : BoundarySelector owner.protocol.signature (.field scalarDomain) :=
  application.selectors.get (.there (.there (.there (.there .here))))

def secondWitnessSelector : BoundarySelector owner.protocol.signature (.field scalarDomain) :=
  application.selectors.get (.there (.there (.there (.there (.there .here)))))

def decisionSelector : BoundarySelector owner.protocol.signature .boolean :=
  ⟨.output .here, ⟨1, by decide +kernel⟩, by decide +kernel⟩

theorem exact_clause : clause.kind = .target ∧ clause.name = "knowledge" ∧
    clause.residual = none ∧ clause.decision = some decisionSelector.erase := by
  decide +kernel

theorem all_clauses : owner.contract.clauses = [clause] := rfl

/-- The two witness selectors name different prover input ports, so their
logical slots are distinct. -/
theorem witnesses_distinct : firstWitnessSelector.erase ≠ secondWitnessSelector.erase := by
  decide +kernel

def formulaBinding : FormulaBinding imported application.relation := by bind_contract

theorem no_formula_preconditions : formulaBinding.preconditions = [] := rfl

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def arguments (firstBase firstKey secondBase secondKey : G) (firstWitness secondWitness : F) :
    Values (assignment F G) formulaBinding.definition.inputs :=
  .cons firstBase (.cons firstKey (.cons secondBase (.cons secondKey
    (.cons firstWitness (.cons secondWitness .nil)))))

/-- The target denotes the actual retained formula process. -/
def Relation (firstBase firstKey secondBase secondKey : G) (firstWitness secondWitness : F) : Prop :=
  formulaBinding.process (arguments firstBase firstKey secondBase secondKey firstWitness secondWitness) =
    .done (.cons true .nil)

theorem formula_process (firstBase firstKey secondBase secondKey : G) (firstWitness secondWitness : F) :
    formulaBinding.process (arguments firstBase firstKey secondBase secondKey firstWitness secondWitness) =
      .done (.cons (decide (firstKey = firstWitness • firstBase) &&
        decide (secondKey = secondWitness • secondBase)) .nil) := by
  rfl

theorem relation_iff (firstBase firstKey secondBase secondKey : G) (firstWitness secondWitness : F) :
    Relation firstBase firstKey secondBase secondKey firstWitness secondWitness ↔
      firstKey = firstWitness • firstBase ∧ secondKey = secondWitness • secondBase := by
  unfold Relation
  rw [formula_process]
  change (PIR.Proc.done (I := closedInterface)
    (.cons (decide (firstKey = firstWitness • firstBase) &&
      decide (secondKey = secondWitness • secondBase)) .nil : Values (assignment F G) [.boolean]) =
        .done (.cons true .nil)) ↔ _
  simp

/-- The subject's only relation is this formula. -/
def environment : RelationEnvironment imported F G where
  meanings index args := by
    have same : index = application.relation.index := by
      apply Fin.ext
      have bound : index.val < 1 := index.isLt
      change index.val = 0
      omega
    subst index
    exact Relation (args.get .here) (args.get (.there .here)) (args.get (.there (.there .here)))
      (args.get (.there (.there (.there .here)))) (args.get (.there (.there (.there (.there .here)))))
      (args.get (.there (.there (.there (.there (.there .here))))))

def target : InterpretedApplication owner clause.subject F G environment where
  binding := application
  interpretation := .formula formulaBinding rfl (fun _ => True)
    (fun args => args.get (.there .here) =
        args.get (.there (.there (.there (.there .here)))) • args.get .here ∧
      args.get (.there (.there (.there .here))) =
        args.get (.there (.there (.there (.there (.there .here))))) • args.get (.there (.there .here)))
    inferInstance

theorem target_formula_law : (target (F := F) (G := G)).interpretation.FormulaLaw := by
  intro args _
  cases args with | cons firstBase args =>
  cases args with | cons firstKey args =>
  cases args with | cons secondBase args =>
  cases args with | cons secondKey args =>
  cases args with | cons firstWitness args =>
  cases args with | cons secondWitness args =>
  cases args
  simp only [Bool.decide_and]
  rfl

def rootInvocation : InvocationCoordinate := ⟨0, []⟩

/-- Parameter and witness values keyed by the actual typed selectors. -/
def assignments (firstBase secondBase : G) (firstWitness secondWitness : F) :
    LogicalAssignments (assignment F G) owner rootInvocation where
  parameters type selector := match type with
    | .group _ => if selector.erase = firstBaseSelector.erase then some firstBase
        else if selector.erase = secondBaseSelector.erase then some secondBase else none
    | _ => none
  witnesses type selector := match type with
    | .field _ => if selector.erase = firstWitnessSelector.erase then some firstWitness
        else if selector.erase = secondWitnessSelector.erase then some secondWitness else none
    | _ => none

/-- Only the verifier's own inputs and its actual returned tuple are projected.
An adversarial transcript does not imply an honest prover execution. -/
def observedBoundary (firstBase firstKey secondBase secondKey : G) (service : Nat)
    (commitments : G × G) (challenge : F) (responses : F × F) : ContractBoundaryValues owner F G :=
  BoundaryValuation.ofOutcome 1 (verifierInputs firstBase firstKey secondBase secondKey service)
    (execute firstBase firstKey secondBase secondKey service commitments challenge responses).outcome

/-- The selected decision is the actual verifier's: both equations must hold. -/
theorem observed_accepts_iff (firstBase firstKey secondBase secondKey : G) (service : Nat)
    (commitments : G × G) (challenge : F) (responses : F × F) :
    decisionSelector.read {} (observedBoundary firstBase firstKey secondBase secondKey service
        commitments challenge responses) = some true ↔
      responses.1 • firstBase = commitments.1 + challenge • firstKey ∧
        responses.2 • secondBase = commitments.2 + challenge • secondKey := by
  change (some (decide (responses.1 • firstBase = commitments.1 + challenge • firstKey) &&
      decide (responses.2 • secondBase = commitments.2 + challenge • secondKey)) = some true) ↔ _
  simp

theorem observed_read (firstBase firstKey secondBase secondKey : G) (firstWitness secondWitness : F)
    (service : Nat) (commitments : G × G) (challenge : F) (responses : F × F) :
    application.read {} (observedBoundary firstBase firstKey secondBase secondKey service
        commitments challenge responses) (assignments firstBase secondBase firstWitness secondWitness) =
      some (arguments firstBase firstKey secondBase secondKey firstWitness secondWitness) := by
  rfl

theorem observed_target_iff (firstBase firstKey secondBase secondKey : G) (firstWitness secondWitness : F)
    (service : Nat) (commitments : G × G) (challenge : F) (responses : F × F) :
    (target (F := F) (G := G)).Holds {} (observedBoundary firstBase firstKey secondBase secondKey service
        commitments challenge responses) (assignments firstBase secondBase firstWitness secondWitness) ↔
      Relation firstBase firstKey secondBase secondKey firstWitness secondWitness := by
  change (∃ args, application.read {} _ _ = some args ∧
    formulaBinding.invokeRelation args = .done (.cons true .nil)) ↔ _
  constructor
  · rintro ⟨args, read, truth⟩
    rw [observed_read] at read
    cases Option.some.inj read
    exact truth
  · intro truth
    exact ⟨_, observed_read .., truth⟩

/-- Two transcripts with one pair of commitments and distinct challenges, both
accepted by the actual verifier, give a witness pair for the actual target at
the first transcript's returned boundary. The pair is new; it is no prover input. -/
theorem extracted_target (firstBase firstKey secondBase secondKey : G) (service : Nat)
    (commitments : G × G) (first second : F) (firstResponses secondResponses : F × F)
    (distinct : first ≠ second)
    (acceptFirst : decisionSelector.read {} (observedBoundary firstBase firstKey secondBase secondKey
      service commitments first firstResponses) = some true)
    (acceptSecond : decisionSelector.read {} (observedBoundary firstBase firstKey secondBase secondKey
      service commitments second secondResponses) = some true) :
    (target (F := F) (G := G)).Holds {} (observedBoundary firstBase firstKey secondBase secondKey service
        commitments first firstResponses)
      (assignments firstBase secondBase ((firstResponses.1 - secondResponses.1) / (first - second))
        ((firstResponses.2 - secondResponses.2) / (first - second))) := by
  rw [observed_accepts_iff] at acceptFirst acceptSecond
  apply (observed_target_iff ..).mpr
  apply (relation_iff ..).mpr
  exact ⟨(Zkc.Protocols.Schnorr.extract_public_key firstBase firstKey commitments.1 first second
      firstResponses.1 secondResponses.1 distinct acceptFirst.1 acceptSecond.1).symm,
    (Zkc.Protocols.Schnorr.extract_public_key secondBase secondKey commitments.2 first second
      firstResponses.2 secondResponses.2 distinct acceptFirst.2 acceptSecond.2).symm⟩

/-- The values the admitted prover sends (`SchnorrAnd.prover_run`) for given
nonces and a challenge, delivered with that challenge, are accepted by the
actual verifier when both keys use the witnesses at the verifier's bases. This
states the values, not a joint run of the two participants. -/
theorem honest_accepts (firstBase firstKey secondBase secondKey : G) (firstWitness secondWitness : F)
    (firstNonce secondNonce challenge : F) (service : Nat)
    (valid : Relation firstBase firstKey secondBase secondKey firstWitness secondWitness) :
    decisionSelector.read {} (observedBoundary firstBase firstKey secondBase secondKey service
      (firstNonce • firstBase, secondNonce • secondBase) challenge
      (firstNonce + challenge * firstWitness, secondNonce + challenge * secondWitness)) = some true := by
  obtain ⟨firstValid, secondValid⟩ := (relation_iff ..).mp valid
  apply (observed_accepts_iff ..).mpr
  subst firstValid secondValid
  exact ⟨Zkc.Protocols.Schnorr.response_equation .., Zkc.Protocols.Schnorr.response_equation ..⟩

end ZkcExamples.Structured.SchnorrAndBinding
