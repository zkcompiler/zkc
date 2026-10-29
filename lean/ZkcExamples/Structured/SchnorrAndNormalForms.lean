module

public import ZkcExamples.Structured.SchnorrAndViews
public import ZkcExamples.Structured.Generated.Scalar.SchnorrAnd
public import Zkc.Source.Structured.ReplyScript
public import Zkc.Source.Structured.ContractExecution
public import Zkc.Source.Structured.ContractElaboration
public import Zkc.Source.Structured.ContractObligations
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Module.Defs

@[expose] public section

/-! Mathematical transcript and contract consumers of the scope-derived source
presentation. Expected replies and algebraic relations are authored properties;
participant traversal and optional input/output masks belong to the generated
source view. -/
namespace ZkcExamples.Structured.SchnorrAndNormalForms
open Zkc.Source Zkc.Source.Structured SchnorrAndViews

set_option smartUnfolding false
/-! Action sites of the root, named from their source labels. -/
def firstNonceSite : String := "s0"
def secondNonceSite : String := "s2"
def firstCommitmentSite : String := "label_66697273745f636f6d6d69746d656e74_0"
def secondCommitmentSite : String := "label_7365636f6e645f636f6d6d69746d656e74_0"
def challengeSite : String := "label_6368616c6c656e6765"
def deliverySite : String := "label_64656c6976657279_0"
def firstResponseSite : String := "label_66697273745f726573706f6e7365_0"
def secondResponseSite : String := "label_7365636f6e645f726573706f6e7365_0"

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The prover's own inputs, in port order; the others are absent. -/
def proverInputs (firstBase firstKey secondBase secondKey : G) (firstWitness secondWitness : F) (nonces : Nat) :
    Values (Component (assignment F G)) program.payload.entry.inputs :=
  .cons (some firstBase) (.cons (some firstKey) (.cons (some secondBase) (.cons (some secondKey) (.cons (some firstWitness) (.cons (some secondWitness) (.cons (some nonces) (.cons none .nil)))))))

/-- The replies of one prover run: received values by type and site, and
drawn values by site. Other requests are refused. -/
def proverReplies (firstNonce secondNonce delivery : F) : ReplyScript F G where
  receive
    | .field _, site => if site = deliverySite then some delivery else none
    | _, _ => none
  draw site := if site = firstNonceSite then some firstNonce else if site = secondNonceSite then some secondNonce else none

/-- The prover's run on those replies: its outcome and its ordered actions. -/
theorem prover_run (firstBase firstKey secondBase secondKey : G) (firstWitness secondWitness : F) (nonces : Nat) (firstNonce secondNonce delivery : F) :
    (proverReplies firstNonce secondNonce delivery).run (program.participant F G 0 (proverInputs firstBase firstKey secondBase secondKey firstWitness secondWitness nonces)) =
      ⟨.returned (.cons none .nil), (),
        [.query firstNonceSite scalarDomain (.cons nonces .nil),
         .query secondNonceSite scalarDomain (.cons nonces .nil),
         .send (ty := .group groupDomain) firstCommitmentSite 1 (firstNonce • firstBase),
         .send (ty := .group groupDomain) secondCommitmentSite 1 (secondNonce • secondBase),
         .receive (.field scalarDomain) deliverySite 1,
         .send (ty := .field scalarDomain) firstResponseSite 1 (firstNonce + (delivery * firstWitness)),
         .send (ty := .field scalarDomain) secondResponseSite 1 (secondNonce + (delivery * secondWitness))]⟩ := by
  rw [Generated.Scalar.SchnorrAnd.Root.prover_participant]
  kernel_rfl

/-- The verifier's own inputs, in port order; the others are absent. -/
def verifierInputs (firstBase firstKey secondBase secondKey : G) (challenges : Nat) :
    Values (Component (assignment F G)) program.payload.entry.inputs :=
  .cons (some firstBase) (.cons (some firstKey) (.cons (some secondBase) (.cons (some secondKey) (.cons none (.cons none (.cons none (.cons (some challenges) .nil)))))))

/-- The replies of one verifier run: received values by type and site, and
drawn values by site. Other requests are refused. -/
def verifierReplies (firstCommitment secondCommitment : G) (challenge firstResponse secondResponse : F) : ReplyScript F G where
  receive
    | .group _, site => if site = firstCommitmentSite then some firstCommitment else if site = secondCommitmentSite then some secondCommitment else none
    | .field _, site => if site = firstResponseSite then some firstResponse else if site = secondResponseSite then some secondResponse else none
    | _, _ => none
  draw site := if site = challengeSite then some challenge else none

/-- The verifier's run on those replies: its outcome and its ordered actions. -/
theorem verifier_run (firstBase firstKey secondBase secondKey : G) (challenges : Nat) (firstCommitment secondCommitment : G) (challenge firstResponse secondResponse : F) :
    (verifierReplies firstCommitment secondCommitment challenge firstResponse secondResponse).run (program.participant F G 1 (verifierInputs firstBase firstKey secondBase secondKey challenges)) =
      ⟨.returned (.cons (some ((decide (firstResponse • firstBase = firstCommitment + (challenge • firstKey))) && (decide (secondResponse • secondBase = secondCommitment + (challenge • secondKey))))) .nil), (),
        [.receive (.group groupDomain) firstCommitmentSite 0,
         .receive (.group groupDomain) secondCommitmentSite 0,
         .query challengeSite scalarDomain (.cons challenges .nil),
         .send (ty := .field scalarDomain) deliverySite 0 challenge,
         .receive (.field scalarDomain) firstResponseSite 0,
         .receive (.field scalarDomain) secondResponseSite 0]⟩ := by
  rw [Generated.Scalar.SchnorrAnd.Root.verifier_participant]
  kernel_rfl

/-! The selected contract clause: its relation binding, the formula's process and
the decision observed at the deciding role. -/
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

def formulaBinding : FormulaBinding imported application.relation := by bind_contract

theorem no_formula_preconditions : formulaBinding.preconditions = [] := rfl



/-- The relation's arguments, in its declared order. -/
def arguments (firstBase firstKey secondBase secondKey : G) (firstWitness secondWitness : F) :
    Values (assignment F G) formulaBinding.definition.inputs :=
  .cons firstBase (.cons firstKey (.cons secondBase (.cons secondKey (.cons firstWitness (.cons secondWitness .nil)))))

/-- The target holds when the retained formula returns `true`. -/
def Relation (firstBase firstKey secondBase secondKey : G) (firstWitness secondWitness : F) : Prop :=
  formulaBinding.process (arguments firstBase firstKey secondBase secondKey firstWitness secondWitness) =
    .done (.cons true .nil)

theorem formula_process (firstBase firstKey secondBase secondKey : G) (firstWitness secondWitness : F) :
    formulaBinding.process (arguments firstBase firstKey secondBase secondKey firstWitness secondWitness) =
      .done (.cons ((decide (firstKey = firstWitness • firstBase)) && (decide (secondKey = secondWitness • secondBase))) .nil) := by
  rfl

theorem relation_iff (firstBase firstKey secondBase secondKey : G) (firstWitness secondWitness : F) :
    Relation firstBase firstKey secondBase secondKey firstWitness secondWitness ↔ firstKey = firstWitness • firstBase ∧ secondKey = secondWitness • secondBase := by
  unfold Relation
  rw [formula_process]
  change (PIR.Process.done (I := closedInterface) (.cons ((decide (firstKey = firstWitness • firstBase)) && (decide (secondKey = secondWitness • secondBase))) .nil :
    Values (assignment F G) [.boolean]) = .done (.cons true .nil)) ↔ _
  simp
  all_goals change ((decide (firstKey = firstWitness • firstBase)) && (decide (secondKey = secondWitness • secondBase))) = true ↔ firstKey = firstWitness • firstBase ∧ secondKey = secondWitness • secondBase
  all_goals simp

/-- Every retained relation uses its formula or captured body. -/
def environment : RelationEnvironment imported F G :=
  RegisteredRelations.formulaOnly (by decide +kernel)

def target : InterpretedApplication owner clause.subject F G environment where
  binding := application
  interpretation := .formula formulaBinding rfl (fun _ => True)
    (fun args => args.get (.there .here) = args.get (.there (.there (.there (.there .here)))) • args.get .here ∧ args.get (.there (.there (.there .here))) = args.get (.there (.there (.there (.there (.there .here))))) • args.get (.there (.there .here)))
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

/-- Parameter and witness values, keyed by the actual typed selectors. -/
def assignments (firstBase secondBase : G) (firstWitness secondWitness : F) :
    LogicalAssignments (assignment F G) owner rootInvocation where
  parameters type selector := match type with
    | .group _ => if selector.erase = firstBaseSelector.erase then some firstBase else if selector.erase = secondBaseSelector.erase then some secondBase else none
    | _ => none
  witnesses type selector := match type with
    | .field _ => if selector.erase = firstWitnessSelector.erase then some firstWitness else if selector.erase = secondWitnessSelector.erase then some secondWitness else none
    | _ => none

/-- Only the verifier's own inputs and its actual returned tuple are projected. -/
def observedBoundary (firstBase firstKey secondBase secondKey : G) (challenges : Nat) (firstCommitment secondCommitment : G) (challenge firstResponse secondResponse : F) : ContractBoundaryValues owner F G :=
  BoundaryValuation.ofOutcome 1 (verifierInputs firstBase firstKey secondBase secondKey challenges)
    ((verifierReplies firstCommitment secondCommitment challenge firstResponse secondResponse).run
      (program.participant F G 1 (verifierInputs firstBase firstKey secondBase secondKey challenges))).outcome

/-- The selected decision is the verifier's actual returned value. -/
theorem observed_accepts_iff (firstBase firstKey secondBase secondKey : G) (challenges : Nat) (firstCommitment secondCommitment : G) (challenge firstResponse secondResponse : F) :
    decisionSelector.read {} (observedBoundary firstBase firstKey secondBase secondKey challenges firstCommitment secondCommitment challenge firstResponse secondResponse) = some true ↔
      firstResponse • firstBase = firstCommitment + (challenge • firstKey) ∧ secondResponse • secondBase = secondCommitment + (challenge • secondKey) := by
  change (some ((decide (firstResponse • firstBase = firstCommitment + (challenge • firstKey))) && (decide (secondResponse • secondBase = secondCommitment + (challenge • secondKey)))) = some true) ↔ _
  simp

theorem observed_read (firstBase firstKey secondBase secondKey : G) (challenges : Nat) (firstWitness secondWitness : F) (firstCommitment secondCommitment : G) (challenge firstResponse secondResponse : F) :
    application.read {} (observedBoundary firstBase firstKey secondBase secondKey challenges firstCommitment secondCommitment challenge firstResponse secondResponse) (assignments firstBase secondBase firstWitness secondWitness) =
      some (arguments firstBase firstKey secondBase secondKey firstWitness secondWitness) := by
  rfl

theorem observed_target_iff (firstBase firstKey secondBase secondKey : G) (challenges : Nat) (firstWitness secondWitness : F) (firstCommitment secondCommitment : G) (challenge firstResponse secondResponse : F) :
    (target (F := F) (G := G)).Holds {} (observedBoundary firstBase firstKey secondBase secondKey challenges firstCommitment secondCommitment challenge firstResponse secondResponse) (assignments firstBase secondBase firstWitness secondWitness) ↔
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

end ZkcExamples.Structured.SchnorrAndNormalForms
