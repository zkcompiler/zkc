module

public import ZkcExamples.Structured.OkamotoViews
public import ZkcExamples.Structured.Generated.Scalar.Okamoto
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
namespace ZkcExamples.Structured.OkamotoNormalForms
open Zkc.Source Zkc.Source.Structured OkamotoViews

set_option smartUnfolding false
/-! Action sites of the root, named from their source labels. -/
def firstNonceSite : String := "label_66697273745f6e6f6e6365"
def secondNonceSite : String := "label_7365636f6e645f6e6f6e6365"
def commitmentSite : String := "label_636f6d6d69746d656e74_0"
def challengeSite : String := "label_6368616c6c656e6765"
def deliverySite : String := "label_64656c6976657279_0"
def firstResponseSite : String := "label_66697273745f726573706f6e7365_0"
def secondResponseSite : String := "label_7365636f6e645f726573706f6e7365_0"

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The prover's own inputs, in port order; the others are absent. -/
def proverInputs (firstBase secondBase point : G) (firstScalar secondScalar : F) (nonces : Nat) :
    Values (Component (assignment F G)) program.payload.entry.inputs :=
  .cons (some firstBase) (.cons (some secondBase) (.cons (some point) (.cons (some firstScalar) (.cons (some secondScalar) (.cons (some nonces) (.cons none .nil))))))

/-- The replies of one prover run: received values by type and site, and
drawn values by site. Other requests are refused. -/
def proverReplies (firstNonce secondNonce delivery : F) : ReplyScript F G where
  receive
    | .field _, site => if site = deliverySite then some delivery else none
    | _, _ => none
  draw site := if site = firstNonceSite then some firstNonce else if site = secondNonceSite then some secondNonce else none

/-- The prover's run on those replies: its outcome and its ordered actions. -/
theorem prover_run (firstBase secondBase point : G) (firstScalar secondScalar : F) (nonces : Nat) (firstNonce secondNonce delivery : F) :
    (proverReplies firstNonce secondNonce delivery).run (program.participant F G 0 (proverInputs firstBase secondBase point firstScalar secondScalar nonces)) =
      ⟨.returned (.cons none .nil), (),
        [.query firstNonceSite scalarDomain (.cons nonces .nil),
         .query secondNonceSite scalarDomain (.cons nonces .nil),
         .send (ty := .group groupDomain) commitmentSite 1 ((firstNonce • firstBase) + (secondNonce • secondBase)),
         .receive (.field scalarDomain) deliverySite 1,
         .send (ty := .field scalarDomain) firstResponseSite 1 (firstNonce + (delivery * firstScalar)),
         .send (ty := .field scalarDomain) secondResponseSite 1 (secondNonce + (delivery * secondScalar))]⟩ := by
  rw [Generated.Scalar.Okamoto.Root.prover_participant]
  kernel_rfl

/-- The verifier's own inputs, in port order; the others are absent. -/
def verifierInputs (firstBase secondBase point : G) (challenges : Nat) :
    Values (Component (assignment F G)) program.payload.entry.inputs :=
  .cons (some firstBase) (.cons (some secondBase) (.cons (some point) (.cons none (.cons none (.cons none (.cons (some challenges) .nil))))))

/-- The replies of one verifier run: received values by type and site, and
drawn values by site. Other requests are refused. -/
def verifierReplies (commitment : G) (challenge firstResponse secondResponse : F) : ReplyScript F G where
  receive
    | .group _, site => if site = commitmentSite then some commitment else none
    | .field _, site => if site = firstResponseSite then some firstResponse else if site = secondResponseSite then some secondResponse else none
    | _, _ => none
  draw site := if site = challengeSite then some challenge else none

/-- The verifier's run on those replies: its outcome and its ordered actions. -/
theorem verifier_run (firstBase secondBase point : G) (challenges : Nat) (commitment : G) (challenge firstResponse secondResponse : F) :
    (verifierReplies commitment challenge firstResponse secondResponse).run (program.participant F G 1 (verifierInputs firstBase secondBase point challenges)) =
      ⟨.returned (.cons (some (decide ((firstResponse • firstBase) + (secondResponse • secondBase) = commitment + (challenge • point)))) .nil), (),
        [.receive (.group groupDomain) commitmentSite 0,
         .query challengeSite scalarDomain (.cons challenges .nil),
         .send (ty := .field scalarDomain) deliverySite 0 challenge,
         .receive (.field scalarDomain) firstResponseSite 0,
         .receive (.field scalarDomain) secondResponseSite 0]⟩ := by
  rw [Generated.Scalar.Okamoto.Root.verifier_participant]
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

def secondBaseSelector : BoundarySelector owner.protocol.signature (.group groupDomain) :=
  application.selectors.get (.there .here)

def pointSelector : BoundarySelector owner.protocol.signature (.group groupDomain) :=
  application.selectors.get (.there (.there .here))

def firstScalarSelector : BoundarySelector owner.protocol.signature (.field scalarDomain) :=
  application.selectors.get (.there (.there (.there .here)))

def secondScalarSelector : BoundarySelector owner.protocol.signature (.field scalarDomain) :=
  application.selectors.get (.there (.there (.there (.there .here))))

def decisionSelector : BoundarySelector owner.protocol.signature .boolean :=
  ⟨.output .here, ⟨1, by decide +kernel⟩, by decide +kernel⟩

theorem exact_clause : clause.kind = .target ∧ clause.name = "knowledge" ∧
    clause.residual = none ∧ clause.decision = some decisionSelector.erase := by
  decide +kernel

theorem all_clauses : owner.contract.clauses = [clause] := rfl

def formulaBinding : FormulaBinding imported application.relation := by bind_contract

theorem no_formula_preconditions : formulaBinding.preconditions = [] := rfl



/-- The relation's arguments, in its declared order. -/
def arguments (firstBase secondBase point : G) (firstScalar secondScalar : F) :
    Values (assignment F G) formulaBinding.definition.inputs :=
  .cons firstBase (.cons secondBase (.cons point (.cons firstScalar (.cons secondScalar .nil))))

/-- The target holds when the retained formula returns `true`. -/
def Relation (firstBase secondBase point : G) (firstScalar secondScalar : F) : Prop :=
  formulaBinding.process (arguments firstBase secondBase point firstScalar secondScalar) =
    .done (.cons true .nil)

theorem formula_process (firstBase secondBase point : G) (firstScalar secondScalar : F) :
    formulaBinding.process (arguments firstBase secondBase point firstScalar secondScalar) =
      .done (.cons (decide (point = (firstScalar • firstBase) + (secondScalar • secondBase))) .nil) := by
  rfl

theorem relation_iff (firstBase secondBase point : G) (firstScalar secondScalar : F) :
    Relation firstBase secondBase point firstScalar secondScalar ↔ point = (firstScalar • firstBase) + (secondScalar • secondBase) := by
  unfold Relation
  rw [formula_process]
  change (PIR.Process.done (I := closedInterface) (.cons (decide (point = (firstScalar • firstBase) + (secondScalar • secondBase))) .nil :
    Values (assignment F G) [.boolean]) = .done (.cons true .nil)) ↔ _
  simp
  all_goals change (decide (point = (firstScalar • firstBase) + (secondScalar • secondBase))) = true ↔ point = (firstScalar • firstBase) + (secondScalar • secondBase)
  all_goals simp

/-- Every retained relation uses its formula or captured body. -/
def environment : RelationEnvironment imported F G :=
  RegisteredRelations.formulaOnly (by decide +kernel)

def target : InterpretedApplication owner clause.subject F G environment where
  binding := application
  interpretation := .formula formulaBinding rfl (fun _ => True)
    (fun args => args.get (.there (.there .here)) = (args.get (.there (.there (.there .here))) • args.get .here) + (args.get (.there (.there (.there (.there .here)))) • args.get (.there .here)))
    inferInstance

theorem target_formula_law : (target (F := F) (G := G)).interpretation.FormulaLaw := by
  intro args _
  cases args with | cons firstBase args =>
  cases args with | cons secondBase args =>
  cases args with | cons point args =>
  cases args with | cons firstScalar args =>
  cases args with | cons secondScalar args =>
  cases args
  rfl

def rootInvocation : InvocationCoordinate := ⟨0, []⟩

/-- Parameter and witness values, keyed by the actual typed selectors. -/
def assignments (firstBase secondBase : G) (firstScalar secondScalar : F) :
    LogicalAssignments (assignment F G) owner rootInvocation where
  parameters type selector := match type with
    | .group _ => if selector.erase = firstBaseSelector.erase then some firstBase else if selector.erase = secondBaseSelector.erase then some secondBase else none
    | _ => none
  witnesses type selector := match type with
    | .field _ => if selector.erase = firstScalarSelector.erase then some firstScalar else if selector.erase = secondScalarSelector.erase then some secondScalar else none
    | _ => none

/-- Only the verifier's own inputs and its actual returned tuple are projected. -/
def observedBoundary (firstBase secondBase point : G) (challenges : Nat) (commitment : G) (challenge firstResponse secondResponse : F) : ContractBoundaryValues owner F G :=
  BoundaryValuation.ofOutcome 1 (verifierInputs firstBase secondBase point challenges)
    ((verifierReplies commitment challenge firstResponse secondResponse).run
      (program.participant F G 1 (verifierInputs firstBase secondBase point challenges))).outcome

/-- The selected decision is the verifier's actual returned value. -/
theorem observed_accepts_iff (firstBase secondBase point : G) (challenges : Nat) (commitment : G) (challenge firstResponse secondResponse : F) :
    decisionSelector.read {} (observedBoundary firstBase secondBase point challenges commitment challenge firstResponse secondResponse) = some true ↔
      (firstResponse • firstBase) + (secondResponse • secondBase) = commitment + (challenge • point) := by
  change (some (decide ((firstResponse • firstBase) + (secondResponse • secondBase) = commitment + (challenge • point))) = some true) ↔ _
  simp

theorem observed_read (firstBase secondBase point : G) (challenges : Nat) (firstScalar secondScalar : F) (commitment : G) (challenge firstResponse secondResponse : F) :
    application.read {} (observedBoundary firstBase secondBase point challenges commitment challenge firstResponse secondResponse) (assignments firstBase secondBase firstScalar secondScalar) =
      some (arguments firstBase secondBase point firstScalar secondScalar) := by
  rfl

theorem observed_target_iff (firstBase secondBase point : G) (challenges : Nat) (firstScalar secondScalar : F) (commitment : G) (challenge firstResponse secondResponse : F) :
    (target (F := F) (G := G)).Holds {} (observedBoundary firstBase secondBase point challenges commitment challenge firstResponse secondResponse) (assignments firstBase secondBase firstScalar secondScalar) ↔
      Relation firstBase secondBase point firstScalar secondScalar := by
  change (∃ args, application.read {} _ _ = some args ∧
    formulaBinding.invokeRelation args = .done (.cons true .nil)) ↔ _
  constructor
  · rintro ⟨args, read, truth⟩
    rw [observed_read] at read
    cases Option.some.inj read
    exact truth
  · intro truth
    exact ⟨_, observed_read .., truth⟩

end ZkcExamples.Structured.OkamotoNormalForms
