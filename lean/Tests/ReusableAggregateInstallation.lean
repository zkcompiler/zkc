import Zkc.Protocols.TableMembership.BatchProtocolInstallation
import ZkcExamples.Structured.TableMembershipLaws
import ZkcExamples.Construction.BatchOpeningConnection
import Zkc.Source.Structured.BodyBindings
import Zkc.Source.Structured.Template
import ZkcTools.StructuredSource.PropertyInstallation
import ZkcTools.StructuredSource.ReferenceLaws
import ZkcTools.Companions

/-! Reuse controls on two actual admitted sources with different call structure:
an eager nested membership scan and a transmitted point/value record batch.
No new interpreter, normal-form expansion, or positional helper installer is
introduced here. Ordinary batch records carry no PCS security assertion. -/
set_option autoImplicit false
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
namespace Tests.ReusableAggregateInstallation
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured ZkcExamples.Construction
open Zkc.Protocols.TableMembership

/-- Actual protocol association keeps the complete roster, scopes and body. -/
def membershipSource : Template.Association TableMembershipViews.unit
    TableMembershipBodies.runSignature TableMembershipBodies.runBody :=
  ⟨TableMembershipViews.runDefinition, TableMembershipViews.run_member, rfl, rfl⟩

variable (model : DomainModel)

/-- Source installation covers arbitrary hidden inputs and an arbitrary
injective role substitution; no mathematics is run by the other participant. -/
theorem hidden_membership_source (ctx : ProtocolContext)
    (distinct : NormalForm.RosterDistinct ctx 0 2)
    (table : Option (List (model.Field "koala-bear")))
    (queries : Option (List (Source.QueryValue (model.Field "koala-bear")))) :
    invokeProtocol (Occurrence.table model TableMembershipViews.unit)
      TableMembershipBodies.runSignature ctx (ctx.roles 0) (.cons table (.cons queries .nil)) =
      .done (.cons none .nil) := by
  have body : TableMembershipBodies.runBody.denote
      (participantMeaningWithOn model (.silent _) Occurrence.actions
        (Occurrence.helpers model TableMembershipViews.unit) (ctx.roles 0)
        (Occurrence.table model TableMembershipViews.unit) ctx Occurrence.iterations)
      (Values.cons none (.cons none .nil)).get = .done (.cons none .nil) := by
    simp only [TableMembershipBodies.runBody, Region.denote, participantMeaningWithOn,
      protocolOperationWithOn, Operands.eval, Values.get, Regions.denote,
      SiteObservations.silent, PIR.Process.bind, Environment.prepend]
    rw [Participant.owned_other _ _ (distinct 1 (by decide +kernel) (by decide +kernel))]
    rfl
  exact membershipSource.invoke 0 ctx distinct
    (.cons .absent (.cons .absent .nil)) rfl .nil
    (.cons table (.cons queries .nil)) (.done (.cons none .nil)) body rfl rfl

/-- The existing helper installer consumes the installed mathematical leaf. -/
theorem actual_contains_decision (found : Bool) (row value : model.Field "koala-bear") :
    Domain.callHelper model TableMembershipViews.program TableMembershipBodies.containsDecisionHelper.name
      [.data .boolean] [.data (.boolean found), .data (.field "koala-bear" row),
        .data (.field "koala-bear" value)] =
      .returned [.data (.boolean (found || decide (row = value)))] := by
  apply_helper_reference Source.containsDecisionLaw model "koala-bear" TableMembershipBodies.names
    using TableMembershipViews.program

theorem actual_opening_decision (valid : Bool)
    (point value expectedPoint expectedValue : model.Field "koala-bear") :
    Domain.callHelper model BatchOpening.program BatchOpeningBodies.checkOpeningHelper.name
      [.data .boolean] [.data (.boolean valid), .data (.field "koala-bear" point),
        .data (.field "koala-bear" value), .data (.field "koala-bear" expectedPoint),
        .data (.field "koala-bear" expectedValue)] =
      .returned [.data (.boolean
        (valid && decide (point = expectedPoint) && decide (value = expectedValue)))] := by
  apply_helper_reference BatchSource.checkOpeningLaw model "koala-bear" ZkcExamples.Structured.BatchOpeningConnection.names
    using BatchOpening.program

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The same source installation covers optional inputs, all role substitutions
and every typed receive answer, retaining both Bool and nominal batch outputs. -/
theorem actual_batch_source (ctx : ProtocolContext)
    (distinct : NormalForm.RosterDistinct ctx 1 2)
    (point value : Option F) (privateBatch : Option (BatchSource.Batch F)) :
    invokeProtocol (Occurrence.table (ringModel F G) BatchOpening.unit)
      BatchOpeningBodies.runSignature ctx (ctx.roles 1)
      (.cons point (.cons value (.cons privateBatch .nil))) =
      BatchSource.validatorReference (G := G) "koala-bear" ZkcExamples.Structured.BatchOpeningConnection.names ZkcExamples.Structured.BatchOpeningConnection.protocolNames
        ctx point value :=
  BatchSource.validator_installed (protocol := ZkcExamples.Structured.BatchOpeningConnection.protocolNames)
    BatchOpening.unit ZkcExamples.Structured.BatchOpeningConnection.installedBodies ZkcExamples.Structured.BatchOpeningConnection.source
    ctx distinct point value privateBatch

/-- Missing validator input does not erase the reached receive event. -/
theorem missing_validator_point (value : F) (privateBatch : Option (BatchSource.Batch F)) :
    invokeProtocol (Occurrence.table (ringModel F G) BatchOpening.unit)
      BatchOpeningBodies.runSignature {} 1
      (.cons none (.cons (some value) (.cons privateBatch .nil))) =
      .call (.action (.receive BatchOpening.batchTy ZkcExamples.Structured.BatchOpeningConnection.protocolNames.messageSite 0))
        (fun _ => .halt .incomplete) :=
  actual_batch_source {} (NormalForm.RosterDistinct.root 1 2) none (some value) privateBatch

/-- The same ReferenceLibrary.forward installation handles both actual formulas. -/
theorem membership_formula (table : List F) (queries : List (Source.QueryValue F)) :
    invoke (closedMeanings (F := F) (G := G) TableMembershipViews.unit.definitions)
      TableMembershipBodies.formulaHelper (.cons table (.cons queries .nil)) =
      primitiveOutcome ((Source.formulaLaw (ringModel F G) "koala-bear"
        TableMembershipBodies.names).reference (.cons table (.cons queries .nil))) :=
  Source.formula_installed TableMembershipViews.unit.linked TableMembershipViews.installedBodies _

theorem batch_formula (point value : F) (batch : BatchSource.Batch F) :
    invoke (closedMeanings (F := F) (G := G) BatchOpening.unit.definitions)
      BatchOpeningBodies.formulaHelper (.cons point (.cons value (.cons batch .nil))) =
      primitiveOutcome ((BatchSource.formulaLaw (ringModel F G) "koala-bear" ZkcExamples.Structured.BatchOpeningConnection.names).reference
        (.cons point (.cons value (.cons batch .nil)))) :=
  BatchSource.formula_installed BatchOpening.unit.linked ZkcExamples.Structured.BatchOpeningConnection.installedBodies _

/-- Empty queries never reach the table scan, even for an oversized table. -/
theorem empty_queries (table : List F) :
    invoke (closedMeanings (F := F) (G := G) TableMembershipViews.unit.definitions)
      TableMembershipBodies.membershipHelper (.cons table (.cons [] .nil)) =
      .done (.cons true .nil) :=
  Source.membership_empty TableMembershipViews.unit.linked TableMembershipViews.installedBodies table

/-- Inactivity is not permission to short-circuit a reached table scan. -/
theorem inactive_query_exhausts (table : List F) (value : F)
    (unbounded : ¬table.length < indexLimit) :
    invoke (closedMeanings (F := F) (G := G) TableMembershipViews.unit.definitions)
      TableMembershipBodies.membershipHelper
      (.cons table (.cons [(false, value, ())] .nil)) = .halt .exhausted :=
  Source.membership_table_exhausted TableMembershipViews.unit.linked
    TableMembershipViews.installedBodies table (false, value, ()) [] (show 1 < indexLimit from by decide +kernel) unbounded

theorem false_accumulator_exhausts (table : List F) (value : F)
    (unbounded : ¬table.length < indexLimit) :
    invoke (closedMeanings (F := F) (G := G) TableMembershipViews.unit.definitions)
      TableMembershipBodies.queryDecisionHelper
      (.cons false (.cons false (.cons value (.cons table .nil)))) = .halt .exhausted :=
  Source.queryDecision_exhausted TableMembershipViews.unit.linked
    TableMembershipViews.installedBodies table false false value unbounded

/-- The optional-input interpreter uses the actual checked helper closure. -/
abbrev batchTables : Evaluation.ComponentTables F G closedInterface :=
  BatchOpening.unit.definitions.foldl (Evaluation.ComponentTables.extend SiteObservations.closed) ⟨[], []⟩

theorem absent_batch (point value : F) :
    Evaluation.componentOperation SiteObservations.closed (batchTables (F := F) (G := G))
      (.invoke BatchOpeningBodies.checkBatchHelper)
      (.cons (some point) (.cons (some value) (.cons none .nil))) .nil = .done (.cons none .nil) := by
  rw [Evaluation.componentOperation_local _ _ _ rfl]
  rfl

/-- A present empty batch returns true; it is distinct from an absent batch. -/
theorem present_empty_batch (point value : F) :
    Evaluation.componentOperation SiteObservations.closed (batchTables (F := F) (G := G))
      (.invoke BatchOpeningBodies.checkBatchHelper)
      (Values.cons point (.cons value (.cons [] .nil))).present .nil =
      .done (.cons (some true) .nil) := by
  rw [Evaluation.componentOperation_local _ _ _ rfl, strictComponent_adequate]
  rw [Evaluation.ComponentTables.closed_fold]
  change (invoke (closedMeanings (F := F) (G := G) BatchOpening.unit.definitions)
    BatchOpeningBodies.checkBatchHelper (.cons point (.cons value (.cons [] .nil)))).bind _ = _
  have actual := BatchSource.check_equation (F := F) (G := G)
    BatchOpening.unit.linked ZkcExamples.Structured.BatchOpeningConnection.installedBodies point value []
  have bounded : ([] : BatchSource.Batch F).length < indexLimit := by
    change 0 < indexLimit
    decide +kernel
  rw [ite_eq_left bounded] at actual
  exact congrArg (fun process : Closed (Values (assignment F G) [.boolean]) =>
    process.bind fun result => .done result.present) actual

-- Exact source association refuses a changed dependency with the same ABI.
example : True := by
  fail_if_success
    have : Source.Bodies TableMembershipViews.unit.definitions "koala-bear"
        {TableMembershipBodies.names with contains := "substituted_contains"} := by
      bind_structured_bodies
  trivial

-- Nominally distinct records cannot borrow the actual batch body associations.
example : True := by
  fail_if_success
    have : BatchSource.Bodies BatchOpening.unit.definitions "koala-bear"
        {ZkcExamples.Structured.BatchOpeningConnection.names with openingName := "different.Opening"} := by
      bind_structured_bodies
  trivial

/-- The original fixed goal is a complete helper equation on the actual source. -/
def FixedMembershipGoal : Prop :=
  invoke (closedMeanings (F := F) (G := G) TableMembershipViews.unit.definitions)
    TableMembershipBodies.formulaHelper (.cons ([] : List F) (.cons [] .nil)) =
      .done (.cons true .nil)

@[zkc "aggregate.membership.fixed"] theorem fixed_membership (F G : Type)
    [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] :
    FixedMembershipGoal (F := F) (G := G) := by
  unfold FixedMembershipGoal
  rw [TableMembershipLaws.formula_equation]
  rfl

/-- This is a valid theorem about a different reference, not the fixed request. -/
@[zkc "aggregate.membership.substituted"] theorem substituted_reference :
    PIR.Relation.Table.membership ([] : List Int) [⟨true, 7⟩] = false := rfl

example : FixedMembershipGoal (F := F) (G := G) :=
  zkc_companion ["aggregate.membership.fixed"[F, G]]

open Lean Elab Command Term Meta in
run_elab do
  let fixed ← elabTerm (← `(term| FixedMembershipGoal (F := Int) (G := Int))) none
  let refused ← ZkcTools.Companions.resolve
    #[⟨"aggregate.membership.substituted", #[]⟩,
      ⟨"aggregate.membership.fixed", #[← `(term| Int), ← `(term| Int)]⟩] fixed
  unless (match refused with | .refused _ _ => true | _ => false) do
    throwError "a reference substitution changed the fixed aggregate goal or silently fell back"

#print axioms actual_batch_source
#print axioms missing_validator_point
#print axioms hidden_membership_source
#print axioms membership_formula
#print axioms batch_formula
#print axioms absent_batch
#print axioms present_empty_batch
#print axioms fixed_membership
end Tests.ReusableAggregateInstallation
