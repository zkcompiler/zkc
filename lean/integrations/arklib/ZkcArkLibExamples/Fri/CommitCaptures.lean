module

public import ZkcArkLibExamples.Fri.BinaryDomain
public import ZkcArkLibExamples.Fri.CommitGeometry
public import ZkcArkLibExamples.Fri.CommitVirtual
public import Zkc.Source.RegionReturnProjection
public import Zkc.Source.Structured.ReceiverMetadata
public meta import Zkc.Source.RegionReturnProjection

@[expose] public section

/-! Follow the receiver from field delivery to the operands of virtual
construction. Shape is read from the published anchor and every scalar
comes from the original source environment or a linked, checked operation. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.CommitCaptures
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open FriSource FriSourceViews FriSourceBodies
open ZkcSecurity.Domains.KoalaBear (Octic)
open ZkcSecurity.Domains.KoalaBearModel (model)
open OracleProtocol (concrete)
attribute [local implicit_reducible] Op.arguments Op.results Op.regions ProtocolOp.arguments ProtocolOp.results ProtocolOp.regions

noncomputable def roundState (n : Nat) (shift : Octic) (layers folds : List OracleAnchor) (service : Nat) :
    FriCommitRound.State model :=
  ⟨layers, folds, 2 ^ (n + 1), shift, RetainedDomain.root (n + 1), ((2 : Octic)⁻¹ : Octic), service⟩

private theorem atReceiver (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (helper : Helper) (args : Values model.Value helper.inputs) (out : Values model.Value helper.outputs)
    (computes : invoke (RetainedFold.helpers (I := OracleProtocol.Interface model)).closed helper args = .done out) :
    OracleProtocol.owned model 1 (context.roles 1) RetainedFold.helpers helper
      (ProtocolValue.embedComponents args.present) = .done (ProtocolValue.embedComponents out.present) := by
  rw [receiver, OracleProtocol.owned_present, computes]
  rfl

private theorem restrictToHolder (context : ProtocolContext) (separate : context.roles 0 ≠ 1)
    (v : Component (ProtocolValue model.toCarriers) (.field extension)) :
    ((verifierAlgebra model).meaning (verifierTable model) context 1).operation
      (.restrict (.field extension) [0]) (.cons v .nil) .nil = .done (.cons none .nil) := by
  change PIR.Process.done (I := OracleProtocol.Interface model)
    (Values.cons (Value := Component (ProtocolValue model.toCarriers)) (ty := Ty.field extension) (Participant.restrict ([context.roles 0].contains 1) v) .nil) = _
  simp [Participant.restrict, Ne.symm separate]

private theorem assembled (context : ProtocolContext) (receiver : context.roles 1 = 1) (separate : context.roles 0 ≠ 1)
    (x y : Component (ProtocolValue model.toCarriers) (.field extension)) :
    ((verifierAlgebra model).meaning (verifierTable model) context 1).operation
      (.assemble (.field extension) [0,1]) (.cons x (.cons y .nil)) .nil = .done (.cons y .nil) := by
  change PIR.Process.done (I := OracleProtocol.Interface model) (Values.cons (Value := Component (ProtocolValue model.toCarriers)) (ty := Ty.field extension)
    (assembleComponent (fun r ↦ context.roles r == 1) none [0,1] (.cons x (.cons y .nil))) .nil) = _
  simp [assembleComponent, receiver, separate]

private theorem halfRows (n : Nat) (bound : n + 1 ≤ 5) :
    ProtocolCalculation.strict model (OracleProtocol.demand model) 1 RetainedFold.helpers .indexLogicalShiftRight
      (.cons (concrete model .index (2 ^ (n + 1))) (.cons (concrete model .index 1) .nil)) rfl =
      .done (.cons (concrete model .index (2 ^ n)) .nil) := by
  erw [ProtocolCalculation.strict_embed model (OracleProtocol.demand model) 1 RetainedFold.helpers
    .indexLogicalShiftRight (.cons (some (2 ^ (n+1))) (.cons (some 1) .nil)) rfl]
  change PIR.Process.done (I := OracleProtocol.Interface model)
    (Values.cons (concrete model .index (logicalShiftRight (2 ^ (n + 1)) 1)) .nil) = _
  rw [BinaryDomain.halfSize n bound]

private theorem missingRoot (x : Octic) :
    ProtocolCalculation.strict model (OracleProtocol.demand model) 1 RetainedFold.helpers (.fieldEqual extension)
      (.cons none (.cons (concrete model (.field extension) x) .nil)) rfl =
      .done (.cons none .nil) := rfl

private theorem rootEqual (x : Octic) :
    ProtocolCalculation.strict model (OracleProtocol.demand model) 1 RetainedFold.helpers (.fieldEqual extension)
      (.cons (concrete model (.field extension) x) (.cons (concrete model (.field extension) x) .nil)) rfl =
      .done (.cons (concrete model .boolean true) .nil) := by
  erw [ProtocolCalculation.strict_embed model (OracleProtocol.demand model) 1 RetainedFold.helpers
    (.fieldEqual extension) (.cons (some x) (.cons (some x) .nil)) rfl]
  change PIR.Process.done (I := OracleProtocol.Interface model)
    (Values.cons (concrete model .boolean (decide (x = x))) .nil) = _
  simp only [decide_true]

variable {M : Type → Type} [Monad M] [LawfulMonad M] {Aux E : Type}
  (network : PublishedWords.Table model → PIR.MonadHandler M (participantInterfaceOn model.toCarriers) Aux E)
  (choose : PublishedWords.Chooser M model Aux E)

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2400000 in
theorem installed (context : ProtocolContext) (receiver : context.roles 1 = 1) (separate : 1 ≠ context.roles 0)
    (step n : Nat) (bound : n + 1 ≤ 5) (shift beta : Octic) (nonzero : shift ≠ 0)
    (layers folds : List OracleAnchor) (service : Nat) (source : OracleAnchor) (word : Fin (2 ^ (n + 1)) → Octic)
    (original : OracleRuntimeState model checkedUnit.snapshot checkedUnit.domains checkedUnit.math (PublishedWords.State model Aux))
    (role : original.self = 1)
    (live : PublishedWords.RegisteredWord (row := .field extension) original.entries original.self source word original.provider) :
    Region.ReturnsProjection (PublishedWords.actionM checkedUnit.oracles network choose)
      (fun state ↦ state.oracle = original) ((verifierAlgebra model).meaning (verifierTable model) context 1)
      FriCommitRound.prepareView (FriCommitRound.deliveredValues step (roundState n shift layers folds service) source beta).get
      (fun liveValues ↦ FriCommitRound.virtualConstruction.arguments.eval liveValues.get)
      (ProtocolValue.embedComponents (CommitVirtual.foldCaptures n source beta shift).present) := by
  have valid : OracleStore.validRows (.table (.field extension) none) live.registry.rows = true := by
    have fits : live.stored.rows < indexLimit := of_decide_eq_true (Bool.and_eq_true_iff.mp live.shape).1
    simp [OracleStore.validRows, OracleKind.rows, live.registryRows, ← live.rows, fits]
  have rootNonzero := (RetainedDomain.order (n+1) (by omega)).ne_zero (by positivity)
  have challenge := atReceiver context receiver helper6Helper (.cons beta .nil) _ (CommitGeometry.challenge beta)
  have root := atReceiver context receiver helper3Helper (.cons (2 ^ (n+1)) .nil) _ (CommitGeometry.generator (n+1) bound)
  have shiftInv := atReceiver context receiver helper4Helper (.cons shift .nil) _ (CommitGeometry.inverse shift nonzero)
  have rootInv := atReceiver context receiver helper4Helper (.cons (RetainedDomain.root (n+1)) .nil) _
    (CommitGeometry.inverse _ rootNonzero)
  repeat' first
    | (project_step ProtocolOp.mark
       apply PIR.Process.ReturnsUnder.call
       exact ReceiverForwarding.mark checkedUnit.oracles (PublishedWords.liftM network) PublishedWords.readM
         (PublishedWords.publishM choose) original _ _
       apply PIR.Process.ReturnsUnder.done)
    | (project_step ProtocolOp.restrict
       exact PIR.Process.ReturnsUnder.ofEquation (restrictToHolder context separate.symm _) (.done _))
    | (project_step ProtocolOp.assemble
       exact PIR.Process.ReturnsUnder.ofEquation (assembled context receiver separate.symm _ _) (.done _))
    | (project_step ProtocolOp.localCall
       first
       | (apply Region.returnsOfLaw; apply OracleProtocol.localCallInactive model _ _ separate.symm)
       | exact PIR.Process.ReturnsUnder.ofEquation challenge (.done _)
       | exact PIR.Process.ReturnsUnder.ofEquation root (.done _)
       | exact PIR.Process.ReturnsUnder.ofEquation shiftInv (.done _)
       | exact PIR.Process.ReturnsUnder.ofEquation rootInv (.done _))
    | (project_step ProtocolOp.oracle [OracleOp.shape]
       exact live.registryRows ▸ ReceiverForwarding.rowsAt role live.lookup valid live.visible)
    | (project_step ProtocolOp.guard
       apply Region.returnsOfLaw
       first | apply OracleProtocol.guardInactive model separate.symm | apply OracleProtocol.guardTrue model)
    | (project_step ProtocolOp.calculate [Op.indexEqual]
       apply Region.returnsOfLaw; exact OracleProtocol.equalIndex model _)
    | (project_step ProtocolOp.calculate [Op.indexConstant]
       apply PIR.Process.ReturnsUnder.done)
    | (project_step ProtocolOp.calculate [Op.indexLogicalShiftRight]
       exact PIR.Process.ReturnsUnder.ofEquation (halfRows n bound) (.done _))
    | (project_step ProtocolOp.calculate [Op.fieldEqual]
       dsimp only [Operands.eval, Values.get, Values.append, Values.present, Values.absent,
         roundState, FriCommitRound.deliveredValues, FriCommitRound.arguments, ProtocolValue.embedComponents,
         Op.results, Op.arguments, Option.map, ProtocolOp.results, protocolDialect, dialect, extension]
       apply PIR.Process.ReturnsUnder.ofEquation
       first | exact missingRoot (RetainedDomain.root (n+1)) | exact rootEqual (RetainedDomain.root (n+1))
       apply PIR.Process.ReturnsUnder.done)
    | (project_step ProtocolOp.calculate [Op.invoke]
       apply PIR.Process.ReturnsUnder.ofEquation
       exact BinaryDomain.installed n bound shift nonzero
       apply PIR.Process.ReturnsUnder.done)
  apply Region.ReturnsProjection.ret

open FriCommitRound (virtualConstruction)
private abbrev meaning (context : ProtocolContext) := (verifierAlgebra model).meaning (verifierTable model) context 1

set_option maxRecDepth 6000 in
private theorem operationAt (context : ProtocolContext) (values : Values (FriBinding.Value model) virtualConstruction.context) :
    (meaning context).operation virtualConstruction.op (virtualConstruction.arguments.eval values.get) (virtualConstruction.callbacks.denote (meaning context)) =
      .call (.oracle ⟨.virtual oracle0Signature 0 [1], CommitVirtual.constructionSite, 1, context.roles,
        virtualConstruction.arguments.eval values.get⟩) .done := by kernel_rfl

abbrev ReachedView := Values (FriBinding.Value model) virtualConstruction.context ×
  Values (FriBinding.Value model) (protocolDialect.results virtualConstruction.op)

abbrev ConstructionRecord (Aux E : Type) := PIR.Execution
  (OracleProtocol.State model checkedUnit.snapshot checkedUnit.domains checkedUnit.math (PublishedWords.State model Aux))
  (OracleProtocol.Event E) ReachedView

set_option maxRecDepth 6000 in
def RegisteredAt (n : Nat) (source : OracleAnchor) (word : Fin (2 ^ (n+1)) → Octic) (beta shift : Octic)
    (outcome : PIR.Outcome ReachedView)
    (store : OracleRuntimeState model checkedUnit.snapshot checkedUnit.domains checkedUnit.math (PublishedWords.State model Aux)) : Prop :=
  ∀ out, outcome = .returned out →
    ∃ anchor, out.2 = .cons (concrete model (.oracle VirtualReads.kind) anchor) .nil ∧
      Nonempty (VirtualStore.Registered store source anchor word beta shift) ∧
      Nonempty (PublishedWords.RegisteredWord (row := .field extension) store.entries store.self source word store.provider)

def RegisteredConstruction (n : Nat) (source : OracleAnchor) (word : Fin (2 ^ (n+1)) → Octic) (beta shift : Octic)
    (record : ConstructionRecord Aux E) := RegisteredAt n source word beta shift record.outcome record.state.oracle

set_option maxRecDepth 6000 in
/-- On the actual continuation of challenge delivery a returned construction
fixes both handles. The view keeps the delivered challenge and the complete
word at the previously returned parent anchor. A stopped prefix cannot
produce a witness. The enclosing continuation is recovered by
`Region.OperationCut.resume` on the same live tuple. -/
theorem registeredAfterDelivery (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (separate : 1 ≠ context.roles 0) (step n : Nat) (bound : n+1 ≤ 5) (shift beta : Octic) (nonzero : shift ≠ 0)
    (layers folds : List OracleAnchor) (service : Nat) (source : OracleAnchor) (word : Fin (2 ^ (n+1)) → Octic)
    (before : OracleProtocol.State model checkedUnit.snapshot checkedUnit.domains checkedUnit.math (PublishedWords.State model Aux))
    (role : before.oracle.self = 1)
    (parent : PublishedWords.RegisteredWord (row := .field extension) before.oracle.entries before.oracle.self source word before.oracle.provider) :
    let inputs := FriCommitRound.deliveredValues step (roundState n shift layers folds service) source beta
    Std.Do.Internal.Ensures (RegisteredConstruction n source word beta shift)
      ((virtualConstruction.reached ((verifierAlgebra model).meaning (verifierTable model) context 1) inputs.get).runM (PublishedWords.actionM checkedUnit.oracles network choose) before) := by
  dsimp only
  let actions := PublishedWords.actionM checkedUnit.oracles network choose
  have admission := installed network choose context receiver separate step n bound shift beta nonzero layers folds service
    source word before.oracle role parent before rfl
  rw [Region.OperationCut.reached, FriCommitRound.prepareView_exact, PIR.runM_bind]
  apply admission.bind
  rintro ⟨out, current, events⟩ ⟨same, projects⟩
  cases out with
  | stopped why => exact Zkc.MonadicPostcondition.pure _ _ (by intro _ eq; cases eq)
  | returned live =>
    change Values (FriBinding.Value model) virtualConstruction.context at live
    have operands := projects live rfl
    have registers := CommitVirtual.sourceRegisters network choose context receiver n source word beta shift current
      (same ▸ role) (same ▸ parent)
    simp only [PIR.Execution.followM]
    refine Zkc.MonadicPostcondition.map (pre := RegisteredConstruction n source word beta shift)
      (post := RegisteredConstruction n source word beta shift) ?_
      (fun r : ConstructionRecord Aux E ↦ {r with events := events ++ r.events}) (fun _ post ↦ post)
    have selected := (operationAt context live).trans (congrArg
      (fun args : Values (FriBinding.Value model) oracle0Signature.inputs.dropLast ↦
        PIR.Process.call (I := OracleProtocol.Interface model) (A := Values (FriBinding.Value model) [.oracle VirtualReads.kind])
          (.oracle ⟨.virtual oracle0Signature 0 [1], CommitVirtual.constructionSite, 1, context.roles, args⟩) PIR.Process.done)
      operands)
    refine (congrArg (fun act : PIR.Process (OracleProtocol.Interface model)
        (Values (FriBinding.Value model) (protocolDialect.results virtualConstruction.op)) ↦
        Std.Do.Internal.Ensures (RegisteredConstruction n source word beta shift)
          ((act.bind fun reply ↦ .done (live, reply)).runM actions current)) selected).mpr ?_
    change Std.Do.Internal.Ensures _ (actions (CommitVirtual.request context n source beta shift) current >>= _)
    apply registers.bind
    rintro ⟨result, after, trace⟩ known
    cases result with
    | stopped why => exact Zkc.MonadicPostcondition.pure _ _ (by intro _ eq; cases eq)
    | returned reply =>
      have facts := known reply rfl
      simp only [PIR.Execution.followM, PIR.Process.bind, PIR.Process.runM, pure_bind, List.append_nil]
      apply Zkc.MonadicPostcondition.pure
      intro pair equal
      obtain rfl := PIR.Outcome.returned.inj equal
      exact ⟨_, facts⟩

end ZkcSecurity.ArkLib.Fri.CommitCaptures
