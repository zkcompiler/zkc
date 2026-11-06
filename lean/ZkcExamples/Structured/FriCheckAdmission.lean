module

public import ZkcExamples.Structured.FriPeeledQuery
public import Zkc.Source.RegionReturnProjection
public import Zkc.Source.Structured.ReceiverMetadata
public meta import Zkc.Source.RegionReturnProjection
public meta import ZkcExamples.Structured.FriCheckPositions
public meta import ZkcTools.StructuredSource.Bindings.CheckedCallback

@[expose] public section

/-! The receiver's admission prefix supplies the operands of the installed
query repeat. The source checks dimensions, sequence lengths, geometry and
coefficient count before making its first cell query. -/
set_option autoImplicit false
namespace ZkcExamples.Structured.FriCheckAdmission
open Zkc.Source Zkc.Source.Structured Bindings
open FriSource FriSourceBodies FriSourceViews FriBinding FriCheckPositions
open OracleProtocol (concrete)
attribute [local implicit_reducible] Op.arguments Op.results Op.regions ProtocolOp.arguments ProtocolOp.results ProtocolOp.regions
variable {model : DomainModel}

checked_repeat_prefix admissionBody := queryOccurrence using queryOnSpine

private def dimensions (model : DomainModel) : ReferenceLaw model helper27Helper.inputs helper27Helper.outputs where
  body := helper27Body
  Requires _ args := args = .cons 3 (.cons 8 .nil)
  reference _ := .returned (.cons true .nil)
  valid _ _ eq := by cases eq; rfl

private def unassociated (model : DomainModel) : ReferenceLaw model helper29Helper.inputs helper29Helper.outputs where
  body := helper29Body
  Requires _ args := args = .cons false (.cons [] (.cons 8 .nil))
  reference _ := .returned (.cons true .nil)
  valid _ _ eq := by cases eq; rfl

private theorem dimensionsStep :
    invoke (unit.oracleCalculations model 1) helper27Helper
      (.cons (concrete model .index 3) (.cons (concrete model .index 8) .nil)) =
      .done (.cons (concrete model .boolean true) .nil) :=
  (dimensions model).invokeOracleConcrete unit 1 rfl FriPairIndex.mathFragment unit.linked
    (by exact_body helper27Definition) (.cons 3 (.cons 8 .nil)) rfl

private theorem associationStep :
    OracleProtocol.owned model 1 1 (FriIndexCollections.helpers model) helper29Helper
      (.cons (concrete model .boolean false) (.cons (concrete model (.vector extension) [])
        (.cons (concrete model .index 8) .nil))) = .done (.cons (concrete model .boolean true) .nil) := by
  change OracleProtocol.owned model 1 1 (FriIndexCollections.helpers model) helper29Helper
    (ProtocolValue.embedComponents (Values.cons (Value := model.Value) (ty := .boolean) false
      (.cons (ty := .vector extension) [] (.cons (ty := .index) 8 .nil))).present) = _
  rw [OracleProtocol.owned_present, (unassociated model).invokeOn (helper := helper29Helper)
    unit.definitions unit.linked (by exact_body helper29Definition) _ rfl]
  rfl

private theorem coefficientLength (cs : List (model.Field extension)) (short : cs.length < indexLimit) :
    OracleProtocol.owned model 1 1 (FriIndexCollections.helpers model) helper0Helper
      (.cons (concrete model (.vector extension) cs) .nil) = .done (.cons (concrete model .index cs.length) .nil) := by
  let law : ReferenceLaw model [.vector extension] [.index] := ReferenceLibrary.marked model "s0" (ReferenceLibrary.execute model (.vectorLength extension) (.cons .here .nil))
  change OracleProtocol.owned model 1 1 (FriIndexCollections.helpers model) helper0Helper
    (ProtocolValue.embedComponents (Values.cons (Value := model.Value) (ty := .vector extension) cs .nil).present) = _
  rw [OracleProtocol.owned_present, law.invokeOn (helper := helper0Helper) unit.definitions unit.linked
    (by exact_body helper0Definition) (.cons cs .nil) trivial]
  change (primitiveOutcome (I := OracleProtocol.Interface model)
    (if cs.length < indexLimit then .returned (Values.cons (Value := model.Value) (ty := .index) cs.length .nil)
      else .stopped .exhausted)).bind _ = _
  rw [ite_eq_left short]
  rfl

private theorem subtractOne (context : ProtocolContext) :
    ((verifierAlgebra model).meaning (verifierTable model) context 1).OperationLaw
      (fun op ↦ .call op .done) (.calculate .indexWrappingSubtract rfl)
      (.cons (concrete model .index 3) (.cons (concrete model .index 1) .nil)) .nil
      (.done (.cons (concrete model .index 2) .nil)) := by
  apply RegionMeaning.OperationLaw.identity
  change ProtocolCalculation.strict model (OracleProtocol.demand model) 1 (FriIndexCollections.helpers model)
    .indexWrappingSubtract (ProtocolValue.embedComponents (.cons (some 3) (.cons (some 1) .nil))) rfl = _
  erw [ProtocolCalculation.strict_embed model (OracleProtocol.demand model) 1 (FriIndexCollections.helpers model)
    .indexWrappingSubtract (.cons (some 3) (.cons (some 1) .nil)) rfl]
  change PIR.Process.done (I := OracleProtocol.Interface model)
    (Values.cons (concrete model .index (wrappingSubtract 3 1)) .nil) = _
  rw [show wrappingSubtract 3 1 = 2 by decide +kernel]

def arguments (handles : FriBindingExecution.Handles) (shift : model.Field extension)
    (cs : List (model.Field extension)) (xs : FriScalarLoop.Positions) :=
  let state := handles.attach (model := model) ⟨none, none, none, concrete model (.field extension) shift,
    concrete model .index 32, concrete model (.vector extension) cs, concrete model .index 3⟩
  FriQueryCall.checkArgs model (FriPhaseCalls.pairs none state.initial none state.layers none state.folds) state xs

def selected (handles : FriBindingExecution.Handles) (shift : model.Field extension)
    (cs : List (model.Field extension)) (xs : FriScalarLoop.Positions) :
    Values (Value model) (.index :: (querySite.spec.state ++ querySite.spec.captures)) :=
  .cons (concrete model .index 8) ((Values.cons (concrete model (.vector extension) []) .nil).append
    (captured (FriPeeledQuery.captures model handles.layers handles.folds [] shift 32
      (concrete model (.vector extension) cs) 2) (xs.map Fin.val) handles.initial))

variable {snapshot : Snapshot} {domains : List DomainSpec} {math : OracleMathEnvironment}
  {S E : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
  (oracles : List (CheckedOracle snapshot domains math))
  (ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E)
  (base : PIR.MonadHandler m (oracleReadInterface model.toCarriers) S E)
  (publish : PIR.MonadHandler m (OraclePublication.Interface model) S E)
  (original : OracleRuntimeState model snapshot domains math S)

private theorem lengthThree {location : OracleLocation} {roles : Nat → Nat} (role : original.self = 1)
    (anchors : List OracleAnchor) (three : anchors.length = 3) :
    ReceiverForwarding.Keeps oracles ordinary base publish original
      (.call (.oracle ⟨.sequenceLength (.table (.field extension) none) 3, location, 1, roles,
        .cons (concrete model layersSort.type anchors) .nil⟩) .done)
      (.cons (concrete model .index 3) .nil) := by
  have read := ReceiverForwarding.sequenceLengthAt (oracles := oracles) (ordinary := ordinary)
    (base := base) (publish := publish) (location := location) (roles := roles)
    (kind := .table (.field extension) none) role three.le (by decide : 3 < indexLimit)
  simpa only [three] using read

private theorem rows32 {location : OracleLocation} {roles : Nat → Nat} (role : original.self = 1)
    (anchor : OracleAnchor) (table : OracleStoredTable model snapshot domains math (.field extension))
    (lookup : OracleStore.find original.entries (.field extension) anchor = some table)
    (visible : OracleStore.visible original.self table.holder table.receivers = true) (size : table.rows = 32) :
    ReceiverForwarding.Keeps oracles ordinary base publish original
      (.call (.oracle ⟨.shape (.table (.field extension) none) "rows", location, 1, roles,
        .cons (concrete model initialSort.type anchor) .nil⟩) .done)
      (.cons (concrete model .index 32) .nil) := by
  have valid : OracleStore.validRows (.table (.field extension) none) table.rows = true := size ▸ (by decide)
  exact size ▸ ReceiverForwarding.rowsAt role lookup valid visible

set_option maxHeartbeats 2400000 in
theorem installed (context : ProtocolContext) (receiver : context.roles 1 = 1) (separate : 1 ≠ context.roles 0)
    (role : original.self = 1) (handles : FriBindingExecution.Handles) (shift : model.Field extension)
    (cs : List (model.Field extension)) (xs : FriScalarLoop.Positions) (eight : xs.length = 8)
    (layers : handles.layers.length = 3) (folds : handles.folds.length = 3) (one : cs.length = 1)
    (table : OracleStoredTable model snapshot domains math (.field extension))
    (lookup : OracleStore.find original.entries (.field extension) handles.initial = some table)
    (visible : OracleStore.visible original.self table.holder table.receivers = true) (size : table.rows = 32) :
    Region.ReturnsProjection (OraclePublication.actionM model oracles ordinary base publish)
      (fun state ↦ state.oracle = original) ((verifierAlgebra model).meaning (verifierTable model) context 1)
      admissionBody (arguments handles shift cs xs).get (fun live ↦ Operands.eval live.get querySite.operands)
      (selected handles shift cs xs) := by
  have short : cs.length < indexLimit := one ▸ (by decide)
  have coeff : OracleProtocol.owned model 1 (context.roles 1) (FriIndexCollections.helpers model) helper0Helper
      (.cons (concrete model (.vector extension) cs) .nil) = .done (.cons (concrete model .index 1) .nil) := by
    rw [receiver]
    simpa only [one] using coefficientLength cs short
  have disabled : OracleProtocol.owned model 1 (context.roles 1) (FriIndexCollections.helpers model) helper29Helper
      (.cons (concrete model .boolean false) (.cons (concrete model (.vector extension) [])
        (.cons (concrete model .index 8) .nil))) = .done (.cons (concrete model .boolean true) .nil) := by
    rw [receiver]; exact associationStep
  repeat' first
    | (project_step ProtocolOp.mark
       apply PIR.Process.ReturnsUnder.call
       exact ReceiverForwarding.mark oracles ordinary base publish original _ _
       apply PIR.Process.ReturnsUnder.done)
    | (project_step ProtocolOp.oracle [OracleOp.input]
       with_unfolding_all apply ReceiverForwarding.inputAt role <;> first | exact separate | simp [receiver])
    | (project_step ProtocolOp.oracle [OracleOp.sequenceLength]
       apply lengthThree oracles ordinary base publish original role _
       first | exact layers | exact folds)
    | (project_step ProtocolOp.oracle [OracleOp.shape]
       exact rows32 oracles ordinary base publish original role handles.initial table lookup visible size)
    | (project_step ProtocolOp.guard
       apply Region.returnsOfLaw; apply OracleProtocol.guardTrue model)
    | (project_step ProtocolOp.localCall
       first
       | exact PIR.Process.ReturnsUnder.ofEquation coeff (.done _)
       | exact PIR.Process.ReturnsUnder.ofEquation disabled (.done _)
       | (apply Region.returnsOfLaw
          first | apply lengthStep model context receiver xs eight | apply FriQueryCall.emptyStep model context receiver))
    | (project_step ProtocolOp.calculate [Op.invoke]
       first
       | exact PIR.Process.ReturnsUnder.ofEquation dimensionsStep (.done _)
       | exact PIR.Process.ReturnsUnder.ofEquation (FriPeeledQuery.sizeProjection shift 32) (.done _))
    | (project_step ProtocolOp.calculate [Op.indexEqual]
       apply Region.returnsOfLaw; exact OracleProtocol.equalIndex model _)
    | (project_step ProtocolOp.calculate [Op.indexWrappingSubtract]
       apply Region.returnsOfLaw
       exact subtractOne context)
    | (project_step ProtocolOp.calculate [Op.indexConstant]
       apply PIR.Process.ReturnsUnder.done)
  apply Region.ReturnsProjection.ret

end ZkcExamples.Structured.FriCheckAdmission
