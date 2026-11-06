module

public import ZkcExamples.Structured.FriCheckPositions
public import ZkcExamples.Structured.FriPairIndex

@[expose] public section

/-! The inner verifier callback selects the actual layer by round and reads
its registered value at the carried position before inspecting the fold. -/
set_option autoImplicit false
namespace ZkcExamples.Structured.FriCheckRound
open Zkc.Source Zkc.Source.Structured
open FriSource FriSourceBodies FriSourceViews FriBinding
open Zkc.Source.Structured.Bindings
open OracleProtocol (concrete AtMarkedCall StopsAfterMarks)
attribute [local implicit_reducible] ProtocolOp.arguments ProtocolOp.results ProtocolOp.regions

checked_callback round := protocol3Body at 1 with_continuation

/-- Inside one query iteration the inner repeat is a sequential cut. In the
full Check declaration the same repeat is nested in an outer callback. -/
def insideQuery : RepeatAt roundSite FriCheckPositions.queryBody :=
  selectedRepeat (ordinal := 0) (by kernel_rfl)

theorem innerOnSpine : insideQuery.onSpine = true := by kernel_rfl

theorem queryBody_eq (model : DomainModel) (context : ProtocolContext)
    (env : Environment (Value model) (.index :: (FriCheckPositions.querySite.spec.state ++
      FriCheckPositions.querySite.spec.captures))) :
    let meaning := (verifierAlgebra model).meaning (verifierTable model) context 1
    FriCheckPositions.queryBody.denote meaning env =
      ((insideQuery.beforeRepeat innerOnSpine).denote meaning env).bind fun live ↦
        (roundSite.iterations meaning live.get).bind fun result ↦ roundSite.next.denote meaning (Environment.prepend live.get result) := by
  dsimp only
  refine (insideQuery.denote_prefix ((verifierAlgebra model).meaning (verifierTable model) context 1)
    innerOnSpine env).trans ?_
  rfl

structure State (model : DomainModel) where
  expected : model.Field extension
  position : Nat
  rows : Nat
  shift : model.Field extension

variable {model : DomainModel}

def iteration (context : ProtocolContext) (step : Nat) (state : State model)
    (layers folds : List OracleAnchor) :=
  let args : Values (Value model) (.index :: (roundSite.spec.state ++ roundSite.spec.captures)) :=
    .cons (concrete model .index step) (.cons (concrete model (.field extension) state.expected)
      (.cons (concrete model .index state.position) (.cons (concrete model .index state.rows)
        (.cons (concrete model (.field extension) state.shift) (.cons (concrete model layersSort.type layers)
          (.cons (concrete model layersSort.type folds) .nil))))))
  roundBody.denote ((verifierAlgebra model).meaning (verifierTable model) context 1) args.get

/-- Only registered oracle operations contribute rows. The typed process
equation below checks the selection, each operand, and the continuation. -/
def sites := roundBody.erase.operations.filterMap fun op ↦ match op with
  | .oracle _ site => some site
  | _ => none

def site (i : Fin 6) : OracleLocation :=
  sites[i.val]'(by
    have length : sites.length = 6 := by kernel_rfl
    simpa only [length] using i.isLt)

abbrev kind := OracleKind.table (.field extension) none

def sequenceRequest (context : ProtocolContext) (layers : List OracleAnchor) (index : Nat)
    (location : OracleLocation) : (OracleProtocol.Interface model).Op :=
  .oracle ⟨.sequenceAt kind 3 [0, 1], location, 1, context.roles,
    .cons (concrete model layersSort.type layers) (.cons (concrete model .index index) .nil)⟩

def rowsRequest (context : ProtocolContext) (anchor : OracleAnchor) (location : OracleLocation) :
    (OracleProtocol.Interface model).Op :=
  .oracle ⟨.shape kind "rows", location, 1, context.roles,
    .cons (concrete model initialSort.type anchor) .nil⟩

def nextRows (state : State model) := logicalShiftRight state.rows 1

def low (state : State model) := bitAnd state.position (wrappingSubtract (nextRows state) 1)

def advanced (state : State model) (folded : model.Field extension) :
    Values (Value model) roundSite.spec.state :=
  .cons (concrete model (.field extension) folded) (.cons (concrete model .index (low state))
    (.cons (concrete model .index (nextRows state))
      (.cons (concrete model (.field extension) (state.shift * state.shift)) .nil)))

abbrev Process (model : DomainModel) :=
  PIR.Process (OracleProtocol.Interface model) (Values (Value model) roundSite.spec.state)

/-- Both selections check the registered row count before the cell action. -/
def selectsRows (context : ProtocolContext) (anchors : List OracleAnchor) (index rows : Nat)
    (sequenceSite shapeSite : OracleLocation) (tail : OracleAnchor → Process model → Prop)
    (process : Process model) : Prop :=
  AtMarkedCall (sequenceRequest context anchors index sequenceSite) (fun select ↦
    ∀ anchor, AtMarkedCall (rowsRequest context anchor shapeSite) (fun shape ↦
      tail anchor (shape (.cons (concrete model .index rows) .nil)))
      (select (.cons (concrete model initialSort.type anchor) .nil))) process

def checksFold (context : ProtocolContext) (step : Nat) (state : State model) (folds : List OracleAnchor)
    (process : Process model) : Prop :=
  selectsRows context folds (wrappingAdd step 1) (nextRows state) (site 3) (site 4) (fun anchor ↦
    AtMarkedCall (OracleProtocol.tableQuery model (.field extension) none anchor (low state) 1 1 context.roles
      (site 5)) (fun read ↦ ∀ folded : model.Field extension, OracleProtocol.AfterMarks (.done (advanced state folded))
        (read (.cons (concrete model (.field extension) folded) .nil)))) process

/-- If the selected handle reports the expected row count, it supplies the
next cell. A mismatch at that cell stops before selecting a virtual handle. -/
def checksLayer (context : ProtocolContext) (step : Nat) (state : State model)
    (layers folds : List OracleAnchor) (process : Process model) : Prop :=
  selectsRows context layers (wrappingAdd step 1) state.rows (site 0) (site 1) (fun anchor ↦
    AtMarkedCall (OracleProtocol.tableQuery model (.field extension) none anchor state.position 1 1 context.roles
      (site 2)) (fun read ↦
        (∀ value : model.Field extension, value ≠ state.expected →
          StopsAfterMarks .reject (read (.cons (concrete model (.field extension) value) .nil))) ∧
        checksFold context step state folds (read (.cons (concrete model (.field extension) state.expected) .nil)))) process

open Lean.Parser.Tactic.Conv in
/-- Open just the next retained operation under a marked-prefix or stop
predicate. The unexamined suffix stays in its original environment. -/
local macro "at_round_action " slot:enterArg " => " action:convSeq : tactic => `(tactic|
  (simp only [PIR.Process.bind]
   conv =>
     enter [$slot]
     rw [Region.denote.eq_def]
     dsimp only
     enter [1]
     ($action:convSeq)))

open Lean.Parser.Tactic.Conv in
local macro "at_round_scalar " slot:enterArg " using " model:term ", " op:term ", " args:term
    " => " rest:convSeq : tactic => `(tactic|
  at_round_action $slot =>
    change ProtocolCalculation.strict $model (OracleProtocol.demand $model) 1 (FriIndexCollections.helpers $model)
      $op (ProtocolValue.embedComponents $args) rfl
    erw [ProtocolCalculation.strict_embed $model (OracleProtocol.demand $model) 1 (FriIndexCollections.helpers $model)
      $op $args rfl]
    ($rest:convSeq))

open Lean.Parser.Tactic.Conv in
local macro "at_round_guard " slot:enterArg " using " model:term ", " ctx:term ", " receiver:term ", " flag:term :
    tactic => `(tactic|
  at_round_action $slot =>
    change ((Participant.guard (services := services) (Value := ($model).Value) 1
      (ProtocolContext.roles $ctx 1) ((concrete $model .boolean $flag).bind ProtocolValue.toConcrete)).interpret
        (OracleProtocol.actions $model)).bind _
    rw [($receiver)]
    simp [OracleProtocol.concrete, Participant.guard, PIR.Process.interpret, PIR.Process.bind])

/-- An actual inner iteration compares the published cell with the carried
value before reading its virtual fold and returning the next four state fields. -/
theorem installed (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (step : Nat) (state : State model) (layers folds : List OracleAnchor) :
    checksLayer context step state layers folds (iteration context step state layers folds) := by
  unfold checksLayer selectsRows iteration
  repeat' with_unfolding_all apply AtMarkedCall.mark
  at_round_scalar 3 using model, .indexWrappingAdd, (.cons (some step) (.cons (some 1) .nil)) =>
    skip
  with_unfolding_all apply AtMarkedCall.mark
  with_unfolding_all apply AtMarkedCall.found
  intro anchor
  repeat' with_unfolding_all apply AtMarkedCall.mark
  with_unfolding_all apply AtMarkedCall.found
  repeat' with_unfolding_all apply AtMarkedCall.mark
  at_round_scalar 3 using model, .indexEqual, (.cons (some state.rows) (.cons (some state.rows) .nil)) =>
    change PIR.Process.done (I := OracleProtocol.Interface model)
      (.cons (concrete model .boolean (decide (state.rows = state.rows))) .nil)
    simp only [decide_true]
  with_unfolding_all apply AtMarkedCall.mark
  at_round_guard 3 using model, context, receiver, true
  with_unfolding_all apply AtMarkedCall.mark
  with_unfolding_all apply AtMarkedCall.found
  constructor
  · intro value mismatch
    repeat' with_unfolding_all apply StopsAfterMarks.mark
    at_round_scalar 2 using model, (.fieldEqual extension), (.cons (some value) (.cons (some state.expected) .nil)) =>
      change PIR.Process.done (I := OracleProtocol.Interface model)
        (.cons (concrete model .boolean (decide (value = state.expected))) .nil)
      simp only [mismatch, decide_false]
    with_unfolding_all apply StopsAfterMarks.mark
    at_round_guard 2 using model, context, receiver, false
    with_unfolding_all apply StopsAfterMarks.now
  · unfold checksFold selectsRows
    repeat' with_unfolding_all apply AtMarkedCall.mark
    at_round_scalar 3 using model, (.fieldEqual extension), (.cons (some state.expected) (.cons (some state.expected) .nil)) =>
      change PIR.Process.done (I := OracleProtocol.Interface model)
        (.cons (concrete model .boolean (decide (state.expected = state.expected))) .nil)
      simp only [decide_true]
    with_unfolding_all apply AtMarkedCall.mark
    at_round_guard 3 using model, context, receiver, true
    with_unfolding_all apply AtMarkedCall.mark
    at_round_action 3 =>
      change invoke (unit.oracleCalculations model 1) helper14Helper
        (.cons (concrete model .index state.position) (.cons (concrete model .index state.rows) .nil))
      erw [FriPairIndex.verifier model state.position state.rows]
    with_unfolding_all apply AtMarkedCall.mark
    with_unfolding_all apply AtMarkedCall.found
    intro view
    with_unfolding_all apply AtMarkedCall.mark
    with_unfolding_all apply AtMarkedCall.found
    repeat' with_unfolding_all apply AtMarkedCall.mark
    at_round_scalar 3 using model, .indexLogicalShiftRight, (.cons (some state.rows) (.cons (some 1) .nil)) =>
      skip
    with_unfolding_all apply AtMarkedCall.mark
    at_round_scalar 3 using model, .indexEqual, (.cons (some (nextRows state)) (.cons (some (nextRows state)) .nil)) =>
      change PIR.Process.done (I := OracleProtocol.Interface model)
        (.cons (concrete model .boolean (decide (nextRows state = nextRows state))) .nil)
      simp only [decide_true]
    with_unfolding_all apply AtMarkedCall.mark
    at_round_guard 3 using model, context, receiver, true
    with_unfolding_all apply AtMarkedCall.mark
    with_unfolding_all apply AtMarkedCall.found
    intro folded
    repeat' with_unfolding_all apply OracleProtocol.AfterMarks.mark
    at_round_scalar 2 using model, .indexLogicalShiftRight, (.cons (some state.rows) (.cons (some 1) .nil)) =>
      skip
    with_unfolding_all apply OracleProtocol.AfterMarks.mark
    at_round_scalar 2 using model, (.fieldMultiply extension), (.cons (some state.shift) (.cons (some state.shift) .nil)) =>
      skip
    with_unfolding_all apply OracleProtocol.AfterMarks.here

end ZkcExamples.Structured.FriCheckRound
