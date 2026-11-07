module

public import ZkcExamples.Structured.FriCheckRound
public meta import ZkcExamples.Structured.FriCheckPositions
public meta import ZkcExamples.Structured.FriCheckRound
public meta import ZkcExamples.Structured.FriSourceBodies
public meta import ZkcTools.StructuredSource.Bindings.CheckedCallback
public import Zkc.Source.Structured.MarkedReturn
public import Zkc.Source.Structured.ReferenceLibrary

@[expose] public section

/-! The first word read and virtual fold inside Check's actual query. The
retained prefix computes the next repeat's operands, the remembered vector,
and the coefficient operand of its suffix. -/
set_option autoImplicit false
namespace ZkcExamples.Structured.FriPeeledQuery
open Zkc.Source Zkc.Source.Structured
open FriSource FriSourceBodies FriSourceViews FriCheckPositions FriCheckRound
open OracleProtocol (concrete AtMarkedCall AtMarkedReturn)
attribute [local implicit_reducible] ProtocolOp.arguments ProtocolOp.results ProtocolOp.regions
variable {model : DomainModel}

checked_repeat_prefix firstFoldBody := insideQuery using innerOnSpine

def sites := firstFoldBody.erase.operations.filterMap fun op ↦ match op with
  | .oracle _ location => some location
  | _ => none

def site (i : Fin 4) : OracleLocation :=
  sites[i.val]'(by
    have size : sites.length = 4 := by kernel_rfl
    simpa only [size] using i.isLt)

def captures (model : DomainModel) (layers folds : List OracleAnchor) (values : List (model.Field extension))
    (shift : model.Field extension) (rows : Nat) (cs : FriBinding.Value model (.vector extension))
    (count : Nat) : Captures model :=
  ⟨concrete model (.vector extension) values, concrete model FriBinding.layersSort.type layers,
    concrete model FriBinding.layersSort.type folds, concrete model (.field extension) shift,
    concrete model .index rows, cs, concrete model .boolean false, concrete model (.vector extension) [],
    concrete model .index count⟩

def reached (layers folds : List OracleAnchor) (values : List (model.Field extension))
    (selected : model.Field extension) (cs : FriBinding.Value model (.vector extension)) (count : Nat)
    (carried : FriCheckRound.State model) (folded : model.Field extension)
    (live : Values (FriBinding.Value model) roundSite.context) : Prop :=
  Operands.eval live.get roundSite.operands = .cons (concrete model .index count)
    ((advanced carried folded).append (FriCheckRound.captures model layers folds)) ∧
  live.get coefficientsPort = cs ∧ live.get rememberedPort = concrete model (.vector extension) (values ++ [selected])

private theorem append (values : List (model.Field extension)) (value : model.Field extension) :
    OracleProtocol.owned model 1 1 (FriIndexCollections.helpers model) helper32Helper
      (.cons (concrete model (.vector extension) values) (.cons (concrete model (.field extension) value) .nil)) =
      .done (.cons (concrete model (.vector extension) (values ++ [value])) .nil) := by
  change OracleProtocol.owned model 1 1 (FriIndexCollections.helpers model) helper32Helper
    (ProtocolValue.embedComponents (Values.cons (Value := model.Value) (ty := .vector extension) values
      (.cons value .nil)).present) = _
  rw [OracleProtocol.owned_present, (ReferenceLibrary.appendVector model extension "s0").invokeOn
    (helper := helper32Helper) unit.definitions unit.linked (by exact_body helper32Definition)
    (.cons values (.cons value .nil)) trivial]
  rfl

theorem sizeProjection (shift : model.Field extension) (rows : Nat) :
    invoke (unit.oracleCalculations model 1) helper28Helper
      (.cons (concrete model (.field extension) shift) (.cons (concrete model .index rows) .nil)) =
      .done (.cons (concrete model .index rows) .nil) := by
  exact (ReferenceLibrary.returnOperands model (.cons (.there .here) .nil)).invokeOracleConcrete
    (helper := helper28Helper) unit 1 rfl FriPairIndex.mathFragment unit.linked
    (by exact_body helper28Definition) (.cons shift (.cons rows .nil)) trivial

private theorem shiftProjection (shift : model.Field extension) (rows : Nat) :
    invoke (unit.oracleCalculations model 1) helper33Helper
      (.cons (concrete model (.field extension) shift) (.cons (concrete model .index rows) .nil)) =
      .done (.cons (concrete model (.field extension) shift) .nil) := by
  exact (ReferenceLibrary.returnOperands model (.cons .here .nil)).invokeOracleConcrete
    (helper := helper33Helper) unit 1 rfl FriPairIndex.mathFragment unit.linked
    (by exact_body helper33Definition) (.cons shift (.cons rows .nil)) trivial

/-- The initial word and sampled position determine the first cell. Every
concrete response continues to the virtual handle selected at zero, and its
reply sets the inner round's expected value. The cuts retain the actual marks
and only describe the branch on which the metadata reports the right size. -/
theorem installed (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (xs : List Nat) (admitted : FriBoundedPositions.Admitted xs) (ordinal : Fin xs.length)
    (source : OracleAnchor) (layers folds : List OracleAnchor) (values : List (model.Field extension))
    (shift : model.Field extension) (rows : Nat) (cs : FriBinding.Value model (.vector extension)) (count : Nat) :
    let position := xs[ordinal.val]
    let cap := captures model layers folds values shift rows cs count
    AtMarkedCall (initialRequest context source position) (fun read ↦ ∀ selected : model.Field extension,
      let carried : FriCheckRound.State model := ⟨selected, position, rows, shift⟩
      selectsRows context folds 0 (nextRows carried) (site 1) (site 2) (fun view ↦
        AtMarkedCall (OracleProtocol.tableQuery model (.field extension) none view (low carried) 1 1 context.roles
          (site 3)) (fun query ↦ ∀ folded : model.Field extension,
          AtMarkedReturn (reached layers folds values selected cs count carried folded)
            (query (.cons (concrete model (.field extension) folded) .nil))))
        (read (.cons (concrete model (.field extension) selected) .nil)))
      (firstFoldBody.denote ((verifierAlgebra model).meaning (verifierTable model) context 1)
        (arguments cap xs ordinal.val source).get) := by
  dsimp only
  with_unfolding_all apply AtMarkedCall.mark
  at_fri_action 3 =>
    change OracleProtocol.owned model 1 (context.roles 1) (FriIndexCollections.helpers model) helper30Helper
      (.cons (concrete model .indices xs) (.cons (concrete model .index ordinal.val) .nil))
    rw [receiver, lookup xs admitted ordinal]
  with_unfolding_all apply AtMarkedCall.mark
  with_unfolding_all apply AtMarkedCall.found
  intro selected
  unfold selectsRows
  with_unfolding_all apply AtMarkedCall.mark
  at_fri_action 3 =>
    change OracleProtocol.owned model 1 (context.roles 1) (FriIndexCollections.helpers model) helper31Helper
      (.cons (concrete model .boolean false) (.cons (concrete model (.vector extension) [])
        (.cons (concrete model .index ordinal.val) (.cons (concrete model (.field extension) selected) .nil))))
    rw [receiver, FriValueAssociation.installed false [] ordinal.val selected (by simp)]
  with_unfolding_all apply AtMarkedCall.mark
  at_fri_guard 3 using model, context, receiver, true
  with_unfolding_all apply AtMarkedCall.mark
  at_fri_action 3 =>
    change OracleProtocol.owned model 1 (context.roles 1) (FriIndexCollections.helpers model) helper32Helper
      (.cons (concrete model (.vector extension) values) (.cons (concrete model (.field extension) selected) .nil))
    rw [receiver, append values selected]
  with_unfolding_all apply AtMarkedCall.mark
  at_fri_action 3 =>
    change invoke (unit.oracleCalculations model 1) helper28Helper
      (.cons (concrete model (.field extension) shift) (.cons (concrete model .index rows) .nil))
    rw [sizeProjection]
  with_unfolding_all apply AtMarkedCall.mark
  at_fri_action 3 =>
    change PIR.Process.done (I := OracleProtocol.Interface model) (Values.cons (Value := FriBinding.Value model)
      (Participant.restrict (([1].map context.roles).contains 1) (concrete model .index rows)) .nil)
    simp [receiver, Participant.restrict]
  with_unfolding_all apply AtMarkedCall.mark
  at_fri_action 3 =>
    change invoke (unit.oracleCalculations model 1) helper33Helper
      (.cons (concrete model (.field extension) shift) (.cons (concrete model .index rows) .nil))
    rw [shiftProjection]
  with_unfolding_all apply AtMarkedCall.mark
  at_fri_action 3 =>
    change PIR.Process.done (I := OracleProtocol.Interface model) (Values.cons (Value := FriBinding.Value model)
      (Participant.restrict (([1].map context.roles).contains 1) (concrete model (.field extension) shift)) .nil)
    simp [receiver, Participant.restrict]
  with_unfolding_all apply AtMarkedCall.mark
  at_fri_action 3 =>
    change invoke (unit.oracleCalculations model 1) helper14Helper
      (.cons (concrete model .index xs[ordinal.val]) (.cons (concrete model .index rows) .nil))
    rw [FriPairIndex.verifier]
  repeat' with_unfolding_all apply AtMarkedCall.mark
  with_unfolding_all apply AtMarkedCall.found
  intro view
  with_unfolding_all apply AtMarkedCall.mark
  with_unfolding_all apply AtMarkedCall.found
  repeat' with_unfolding_all apply AtMarkedCall.mark
  at_fri_scalar 3 using model, .indexLogicalShiftRight, (.cons (some rows) (.cons (some 1) .nil)) =>
    skip
  with_unfolding_all apply AtMarkedCall.mark
  at_fri_scalar 3 using model, .indexEqual, (.cons (some (logicalShiftRight rows 1)) (.cons (some (logicalShiftRight rows 1)) .nil)) =>
    change PIR.Process.done (I := OracleProtocol.Interface model)
      (.cons (concrete model .boolean (decide (logicalShiftRight rows 1 = logicalShiftRight rows 1))) .nil)
    simp only [decide_true]
  with_unfolding_all apply AtMarkedCall.mark
  at_fri_guard 3 using model, context, receiver, true
  with_unfolding_all apply AtMarkedCall.mark
  with_unfolding_all apply AtMarkedCall.found
  intro folded
  repeat' with_unfolding_all apply AtMarkedReturn.mark
  at_fri_scalar 2 using model, .indexLogicalShiftRight, (.cons (some rows) (.cons (some 1) .nil)) =>
    skip
  with_unfolding_all apply AtMarkedReturn.mark
  at_fri_scalar 2 using model, (.fieldMultiply extension), (.cons (some shift) (.cons (some shift) .nil)) =>
    skip
  repeat' with_unfolding_all apply AtMarkedReturn.mark
  with_unfolding_all apply AtMarkedReturn.done
  exact ⟨rfl, rfl, rfl⟩

end ZkcExamples.Structured.FriPeeledQuery
