module

public import Zkc.IR.Source.Structured.OracleEffects

@[expose] public section

/-! Pure structural observations of deferred data. These functions do not run an oracle,
materialize data, supply missing values or select a mathematical operation's meaning. -/

set_option autoImplicit false
namespace Zkc.Source.Structured

def OracleDataView.count {sort : OracleLogicalSort} (view : OracleDataView sort) : Nat :=
  match sort, view with
  | .singleton (.table _ _), view => view.references.shape.get .here
  | .sequence _ _, view => view.references.length

/-- Selecting an element of the paired data sequence retains that element's complete
reference. It does not demand any element's contents, including ignored elements. -/
def OracleDataView.select {kind : OracleKind} {maximum : Nat}
    (view : OracleDataView (.sequence kind maximum)) (index : Nat) :
    Option (OracleDataView (.singleton kind)) :=
  view.references[index]?.map (fun reference ↦ ⟨view.holder, view.receivers, reference⟩)

namespace ProtocolValue

/-- A shape observation only. The surrounding source adapter must still check that the
source operation accepts a collection type; scalar inputs return `none`. -/
def observedLength {carriers : Carriers} : {type : Ty} → ProtocolValue carriers type → Option Nat
  | _, .deferred view => some view.count
  | _, .sequence _ values => some values.toList.length
  | .vector _, .concrete _ values => some values.length
  | .groups _, .concrete _ values => some values.length
  | .indices, .concrete _ values => some values.length
  | .oracleSequence _ _, .concrete _ values => some values.length
  | _, _ => none

/-- This API selects from a paired sequence with its exact capacity. A singleton table's
concrete rows are deliberately not interpreted as another paired sequence. -/
def selectData {carriers : Carriers} (kind : OracleKind) (maximum : Nat) {type : Ty}
    (value : ProtocolValue carriers type) (index : Nat) :
    Option (ProtocolValue carriers kind.data) :=
  match value with
  | .sequence element values =>
    if same : element = kind.data then (same ▸ values).toList[index]? else none
  | @ProtocolValue.deferred _ sort view =>
    if same : sort = .sequence kind maximum then
      ((same ▸ view).select index).map ProtocolValue.deferred
    else none
  | _ => none

@[simp] theorem observedLength_deferred {carriers : Carriers} {sort : OracleLogicalSort}
    (view : OracleDataView sort) :
    observedLength (carriers := carriers) (.deferred view) = some view.count := rfl

@[simp] theorem selectData_deferred {carriers : Carriers} (kind : OracleKind) (maximum : Nat)
    (view : OracleDataView (.sequence kind maximum)) (index : Nat) :
    selectData (carriers := carriers) kind maximum (.deferred view) index =
      (view.select index).map ProtocolValue.deferred := by
  simp [selectData]

/-- Pure selection followed by demand visits only the selected singleton view. The handler
still owns holder/shape/domain checks and may refuse unsupported concrete virtual demand. -/
theorem materialize_selected {carriers : Carriers} {I : PIR.Signature}
    (demand : OracleDataDemandInterpretation carriers I) (self : Nat)
    (kind : OracleKind) (maximum : Nat) (view : OracleDataView (.sequence kind maximum))
    (index : Nat) (selected : OracleDataView (.singleton kind))
    (found : view.select index = some selected) :
    selectData (carriers := carriers) kind maximum (.deferred view) index =
      some (.deferred selected) ∧
    materializeWith demand self (.deferred selected) = demand ⟨self, .singleton kind, selected⟩ := by
  exact ⟨by rw [selectData_deferred, found]; rfl, materializeWith_deferred demand self selected⟩

end ProtocolValue
end Zkc.Source.Structured
