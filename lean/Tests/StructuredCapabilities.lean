import Zkc.Source.Structured.NormalForm.Observation
import ZkcTools.ConstructionBindings.Readback
import Zkc.Source.KernelRfl

/-! Capabilities are nominal ABI inputs, never encoded payloads or arbitrary
field literals. These controls quantify the actual service handle. -/
set_option autoImplicit false
namespace Tests.StructuredCapabilities
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction

def pattern (field : String) (handle : Nat) : InputPattern [.service ("random." ++ field ++ "/0")] :=
  .cons (.capability ("random." ++ field ++ "/0") handle) .nil

def body (field : String) : Region protocolDialect [.service ("random." ++ field ++ "/0")] [.field field] :=
  .letOp (.draw 0 field "draw") (.cons .here .nil) .nil (.ret (.cons .here .nil))

def form (field : String) (handle : Nat) : Form [] [] [] [.field field] :=
  .query "draw" field (.cons (.capability ("random." ++ field ++ "/0") handle) .nil)
    (.done (.cons (.present (.var .here)) .nil))

example (field : String) (handle : Nat) :
    normalize {} (body field) 0 1 (pattern field handle) = .ok (form field handle) := by kernel_rfl

theorem source_exact (model : DomainModel) (field : String) (handle : Nat)
    (tables : Tables model (Occurrence.signature model.toCarriers)) :
    (body field).denote (participantMeaningWithOn model (.silent _) Occurrence.actions tables 0 [] {} Occurrence.iterations)
      (pattern field handle |>.environment model .nil).get =
    (form field handle).denoteOn model Occurrence.actions tables (LawResults.empty model) {}
      (runsAtOn model Occurrence.actions Occurrence.iterations tables [] {} 0)
      (noCallees model (Occurrence.signature model.toCarriers)) .nil :=
  normalize_occurrence_sound {} (body field) 0 1 (pattern field handle) (form field handle)
    (by kernel_rfl) (by kernel_rfl) (RosterDistinct.root 0 1) (LawResults.empty model)
    (noCallees model (Occurrence.signature model.toCarriers)) .nil (LawsHold.empty _ _) (noCallees_hold _ _)

-- The full ABI readback uses the same handle and no physical cell.
def capabilityReadback (service : String) (handle : Nat) :
    ConnectionFrame.Readback ([] : ConnectionFrame.Layout [])
      (.cons (.present (.capability service handle)) .nil) [.capability handle] := by
  derive_source_readback

example (model : DomainModel) (service : String) (actual selected : Nat) (different : actual ≠ selected) :
    ¬ Original.ValuesHolds (carriers := model.toCarriers) [] [.capability selected]
      (.cons (ty := .service service) (some actual) .nil) := by
  intro related
  exact different (Option.some.inj related.1)

-- Service handles are not eligible for arbitrary mathematical literal laws.
example (service : String) (handle : Nat) :
    (Term.capability (laws := []) (Δ := []) service handle).literal? = none := rfl
example (model : DomainModel) (service : String) (handle : Nat) :
    Domain.Value.encode (carriers := model.toCarriers) (.service service) (handle : model.Value (.service service)) = none := rfl

-- A repeated component receives the exact pinned handle, or proposal refuses.
example (service : String) :
    calleeArguments (.cons (.capability service 73) .nil)
      (.cons (Comp.present (laws := []) (Δ := []) (.capability service 73)) .nil) = some .nil := by kernel_rfl
example (service : String) :
    calleeArguments (.cons (.capability service 73) .nil)
      (.cons (Comp.present (laws := []) (Δ := []) (.capability service 91)) .nil) = none := by kernel_rfl

end Tests.StructuredCapabilities
