module

public import Zkc.Source.Structured.OracleValues
public import Zkc.Source.Structured.TypeProperties

@[expose] public section

/-! A typed representation relation for closure captures. Ordinary data retains
its complete value; logical handles become nominal constructor/slot records.
The relation supplied by immutable storage determines which anchor a physical
reference denotes. Neither equal types nor equal word contents determine it.
-/

set_option autoImplicit false
namespace Zkc.Realization.CaptureLayout
open Zkc.Source Zkc.Source.Structured

abbrev referenceFields : ProductFields := .cons .index (.cons .index .nil)
def referenceType (identity : String) : Ty := .product identity "Record" referenceFields

/-- This profile matches the native virtual closure: direct oracle sources and
handle-free parameters. Nested logical aggregates require their own representation. -/
inductive Layout : List Ty → List Ty → Type where
  | nil : Layout [] []
  | data {type : Ty} {source target : List Ty} (ordinary : type.isHandle = false)
      (rest : Layout source target) : Layout (type :: source) (type :: target)
  | handle {source target : List Ty} (kind : OracleKind) (identity : String)
      (rest : Layout source target) :
      Layout (.oracle kind :: source) (referenceType identity :: target)

/-- Obtain the layout from the checked declaration and the actual record fields.
There is no caller-selected permutation or flattening of the capture telescope. -/
def recognize : (source target : List Ty) → Option (Layout source target)
  | [], [] => some .nil
  | .oracle kind :: source, .product identity "Record"
      (.cons .index (.cons .index .nil)) :: target =>
    (recognize source target).map (.handle kind identity)
  | type :: source, physical :: target => do
    if ordinary : type.isHandle = false then
      if same : physical = type then
        let rest ← recognize source target
        return same.symm ▸ Layout.data ordinary rest
      else none
    else none
  | _, _ => none

/-- This is a view of actual immutable storage, not a second handle allocator. -/
abbrev References := (kind : OracleKind) → (identity : String) →
  OracleAnchor → (Nat × Nat) → Prop

def Unambiguous (references : References) : Prop :=
  ∀ kind identity first second physical,
    references kind identity first physical → references kind identity second physical → first = second

/-- Same-typed captures retain their source order. An oracle capture is justified
by its stored association, while an ordinary parameter must be exactly equal. -/
def Related {carriers : Carriers} (references : References) :
    {source target : List Ty} → Layout source target →
      Values carriers.Value source → Values carriers.Value target → Prop
  | _, _, .nil, .nil, .nil => True
  | _, _, .data _ rest, .cons value values, .cons physical physicals =>
      value = physical ∧ Related references rest values physicals
  | _, _, .handle kind identity rest, .cons anchor values, .cons physical physicals =>
      references kind identity anchor (physical.1, physical.2.1) ∧
        Related references rest values physicals

/-- The physical slot and its type follow the original capture slot.
Parameter readers and child-handle readers use this same ordered map. -/
def Layout.physicalType : {source target : List Ty} → {type : Ty} →
    Layout source target → Var source type → Ty
  | _, _, type, .data _ _, .here => type
  | _, _, _, .handle _ identity _, .here => referenceType identity
  | _, _, _, .data _ rest, .there slot => rest.physicalType slot
  | _, _, _, .handle _ _ rest, .there slot => rest.physicalType slot

def Layout.physicalVar : {source target : List Ty} → {type : Ty} →
    (layout : Layout source target) → (slot : Var source type) →
      Var target (layout.physicalType slot)
  | _, _, _, .data _ _, .here => .here
  | _, _, _, .handle _ _ _, .here => .here
  | _, _, _, .data _ rest, .there slot => .there (rest.physicalVar slot)
  | _, _, _, .handle _ _ rest, .there slot => .there (rest.physicalVar slot)

theorem Layout.physicalVar_index {source target : List Ty} {type : Ty}
    (layout : Layout source target) (slot : Var source type) :
    (layout.physicalVar slot).index = slot.index := by
  induction layout with
  | nil => cases slot
  | data ordinary rest ih => cases slot with
    | here => rfl
    | there slot => exact congrArg Nat.succ (ih slot)
  | handle kind identity rest ih => cases slot with
    | here => rfl
    | there slot => exact congrArg Nat.succ (ih slot)

def Layout.Cell {carriers : Carriers} (references : References) :
    {source target : List Ty} → {type : Ty} → (layout : Layout source target) →
      (slot : Var source type) → carriers.Value type →
      carriers.Value (layout.physicalType slot) → Prop
  | _, _, _, .data _ _, .here, value, physical => value = physical
  | _, _, _, .handle kind identity _, .here, anchor, physical =>
      references kind identity anchor (physical.1, physical.2.1)
  | _, _, _, .data _ rest, .there slot, value, physical =>
      rest.Cell references slot value physical
  | _, _, _, .handle _ _ rest, .there slot, value, physical =>
      rest.Cell references slot value physical

/-- Reading an original capture selects the matching typed physical slot. -/
theorem Related.get {carriers : Carriers} {references : References}
    {source target : List Ty} {layout : Layout source target}
    {values : Values carriers.Value source} {physical : Values carriers.Value target}
    (related : Related references layout values physical) {type : Ty} (slot : Var source type) :
    layout.Cell references slot (values.get slot) (physical.get (layout.physicalVar slot)) := by
  induction layout with
  | nil => cases slot
  | data ordinary rest ih =>
      cases values with | cons value values =>
        cases physical with | cons physical physicals =>
          cases slot with
          | here => exact related.1
          | there slot => exact ih related.2 slot
  | handle kind identity rest ih =>
      cases values with | cons anchor values =>
        cases physical with | cons physical physicals =>
          cases slot with
          | here => exact related.1
          | there slot => exact ih related.2 slot

/-- Extending stores preserves captures whenever it preserves each reference.
No protocol-specific frame lemma is required for the remaining data fields. -/
theorem Related.transport {carriers : Carriers} {before after : References}
    (kept : ∀ kind identity anchor physical,
      before kind identity anchor physical → after kind identity anchor physical)
    {source target : List Ty} {layout : Layout source target}
    {values : Values carriers.Value source} {physical : Values carriers.Value target}
    (related : Related before layout values physical) : Related after layout values physical := by
  induction layout with
  | nil => cases values; cases physical; trivial
  | data ordinary rest ih =>
      cases values with | cons value values =>
        cases physical with | cons physical physicals =>
          exact ⟨related.1, ih related.2⟩
  | handle kind identity rest ih =>
      cases values with | cons anchor values =>
        cases physical with | cons physical physicals =>
          exact ⟨kept kind identity anchor _ related.1, ih related.2⟩

/-- A fixed physical record has only one logical capture tuple. In particular,
swapping distinct same-typed parent handles cannot retain this association. -/
theorem Related.source_unique {carriers : Carriers} {references : References}
    (unique : Unambiguous references) {source target : List Ty}
    {layout : Layout source target} {first second : Values carriers.Value source}
    {physical : Values carriers.Value target}
    (left : Related references layout first physical)
    (right : Related references layout second physical) : first = second := by
  induction layout with
  | nil => cases first; cases second; rfl
  | data ordinary rest ih =>
      cases first with | cons first firsts =>
        cases second with | cons second seconds =>
          cases physical with | cons physical physicals =>
            have head := left.1.trans right.1.symm
            have tail := ih left.2 right.2
            cases head; cases tail; rfl
  | handle kind identity rest ih =>
      cases first with | cons first firsts =>
        cases second with | cons second seconds =>
          cases physical with | cons physical physicals =>
            have head := unique kind identity first second _ left.1 right.1
            have tail := ih left.2 right.2
            cases head; cases tail; rfl

end Zkc.Realization.CaptureLayout
